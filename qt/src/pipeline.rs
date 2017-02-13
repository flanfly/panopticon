use std::collections::{HashMap,HashSet};
use std::sync::Arc;
use std::sync::atomic::{Ordering,AtomicUsize};
use std::fmt::Debug;
use std::iter::FromIterator;
use std::borrow::Cow;
use std::ops::Range;

use parking_lot::RwLock;
use uuid::Uuid;
use rayon::prelude::*;
use graph_algos::{
    GraphTrait,
    VertexListGraphTrait,
    MutableGraphTrait,
    BidirectionalGraphTrait,
    AdjacencyMatrixGraphTrait,
};

use panopticon::{
    BasicBlock,
    Mnemonic,
    Function,
    FunctionRef,
    Region,
    Lvalue,
    Rvalue,
    amd64,
    Program,
    Result,
    ControlFlowTarget,
    Statement,
    ssa_convertion,
    variable_access,
    Avalue,
    approximate,
    CallTarget,
    CallGraphRef,
    BoundedAddrTrack,
    Architecture,
};

struct QueryResult<Q: Query> {
    answer: Q::Answer,
    subqueries: Vec<(CallTarget,Q)>,
}

trait Query: Send + Sync + Sized + PartialEq + Clone + Debug {
    type Answer: Send + Sync + Sized + PartialEq + Debug;
    fn execute(&self, &Function, &Region, &HashMap<Range<u64>,Cow<'static,str>>,
               &HashMap<CallTarget,Vec<(Self,Self::Answer)>>) -> Result<QueryResult<Self>>;
    fn simulate(&self, &Cow<'static,str>) -> Result<QueryResult<Self>>;
}

#[derive(Debug,Clone,PartialEq,Eq)]
enum QueryState {
    Done,
    Blocked,
    Ready,
}

#[derive(Clone)]
struct QueryWrapper<Q: Query> {
    id: usize,
    parent: usize,
    target: CallTarget,
    query: Q,
    state: QueryState,
}

fn run_query<Q: Query>(entries: &Vec<CallTarget>, query: Q, program: &Program, region: &Region,
                       symbols: &HashMap<Range<u64>,Cow<'static,str>>) -> Result<HashMap<CallTarget,Vec<(Q,Q::Answer)>>> {
    use std::iter::FromIterator;

    let answers = RwLock::new(HashMap::<CallTarget,Vec<(Q,Q::Answer)>>::new());
    let mut queries = vec![];
    let next_query = AtomicUsize::new(1);

    queries.extend(entries.iter().map(|f| QueryWrapper{
        id: 0,
        parent: 0,
        target: f.clone(),
        query: query.clone(),
        state: QueryState::Ready,
    }));

    while !queries.is_empty() {
        queries = try!(queries.into_par_iter().
            map(|mut q| -> Result<Vec<QueryWrapper<Q>>> {
                let id = q.id;
                let mut new_queries = vec![];

                if let QueryWrapper{ state: ref mut state@QueryState::Ready, target: ref tgt, ref query, id,.. } = q {
                    println!("run {}",id);

                    let query_res = match tgt {
                        &CallTarget::Function(ref func_uuid) => {
                            let function = try!(program.functions.get(&func_uuid)
                                                .ok_or("Got query for unknown function w/"));
                            try!(query.execute(&*function.0.read(),region,symbols,&*answers.read()))
                        }
                        &CallTarget::Stub(ref name) => {
                            try!(query.simulate(name))
                        }
                    };

                    let QueryResult{ answer, mut subqueries } = query_res;
                    let qa_pair = (query.clone(),answer);
                    let fixedpoint = answers.read().get(tgt).and_then(|x| x.iter().find(|x| **x == qa_pair)).is_some();

                    if fixedpoint {
                        debug!("QR: {:?}",qa_pair);
                        debug!("QR: saw this question already, stopping");
                    }

                    if fixedpoint || subqueries.is_empty() {
                        *state = QueryState::Done;
                    } else {
                        *state = QueryState::Blocked;
                    }

                    if !fixedpoint {
                        answers.write().entry(tgt.clone()).or_insert(vec![]).push(qa_pair);
                        new_queries = subqueries.drain(..)
                            .map(|(tgt,q)| QueryWrapper::<Q>{
                                id: next_query.fetch_add(1,Ordering::Relaxed),
                                parent: id,
                                target: tgt,
                                query: q,
                                state: QueryState::Ready,
                            }).collect();
                    }
                } else {
                    println!("skip {}",id);
                }

                new_queries.push(q);
                Ok(new_queries)
            }).reduce(|| Ok(vec![]),|acc_,x_| -> Result<Vec<QueryWrapper<Q>>> {
                let mut acc = try!(acc_);
                let mut x = try!(x_);
                let mut ret: Vec<QueryWrapper<Q>> = Vec::from_iter(acc.drain(..).chain(x.drain(..)));
                let sec = ret.iter().map(|qw| (qw.parent,qw.state.clone())).collect::<Vec<_>>();

                for r in ret.iter_mut() {
                    if let &mut QueryWrapper::<Q>{ state: ref mut state@QueryState::Blocked, id,.. } = r {
                        for q in sec.iter() {
                            let &(q_parent,ref q_state) = q;

                            if q_parent == id && *q_state == QueryState::Done {
                                *state = QueryState::Ready;
                                println!("{} becomes ready",id);
                            }
                        }
                    }
                }
                Ok(ret)
            }));
        queries.retain(|q| q.state != QueryState::Done);
    }

    Ok(answers.into_inner())
}

#[derive(Debug,PartialEq,Clone)]
struct DataflowQuery{}

struct DataflowAnswer {
    function: Option<Function>,
    reads: Vec<Rvalue>,
    writes: Vec<Lvalue>,
}

use std::fmt;
impl fmt::Debug for DataflowAnswer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DataflowAnswer{{ reads: {:?}, writes: {:?} }}",self.reads,self.writes)
    }
}

impl PartialEq for DataflowAnswer {
    fn eq(&self, rhs: &Self) -> bool { true }
}

impl Query for DataflowQuery {
    type Answer = DataflowAnswer;

    fn simulate(&self, sym: &Cow<'static,str>) -> Result<QueryResult<Self>> {
        if sym == "__libc_start_main" {
            Ok(QueryResult::<Self>{
                answer: DataflowAnswer{
                    function: None,
                    reads: vec![
                        Rvalue::Variable{ name: "RSP".into(), size: 64, subscript: Some(0), offset: 0 },
                        Rvalue::Variable{ name: "RDI".into(), size: 64, subscript: Some(0), offset: 0 }, // main
                        Rvalue::Variable{ name: "RSI".into(), size: 64, subscript: Some(0), offset: 0 }, // argc
                        Rvalue::Variable{ name: "RDX".into(), size: 64, subscript: Some(0), offset: 0 }, // argv
                        Rvalue::Variable{ name: "RCX".into(), size: 64, subscript: Some(0), offset: 0 }, // init
                        Rvalue::Variable{ name: "R8".into(), size: 64, subscript: Some(0), offset: 0 }, // fini
                        Rvalue::Variable{ name: "R9".into(), size: 64, subscript: Some(0), offset: 0 }, // rtld_fini
                    ],
                    writes: vec![]
                },
                subqueries: vec![],
            })
        } else {
            warn!("Dataflow: unknown symbol {}", sym);
            Ok(QueryResult::<Self>{
                answer: DataflowAnswer{
                    function: None,
                    reads: vec![],
                    writes: vec![]
                },
                subqueries: vec![],
            })
        }
    }

    fn execute(&self, func: &Function, region: &Region, symbols: &HashMap<Range<u64>,Cow<'static,str>>,
               answers: &HashMap<CallTarget,Vec<(Self,Self::Answer)>>) -> Result<QueryResult<Self>> {
        let mut subqs = vec![];
        let subq = DataflowQuery{};
        let calls = func.collect_resolved_calls();
        let deps = HashMap::<CallTarget,&DataflowAnswer>::from_iter(calls.iter().filter_map(|ct| {
            let answer = answers.get(ct);

            if answer.is_none() {
                subqs.push((ct.clone(),subq.clone()));
            }

            answer.and_then(|x| x.first()).map(|x| (ct.clone(),&x.1))
        }));
        let mut new_func: Function = (*func).clone();

        ssa_convertion(&mut new_func);
        let (reads,writes) = variable_access(&new_func);

        Ok(QueryResult{
            answer: DataflowAnswer{
                function: Some(new_func),
                reads: reads,
                writes: writes
            },
            subqueries: subqs,
        })
    }
}

type AbstractInterpEnv = HashMap<(Cow<'static,str>,usize),BoundedAddrTrack>;

#[derive(Debug,PartialEq,Clone)]
struct AbstractInterpQuery{
    env: AbstractInterpEnv,
}

#[derive(PartialEq,Debug)]
struct AbstractInterpAnswer {
    values: HashMap<Lvalue,BoundedAddrTrack>,
}

impl AbstractInterpQuery {
    fn is_environment_more_exact(a: &AbstractInterpEnv, b: &AbstractInterpEnv) -> bool {
        if a.len() < b.len() { return false; }
        if a.len() > b.len() { return true; }
        for (k,aval1) in a.iter() {
            let aval2 = b.get(k).unwrap_or(&BoundedAddrTrack::Meet).clone();
            if !aval1.more_exact(&aval2) { return false; }
        }
        true
    }
}

impl Query for AbstractInterpQuery {
    type Answer = AbstractInterpAnswer;

    fn simulate(&self, sym: &Cow<'static,str>) -> Result<QueryResult<Self>> {
        debug!("AI of {:?} w/ env:",sym);
        for x in self.env.iter() { debug!("\t{:?}",x); }
        debug!("\tEOL");

        if sym == "__libc_start_main" {
            Ok(QueryResult::<Self>{
                answer: AbstractInterpAnswer{
                    values: HashMap::new(),
                },
                subqueries: vec![],
            })
        } else {
            warn!("AbstractInterp: unknown symbol {}", sym);
            Ok(QueryResult::<Self>{
                answer: AbstractInterpAnswer{
                    values: HashMap::new(),
                },
                subqueries: vec![],
            })
        }
    }

    fn execute(&self, func: &Function, region: &Region, symbols: &HashMap<Range<u64>,Cow<'static,str>>,
               answers: &HashMap<CallTarget,Vec<(Self,Self::Answer)>>) -> Result<QueryResult<Self>> {
        //println!("{}",func.to_dot());
        let values = try!(approximate::<BoundedAddrTrack>(func,Some(region),&symbols,&self.env));
        debug!("AI of {:?} w/ env:",func.name);
        for x in self.env.iter() { debug!("\t{:?}",x); }
        debug!("\tEOL");

        let mut subqs = vec![];

        for vx in func.cflow_graph.vertices() {
            let lb = try!(func.cflow_graph.vertex_label(vx).ok_or("No label"));
            match lb {
                &ControlFlowTarget::BasicBlock(ref bb) => {
                    bb.execute(|stmt| match stmt {
                        &Statement::ResolvedCall{ ref function, ref reads, ref writes } => {
                            let current_env = AbstractInterpEnv::from_iter(reads.iter().filter_map(|x| {
                                if let &Rvalue::Variable{ ref name, ref size,.. } = x {
                                    let lv = Lvalue::from_rvalue(x.clone()).unwrap();
                                    values.get(&lv).map(|y| ((name.clone(),*size),y.clone()))
                                } else {
                                    None
                                }
                            }));
                            // XXX: do a subq if the current (in values) values for reads are more
                            // exact than those of all prev queries
                            let start_subquery = answers.get(function).map(|qa_pairs| {
                                qa_pairs.iter()
                                        .all(|&(ref q,_)| {
                                            let ret = Self::is_environment_more_exact(&current_env,&q.env);
                                            if !ret { debug!("{:?} is eq of more exact then {:?}",q.env,current_env); }
                                            ret })
                            }).unwrap_or(true);

                            debug!("possible AI subquery from {} to {:?} with env:",func.name,function);
                            for x in current_env.iter() { debug!("\t{:?}",x); }

                            if start_subquery {
                                debug!("\tRUN");
                                let subq = AbstractInterpQuery{
                                    env: current_env/*HashMap::from_iter(reads.iter().filter_map(|rv| {
                                        match rv {
                                            &Rvalue::Variable{ ref name, ref size, ref subscript, ref offset } => {
                                                let lv = Lvalue::Variable{ name: name.clone(), size: *size, subscript: *subscript };
                                                let var = (name.clone(),*size);
                                                let aval = values.get(&lv).unwrap_or(&BoundedAddrTrack::initial()).clone();

                                                Some((var,aval))
                                            }
                                            _ => { None }
                                        }
                                    }))*/,
                                };
                                subqs.push((function.clone(),subq));
                            } else {
                                debug!("\tABORT");
                            }
                        }
                        _ => {}
                    });
                }
                _ => {}
            }
        }

        Ok(QueryResult{
            answer: AbstractInterpAnswer{
                values: values,
            },
            subqueries: subqs,
        })
    }
}

enum CallAddress {
    Address(u64),
    Symbol(Cow<'static,str>),
}

pub fn run_disassembler(mut functions: Vec<CallTarget>, program: &mut Program, region: &Region,
                        symbols: &HashMap<Range<u64>,Cow<'static,str>>) -> Result<bool> {
    let mut fixedpoint = false;
    let mut initial_env = HashMap::<(Cow<'static,str>,usize),BoundedAddrTrack>::from_iter(vec![
        //(("RDX".into(),64),BoundedAddrTrack::Offset{ region: Some(("atexit".into(),0)), offset: 0, offset_size: 64 }),
    ].into_iter());

    let entries = functions.clone();
    let registers = HashSet::<&'static str>::from_iter(try!(amd64::Amd64::registers(&amd64::Mode::Long)).iter().map(|x| *x));

    while !fixedpoint {
        // disassemble and find new functions
        let map_reduce_res: Result<(bool,Vec<(CallTarget,CallAddress)>)> = functions.par_iter().map(
            |ct| -> Result<(bool,Vec<(CallTarget,CallAddress)>)> {
                match ct {
                    &CallTarget::Function(ref uuid) => {
                        let fref: FunctionRef = try!(program.functions.get(uuid)
                                                     .ok_or::<Cow<'static,str>>("unknown function".into())).clone();
                        {
                            let mut func = fref.0.write();
                            println!("Try to disassemble more of {}",func.name);
                            disassemble(&mut *func,region)
                        }.map(|(a,b)| {
                            (a,b.into_iter()
                                .map(|x| (CallTarget::Function(fref.0.read().uuid.clone()),x))
                                .collect::<Vec<_>>())})
                    }
                    &CallTarget::Stub(ref name) => {
                        println!("simulate {}",name);
                        Ok((false,vec![]))
                    }
                }
            }
        ).reduce(
            || Ok((false,vec![])),
            |a_,b_| -> Result<(bool,Vec<(CallTarget,CallAddress)>)> {
                let mut a = try!(a_);
                let mut b = try!(b_);

                a.1.append(&mut b.1);
                Ok((a.0 || b.0,a.1))
            }
        );

        let (redo_analysis,calls) = try!(map_reduce_res);
        let mut new_functions = vec![];

        fixedpoint = !redo_analysis;

        // insert new calls into call graph and resolve call statements
        for (from_ct,to_addr) in calls.into_iter() {
            match from_ct {
                CallTarget::Function(ref from_uuid) => {
                    let from_ref = try!(program.functions.get(from_uuid).ok_or::<Cow<'static,str>>("unknown function".into())).clone();
                    match to_addr {
                        CallAddress::Address(ref to_addr) => {
                            let (_,maybe_new_function) = try!(insert_call_address(&from_ref,*to_addr,program));
                            if let Some(new_function) = maybe_new_function {
                                let uuid = new_function.0.read().uuid;
                                println!("new function {} ({})",new_function.0.read().name,uuid);
                                new_functions.push(CallTarget::Function(uuid));
                            }
                        }
                        CallAddress::Symbol(ref to_symbol) => {
                            let (_,new_vx) = try!(insert_call_stub(&from_ref,to_symbol.clone(),program));
                            println!("new function {}",to_symbol);
                            new_functions.push(CallTarget::Stub(to_symbol.clone()));
                        }
                    }
                }
                CallTarget::Stub(ref from_name) => {
                    println!("MISSING: call from {}",from_name);
                }
            }
        }

        fixedpoint &= new_functions.is_empty();
        functions.append(&mut new_functions);

        let mut dflow_fixpnt = false;
        while !dflow_fixpnt {
            let mut new_dflow = try!(run_query(&functions, DataflowQuery{}, program, region, symbols));
            let mut var_access = HashMap::<CallTarget,(Vec<Rvalue>,Vec<Lvalue>)>::new();

            dflow_fixpnt = true;

            // update SSA variable subscripts
            // XXX: parallelize
            for (ct,qa_pairs) in new_dflow.iter_mut() {
                let (_,DataflowAnswer{ function: maybe_function, reads, writes }) = qa_pairs.swap_remove(0);
                var_access.insert(ct.clone(),(reads,writes));
                if let Some(function) = maybe_function {
                    if let Some(&(ref func_ref,_)) = program.functions.get(&function.uuid) {
                        println!("update SSA vars of {}",function.name);
                        *func_ref.write() = function;
                    }
                }
            }

            // update reads/writes sets
            // XXX: parallelize
            for ct in var_access.keys() {
                if let &CallTarget::Function(ref uuid) = ct {
                if let Some((fref,_)) = program.find_function_by_uuid(uuid) {
                    let mut func = &mut *fref.write();
                    let name = func.name.clone();
                    let vxs = { func.cflow_graph.vertices().collect::<Vec<_>>() };

                    debug!("update rd/wr for calls from {:?}",name);

                    for vx in vxs {
                        if let Some(&mut ControlFlowTarget::BasicBlock(ref mut bb)) = func.cflow_graph.vertex_label_mut(vx) {
                            bb.rewrite(|stmt| {
                                match stmt {
                                    &mut Statement::ResolvedCall{ function: ref other_function, ref mut reads, ref mut writes } => {
                                        if let Some(&(ref target_rd,ref target_wr)) = var_access.get(other_function) {
                                            for r in target_rd.iter() {
                                                if let &Rvalue::Variable{ ref name, ref size,.. } = r {
                                                    let new_rv = registers.contains(&**name) && reads.iter().find(|rv| {
                                                        if let &&Rvalue::Variable{ name: ref other_name, size: ref other_size,.. } = rv {
                                                            *other_name == *name && *other_size == *size
                                                        } else {
                                                            false
                                                        }
                                                    }).is_none();

                                                    if new_rv {
                                                        reads.push(r.clone());
                                                        dflow_fixpnt = false;
                                                    }
                                                }
                                            }

                                            for w in target_wr.iter() {
                                                if let &Lvalue::Variable{ ref name, ref size,.. } = w {
                                                    let new_lv = registers.contains(&**name) && writes.iter().find(|lv| {
                                                        if let &&Lvalue::Variable{ name: ref other_name, size: ref other_size,.. } = lv {
                                                            *other_name == *name && *other_size == *size
                                                        } else {
                                                            false
                                                        }
                                                    }).is_none();

                                                    if new_lv {
                                                        writes.push(w.clone());
                                                        dflow_fixpnt = false;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            });
                        }
                    }
                }
            }
        }
        }

        let ai_query = AbstractInterpQuery{
            env: initial_env.clone(),
        };
        let new_ainterp = try!(run_query(&functions, ai_query, program, region, symbols));

        // resolve symbolic jumps/calls
        // XXX: parallelize
        for (ref ct,ref qa_pairs) in new_ainterp {
            match ct {
                &CallTarget::Function(ref uuid) => {
                    let func_ref = try!(program.functions.get(uuid).ok_or::<Cow<'static,str>>("unknown function".into())).clone();
                    let func = &mut *func_ref.0.write();
                    if let Some(&(_,ref a)) = qa_pairs.last() {
                        let vals = &a.values;
                        let vxs = { func.cflow_graph.vertices().collect::<Vec<_>>() };

                        //println!("vals: {:?}",vals);

                        for &vx in vxs.iter() {
                            let new_lb = {
                                let maybe_lb = func.cflow_graph.vertex_label(vx);
                                if let Some(&ControlFlowTarget::Value(Rvalue::Variable{ ref name, ref size, ref subscript, offset: 0 })) = maybe_lb {
                                    println!("{:?}",name);

                                    let aval = vals.get(&Lvalue::Variable{ name: name.clone(), size: *size, subscript: *subscript });
                                    if let Some(&BoundedAddrTrack::Offset{ ref region, ref offset, ref offset_size }) = aval {
                                        println!("{:?}",aval);
                                        if region.is_none() {
                                            debug!("resolved {:?} to {:?}",name,*offset);
                                            fixedpoint = false;
                                            Some(ControlFlowTarget::Value(Rvalue::Constant{ value: *offset, size: *offset_size }))
                                                //fixpoint = true;
                                                //resolved_jumps.insert(*offset);
                                        } else if *offset == 0 {
                                            let maybe_prev_bb = func.cflow_graph.in_edges(vx).next()
                                                .map(|e| func.cflow_graph.source(e))
                                                .and_then(|vx| func.cflow_graph.vertex_label(vx))
                                                .and_then(|lb| if let &ControlFlowTarget::BasicBlock(ref bb) = lb { Some(bb.area.start) } else { None });
                                            if let Some(prev_bb) = maybe_prev_bb {
                                                let bb = BasicBlock::from_vec(vec![
                                                                              try!(Mnemonic::new(prev_bb..prev_bb,"__internal_stub_call".to_string(),"".to_string(),vec![].iter(),vec![
                                                                                                 Statement::ResolvedCall{
                                                                                                     function: CallTarget::Stub(region.clone().unwrap().0.into()),
                                                                                                     reads: vec![],
                                                                                                     writes: vec![],
                                                                                                 }].iter()))]);
                                                debug!("resolved {:?} to symbolic value {:?}",name,region);
                                                let _ = try!(insert_call_stub(&func_ref,region.clone().unwrap().0,program));
                                                functions.push(CallTarget::Stub(region.clone().unwrap().0));
                                                fixedpoint = false;
                                                Some(ControlFlowTarget::BasicBlock(bb))
                                            } else {
                                                warn!("No previous basic block");
                                                None
                                            }
                                        } else {
                                            warn!("Can't be resolved");
                                            None
                                        }
                                    } else {
                                        warn!("No abstract value known for {}",name);
                                        None
                                    }
                                } else {
                                    None
                                }
                            };

                            if let (Some(mut have),Some(mut new)) = (func.cflow_graph.vertex_label_mut(vx),new_lb) {
                                *have = new
                            }
                        }
                    }
                }
                &CallTarget::Stub(ref name) if *name == "__libc_start_main" => {
                    if let Some(&(ref func_ref,ref a)) = qa_pairs.last() {
                        let vals = &a.values;
                        let maybe_main = vals.get(&Lvalue::Variable{ name: "RDI".into(), size: 64, subscript: None });
                        if let Some(&BoundedAddrTrack::Offset{ region: None, ref offset, ref offset_size }) = maybe_main {
                            debug!("resolved main to {:?}",offset);
                            let has_main = prog.fin
                            let mut to_func = Function::new(format!("func_{:x}",to_address),from_func.region.clone());
                            let to_uuid = to_func.uuid.clone();
                            let to_ent = to_func.cflow_graph.add_vertex(ControlFlowTarget::Value(Rvalue::Constant{ value: to_address, size: 64 }));
                            let to_vx = prog.call_graph.add_vertex(CallTarget::Function(to_uuid.clone()));

                            to_func.entry_point = Some(to_ent);

                            let to_ref = (Arc::new(RwLock::new(to_func)),to_vx);

                            prog.functions.insert(to_uuid,to_ref.clone());
                            prog.call_graph.add_edge((),func_ref.1,to_ref.1);
                            fixedpoint &= !changed;
                        }
                    }
                }
            }
        }
    }

    Ok(true)
}

fn insert_call_stub(func_ref: &FunctionRef, to_symbol: Cow<'static,str>, prog: &mut Program) -> Result<(bool,CallGraphRef)> {
    let mut maybe_vx = None;

    for vx in prog.call_graph.vertices() {
        let maybe_lb = prog.call_graph.vertex_label(vx);
        if let Some(&CallTarget::Stub(ref name)) = maybe_lb {
            if *name == to_symbol { maybe_vx = Some(vx); }
        }
    }

    if let Some(to_vx) = maybe_vx {
        if prog.call_graph.edge(func_ref.1,to_vx).is_some() {
            Ok((false,to_vx))
        } else {
            prog.call_graph.add_edge((),func_ref.1,to_vx);
            Ok((true,to_vx))
        }
    } else {
        let to_vx = prog.call_graph.add_vertex(CallTarget::Stub(to_symbol.clone()));

        prog.call_graph.add_edge((),func_ref.1,to_vx);

        Ok((true,to_vx))
    }
}

fn insert_call_address(func_ref: &FunctionRef, to_address: u64, prog: &mut Program) -> Result<(bool,Option<FunctionRef>)> {
    if let Some(to_ref) = prog.find_function_by_entry(to_address) {
        if prog.call_graph.edge(func_ref.1,to_ref.1).is_some() {
            Ok((false,None))
        } else {
            prog.call_graph.add_edge((),func_ref.1,to_ref.1);
            let mut from_func = &mut *func_ref.0.write();
            from_func.resolve_calls(to_address,&to_ref.0.read().uuid);
            Ok((true,None))
        }
    } else {
        use std::sync::Arc;
        use parking_lot::RwLock;

        let to_ref = {
            let from_func = &*func_ref.0.read();
            let mut to_func = Function::new(format!("func_{:x}",to_address),from_func.region.clone());
            let to_uuid = to_func.uuid.clone();
            let to_ent = to_func.cflow_graph.add_vertex(ControlFlowTarget::Value(Rvalue::Constant{ value: to_address, size: 64 }));
            let to_vx = prog.call_graph.add_vertex(CallTarget::Function(to_uuid.clone()));

            to_func.entry_point = Some(to_ent);

            let to_ref = (Arc::new(RwLock::new(to_func)),to_vx);

            prog.functions.insert(to_uuid,to_ref.clone());
            prog.call_graph.add_edge((),func_ref.1,to_ref.1);
            to_ref
        };

        {
            let mut from_func = &mut *func_ref.0.write();
            from_func.resolve_calls(to_address,&to_ref.0.read().uuid);
        }

        Ok((true,Some(to_ref)))
    }
}

/*

fn analyse<A: Analysis>(entry: &FunctionRef, progam: &Program, region: &Region) -> Result<HashMap<Uuid,A::Answer>> {
    let addr_to_function = HashMap::<u64,FunctionRef>::from_iter(progam.functions.iter().filter_map(|f| {
        f.1.read().and_then(|f| {
            f.entry_point.and_then(|ent| {
                f.cflow_graph.vertex_label(ent).and_then(|ct| {
                    if let &ContolFlowTarget::BasicBlock(ref bb) = ct {
                        Some(bb.area.start)
                    } else {
                        None
                    }
                })
            })
        }).map(|a| {
            (a,f.1)
        })
    }));
    let mut answers = HashMap::<Uuid,A::Answer>::new();
    let entry = try!(entry.1.read().ok_or(Err("Entry function not in program".into())));

    while answers.get(entry).is_none() {



}

struct Address {
    value: u64,
    size: usize,
    region: Cow<'static,str>
}

pub struct DisassembleRequest {
    partial: FunctionRef,
    from: Option<FunctionRef>,
    environment: Vec<(Cow<'static,str>,usize,u64)>,
}

pub struct AnalysisRequest {
    func: FunctionRef,
    from: Option<FunctionRef>,
    environment: Vec<(Cow<'static,str>,usize,u64)>,
}

lazy_static!{
    pub static ref DISASSEMBLE_QUEUE: Mutex<Sender<DisassembleRequest>> = {
        let (tx,rx) = channel::<DisassembleRequest>();
        thread::spawn(move || -> Result<()> {
            while let Ok(DisassembleRequest{ partial, from, environment }) = rx.recv() {
                let (new_callees,new_code) = {
                    try!(Controller::read(|sess| -> Result<()> {
                        let mut func_guard = try!(partial.0.write());
                        let mut func = &mut *func_guard;
                        let root = sess.project.data.dependencies.vertex_label(sess.project.data.root).unwrap();
                        try!(pipeline::disassemble(&mut func,&root))
                    }))
                };

                println!("request done");

                for f in new_callees {
                    CALLGRAPH_QUEUE.lock().unwrap().send(CallgraphRequest { from: partial, to: f });
                }

                if new_code {
                    DATAFLOW_QUEUE.lock().unwrap().send(DataflowRequest{ from: from, func: partial, environment: environment });
                }
            }

            Ok(())
        });
        Mutex::new(tx)
    };
    pub static ref CALLGRAPH_QUEUE: Mutex<Sender<CallgraphRequest>> = {
        let (tx,rx) = channel::<CallgraphRequest>();
        thread::spawn(move || -> Result<()> {
            while let Ok(CallgraphRequest{ from: func_ref, to_address, to_region }) = rx.recv() {
                if (is_new,was_updated,to_ref) = {
                    try!(Controller::modify(|sess| {
                                          }))
                };

                if is_new {
                    DISASSEMBLER_QUEUE.lock().unwrap().send(DisassemblerRequest{ partial to_ref, from: from_ref, environment: vec![] });
                } else if was_updated {
                    DATAFLOW_QUEUE.lock().unwrap().send(DataflowRequest{ func: to_ref, from: from_ref, environment: vec![] });
                }
            }
            Ok(())
        });
        Mutex::new(tx)
    }
    pub static ref DATAFLOW_QUEUE: Mutex<Sender<DataflowRequest>> = {
        let (tx,rx) = channel::<AnalysisRequest>();
        thread::spawn(move || -> Result<()> {

            while let Ok(DataflowRequest{ func: func_ref, from: from_ref, environment }) = rx.recv() {
                let (update_callers,update_callees) = {
                    dataflow(&mut func);

                if update_callers {
                    let caller_refs = try!(Controller::read(|sess| {
                        let cg = &sess.project.code[0].call_graph;

                        cg.in_edges(func_ref.1).filter_map(|x| cg.vertex_label(cg.source(x))).collect::<Vec<_>>()
                    };
                    for caller_ref in caller_refs.drain(..) {
                        DATAFLOW_QUEUE.lock().unwrap().send(DataflowRequest{ func: caller_ref, from: func_ref, environment: vec![] });
                    }
                    }

                    if update_callees {
                        let callee_refs = try!(Controller::read(|sess| {
                            let cg = &sess.project.code[0].call_graph;
                            let mut ret = vec![];

                            for e in cg.out_edges(func_ref.1) {
                                let to = cg.vertex_label(cg.target(e)).unwrap();

                                for f in cg.in_edges(to.1) {
                                    let from = cg.vertex_label(cg.source(f)).unwrap();

                                    ret.push((from,to));
                                }
                            }

                            Ok(ret)
                        };
                        for (from_ref,to_ref) in callee_refs.drain(..) {
                            DATAFLOW_QUEUE.lock().unwrap().send(DataflowRequest{ func: to_ref, from: from_ref, environment: vec![] });
                        }
                        }

                    ANALYSIS_QUEUE.lock().unwrap().send(AnalysisRequest{ func: func_ref, from: from_ref, environment: environment });
            }
            Ok(())
        });
        Mutex::new(tx)
    };
    pub static ref ANALYSIS_QUEUE: Mutex<Sender<AnalysisRequest>> = {
        let (tx,rx) = channel::<AnalysisRequest>();
        thread::spawn(move || -> Result<()> {
            use panopticon::Statement;

            while let Ok(AnalysisRequest{ func: func_ref, from: from_ref, environment }) = rx.recv() {
                let maybe_from_uuid = from_ref.clone().map(|x| (*x.0.read().unwrap()).uuid.clone());
                let vals = {
                    let func_guard = try!(func_ref.0.read());
                    let func = &*func_guard;

                    println!("request for analysis of {} called by {:?}",func.uuid,maybe_from_uuid);

                    use std::borrow::Cow;
                    let mut env = HashMap::<(Cow<'static,str>,usize),BoundedAddrTrack>::new();
                    env.insert(("ESP".into(),0),BoundedAddrTrack::Offset{ region: Some(("stack".into(),0)), offset: 0, offset_size: 32 });
                    env.insert(("RSP".into(),0),BoundedAddrTrack::Offset{ region: Some(("stack".into(),0)), offset: 0, offset_size: 64 });

                    let symtbl = HashMap::new();
                    Controller::read(|sess| {
                        let root = sess.project.data.dependencies.vertex_label(sess.project.data.root).unwrap();
                        approximate::<BoundedAddrTrack>(&func,Some(root),&symtbl,&env)
                    }).unwrap().unwrap()
                };

                let (resolved_jumps,new_functions) = {
                    let mut func_guard = try!(func_ref.0.write());
                    let func = &mut *func_guard;
                    let vxs = func.cflow_graph.vertices().collect::<Vec<_>>();
                    let mut resolved_jumps = false;
                    let mut new_functions = vec![];

                    for &vx in vxs.iter() {
                        let maybe_lb = func.cflow_graph.vertex_label_mut(vx);

                        match maybe_lb {
                            Some(&mut ControlFlowTarget::Value(ref mut var@Rvalue::Variable{..})) => {
                                let aval = vals.get(&Lvalue::from_rvalue(var.clone()).unwrap());
                                if let Some(&BoundedAddrTrack::Offset{ ref region, ref offset, ref offset_size }) = aval {
                                    if region.is_none() {
                                        *var = Rvalue::Constant{ value: *offset, size: *offset_size };
                                        debug!("resolved {:?} to {:?}",var,*offset);
                                        resolved_jumps = true;
                                    } else if *offset == 0 {
                                        debug!("resolved {:?} to symbolic value {:?}",var,region);
                                    }
                                }
                            }
                            Some(&mut ControlFlowTarget::BasicBlock(ref mut bb)) => {
                                bb.rewrite(|mut stmt| {
                                    match stmt {
                                        &mut Statement::Call{ target: ref mut var@Rvalue::Variable{..},.. } => {
                                            let aval = vals.get(&Lvalue::from_rvalue(var.clone()).unwrap());
                                            if let Some(&BoundedAddrTrack::Offset{ ref region, ref offset, ref offset_size }) = aval {
                                                if region.is_none() {
                                                    *var = Rvalue::Constant{ value: *offset, size: *offset_size };
                                                    debug!("resolved {:?} to {:?}",var,*offset);
                                                    new_functions.push(*offset);
                                                } else if *offset == 0 {
                                                    debug!("resolved {:?} to symbolic value {:?}",var,region);
                                                }
                                            }
                                        }

                                        &mut Statement::Call{ target: Rvalue::Constant{ value,.. },.. } => {
                                            new_functions.push(value);
                                        }

                                        _ => {}
                                    }
                                })
                            }
                            _ => {}
                        }
                    }

                    (resolved_jumps,new_functions)
                };

                if resolved_jumps {
                    DISASSEMBLER_QUEUE.lock().unwrap().send(DisassembleRequest{ partial: func_ref.clone(), from: from_ref, environment: environment });
                }

                let _ = try!(Controller::modify(|mut sess| -> Result<()> {
                    let mut prog = &mut sess.project.code[0];
                    let from_region = (*func_ref.0.read().unwrap()).region.clone();
                    let from_vx = func_ref.1;

                    for addr in new_functions {
                        match prog.find_function_by_entry(addr) {
                            Some((to_ref,vx)) => {
                                prog.call_graph.add_edge((),from_vx,vx);
                                ANALYSIS_QUEUE.lock().unwrap().send(AnalysisRequest{ func: (to_ref,vx), from: Some(func_ref.clone()), environment: vec![] });
                            }
                            None => {
                                use std::sync::{RwLock,Arc};

                                let mut func = Function::new(format!("func_{:x}",addr),from_region.clone());
                                let to_uuid = func.uuid.clone();
                                let ent = func.cflow_graph.add_vertex(ControlFlowTarget::Value(Rvalue::Constant{ value: addr, size: 64 }));
                                let vx = prog.call_graph.add_vertex(CallTarget::Function(to_uuid.clone()));

                                prog.call_graph.add_edge((),from_vx,vx);
                                func.entry_point = Some(ent);

                                let to_ref = (Arc::new(RwLock::new(func)),vx);
                                prog.functions.insert(to_uuid,to_ref.clone());

                                DISASSEMBLER_QUEUE.lock().unwrap().send(DisassembleRequest{ partial: to_ref, from: Some(func_ref.clone()), environment: vec![] });
                            }
                        }
                    }

                    Ok(())
                }));
            }

            Ok(())
        });
        Mutex::new(tx)
    };
}*/

/// new calls, new code
fn disassemble(func: &mut Function, region: &Region) -> Result<(bool,Vec<CallAddress>)> {
    use graph_algos::VertexListGraphTrait;

    let mut ret = false;

    loop {
        let mut maybe_addr = None;

        for vx in func.cflow_graph.vertices() {
            let maybe_lb = func.cflow_graph.vertex_label(vx);
            if let Some(&ControlFlowTarget::Value(Rvalue::Constant{ ref value,.. })) = maybe_lb {
                maybe_addr = Some(*value);
                break;
            }
        }

        if let Some(entry) = maybe_addr {
            println!("continue disassembling {} at 0x{:x}",func.name,entry);
            ret = true;
            try!(Function::disassemble::<amd64::Amd64>(func,amd64::Mode::Long,entry,&region));
        } else {
            break;
        }
    }

    let new_funcs = func.collect_calls()
        .iter()
        .filter_map(|rv| {
            match rv {
                &Rvalue::Constant{ value,.. } => Some(CallAddress::Address(value)),
                _ => None
            }
        })
        .collect();
    Ok((ret,new_funcs))
}

/*
/// update caller/update callees
fn dataflow(func: &mut Function, callees: Vec<&Function>) -> Result<(bool,bool)> {
    let (read_before,write_before) = variable_access(func);
    let get_ctx = |f| {
        if let Some(vx) = f.entry_point {
            if let Some(&ControlFlowTarget::Concrete(ref bb)) = f.cflow_graph.vertex_label(vx) {
                return Some((bb.area.start,variable_access(f)));
            }
        }
        None
    };
    let callee_info = HashMap::from_iter(callees.filter_map(get_ctx));

    // call vars update
    func.rewrite(|mut stmt| {
        match stmt {
            &mut Statement::Call{ ref mut reads, ref mut writes, target: Rvalue::Constant{ value,.. } } => {
                if let Some((_,(ref new_reads,ref new_writes))) = callee_info.get(value) {
                    reads = new_reads.clone();
                    writes = new_writes.clone();
                }
            }
            _ => {}
        }
    });

    ssa_convertion(&mut func);
    let (read_after,write_after) = variable_access(func);

    Ok((read_after != read_before,write_before != write_after))
}

/// to update callees/new functions/cont disassm
fn analysis(func: &mut Function, region: &Region, initial: &HashMap<(Cow<'static,str>,usize>),A>, last: &HashMap<Lvalue,A>) -> Result<(Vec<(u64,usize>),Vec<(u64,usize>),bool)> {
    println!("request for analysis of {} called by {:?}",func.uuid);

    let symtbl = HashMap::new();
    let vals = approximate::<BoundedAddrTrack>(&func,Some(root),&symtbl,&env)
    let vxs = func.cflow_graph.vertices().collect::<Vec<_>>();
    let mut resolved_jumps = false;
    let mut new_functions = vec![];

    for &vx in vxs.iter() {
        let maybe_lb = func.cflow_graph.vertex_label_mut(vx);

        match maybe_lb {
            Some(&mut ControlFlowTarget::Value(ref mut var@Rvalue::Variable{..})) => {
                let aval = vals.get(&Lvalue::from_rvalue(var.clone()).unwrap());
                if let Some(&BoundedAddrTrack::Offset{ ref region, ref offset, ref offset_size }) = aval {
                    if region.is_none() {
                        *var = Rvalue::Constant{ value: *offset, size: *offset_size };
                        debug!("resolved {:?} to {:?}",var,*offset);
                        resolved_jumps = true;
                    } else if *offset == 0 {
                        debug!("resolved {:?} to symbolic value {:?}",var,region);
                    }
                }
            }
            Some(&mut ControlFlowTarget::BasicBlock(ref mut bb)) => {
                bb.rewrite(|mut stmt| {
                    match stmt {
                        &mut Statement::Call{ target: ref mut var@Rvalue::Variable{..},.. } => {
                            let aval = vals.get(&Lvalue::from_rvalue(var.clone()).unwrap());
                            if let Some(&BoundedAddrTrack::Offset{ ref region, ref offset, ref offset_size }) = aval {
                                if region.is_none() {
                                    *var = Rvalue::Constant{ value: *offset, size: *offset_size };
                                    debug!("resolved {:?} to {:?}",var,*offset);
                                    new_functions.push(*offset);
                                } else if *offset == 0 {
                                    debug!("resolved {:?} to symbolic value {:?}",var,region);
                                }
                            }
                        }

                        &mut Statement::Call{ target: Rvalue::Constant{ value,.. },.. } => {
                            new_functions.push(value);
                        }

                        _ => {}
                    }
                })
            }
            _ => {}
        }
    }
}*/
