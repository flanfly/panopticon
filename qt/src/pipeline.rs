use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{Ordering,AtomicUsize};
use std::fmt::Debug;

use parking_lot::RwLock;
use uuid::Uuid;
use rayon::prelude::*;
use graph_algos::GraphTrait;

use panopticon::{
    Function,
    FunctionRef,
    Region,
    Rvalue,
    amd64,
    Program,
    Result,
    ControlFlowTarget,
};

struct QueryResult<Q: Query> {
    answer: Q::Answer,
    subqueries: Vec<(Uuid,Q)>,
}

trait Query: Send + Sync + Sized + PartialEq + Debug + Clone {
    type Answer: Send + Sync + Sized + PartialEq + Debug;
    fn execute(&self, &Function, &HashMap<Uuid,Vec<(Self,Self::Answer)>>, &HashMap<u64,Uuid>) -> Result<QueryResult<Self>>;
}

#[derive(Debug,Clone,PartialEq,Eq)]
enum QueryState {
    Done,
    Blocked,
    Ready,
}

#[derive(Debug,Clone)]
struct QueryWrapper<Q: Query> {
    id: usize,
    parent: usize,
    function: Uuid,
    query: Q,
    state: QueryState,
}

fn run_query<Q: Query>(entry: &Uuid, query: Q, program: &Program) -> Result<HashMap<Uuid,Vec<(Q,Q::Answer)>>> {
    use std::iter::FromIterator;

    let addr_to_function = HashMap::<u64,Uuid>::from_iter(program.functions.iter().filter_map(|f| {
        let func = (f.1).0.read();
        if let Some(ent) = func.entry_point {
            let cfg = &func.cflow_graph;
            if let Some(&ControlFlowTarget::Resolved(ref bb)) = cfg.vertex_label(ent) {
                return Some((bb.area.start,func.uuid.clone()));
            }
        }
        None
    }));
    let answers = RwLock::new(HashMap::<Uuid,Vec<(Q,Q::Answer)>>::new());
    let mut queries = vec![];
    let next_query = AtomicUsize::new(1);

    queries.push(QueryWrapper{
        id: 0,
        parent: 0,
        function: entry.clone(),
        query: query,
        state: QueryState::Ready,
    });

    while !queries.is_empty() {
        println!("start new query: {:?}",queries);

        queries = try!(queries.into_par_iter().
            map(|mut q| -> Result<Vec<QueryWrapper<Q>>> {
                let id = q.id;
                let mut new_queries = vec![];

                if let QueryWrapper{ state: ref mut state@QueryState::Ready, function: ref func_uuid, ref query, id,.. } = q {
                    println!("run {}",id);
                    let function = try!(program.functions.get(&func_uuid)
                                        .ok_or("Got query for unknown function w/"));
                    let query_res = {
                        try!(query.execute(&*function.0.read(),&*answers.read(),&addr_to_function))
                    };
                    let QueryResult{ answer, mut subqueries } = query_res;
                    let uuid = function.0.read().uuid.clone();
                    let qa_pair = (query.clone(),answer);
                    let fixedpoint = answers.read().get(&uuid).and_then(|x| x.iter().find(|x| **x == qa_pair)).is_some();

                    if fixedpoint || subqueries.is_empty() {
                        *state = QueryState::Done;
                    } else {
                        *state = QueryState::Blocked;
                    }

                    if !fixedpoint {
                        answers.write().entry(uuid).or_insert(vec![]).push(qa_pair);
                        new_queries = subqueries.drain(..)
                            .map(|(uuid,q)| QueryWrapper::<Q>{
                                id: next_query.fetch_add(1,Ordering::Relaxed),
                                parent: id,
                                function: uuid,
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

pub fn run_disassembler(mut functions: Vec<FunctionRef>, program: &Program, region: &Region) -> Result<bool> {
    functions.into_par_iter().map(|fref| -> Result<bool> {
        let mut func = fref.0.write();
        disassemble(&mut *func,region)
    }).reduce(|| Ok(false),|a_,b_| {
        let a = try!(a_);
        let b = try!(b_);
        Ok(a || b)
    })
}

/*

fn analyse<A: Analysis>(entry: &FunctionRef, progam: &Program, region: &Region) -> Result<HashMap<Uuid,A::Answer>> {
    let addr_to_function = HashMap::<u64,FunctionRef>::from_iter(progam.functions.iter().filter_map(|f| {
        f.1.read().and_then(|f| {
            f.entry_point.and_then(|ent| {
                f.cflow_graph.vertex_label(ent).and_then(|ct| {
                    if let &ContolFlowTarget::Resolved(ref bb) = ct {
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
                        let prog = &mut sess.project.code[0];
                        if let Some(to_ref) = prog.find_function_by_entry(to_address) {
                            if prog.call_graph.has_edge(from_ref.1,to_ref.1) {
                                Ok((false,false,to_ref))
                            } else {
                                prog.call_graph.add_edge(from_ref.1,to_ref.1);
                                Ok((false,true,to_ref))
                            }
                        } else {
                            use std::sync::{RwLock,Arc};

                            let mut to_func = Function::new(format!("func_{:x}",to_address),to_region.clone());
                            let to_uuid = to_func.uuid.clone();
                            let to_ent = to_func.cflow_graph.add_vertex(ControlFlowTarget::Unresolved(Rvalue::Constant{ value: to_address, size: 64 }));
                            let to_vx = prog.call_graph.add_vertex(CallTarget::Function(to_uuid.clone()));

                            to_func.entry_point = Some(to_ent);

                            let to_ref = (Arc::new(RwLock::new(to_func)),to_vx);

                            prog.functions.insert(to_uuid,to_ref.clone());
                            prog.call_graph.add_edge(from_ref.1,to_ref.1);

                            Ok((true,true,to_ref))
                        }
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
                            Some(&mut ControlFlowTarget::Unresolved(ref mut var@Rvalue::Variable{..})) => {
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
                            Some(&mut ControlFlowTarget::Resolved(ref mut bb)) => {
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
                                let ent = func.cflow_graph.add_vertex(ControlFlowTarget::Unresolved(Rvalue::Constant{ value: addr, size: 64 }));
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
fn disassemble(func: &mut Function, region: &Region) -> Result<bool> {
    use graph_algos::VertexListGraphTrait;

    let mut ret = false;

    loop {
        let mut maybe_addr = None;

        for vx in func.cflow_graph.vertices() {
            let maybe_lb = func.cflow_graph.vertex_label(vx);
            if let Some(&ControlFlowTarget::Unresolved(Rvalue::Constant{ ref value,.. })) = maybe_lb {
                maybe_addr = Some(*value);
                break;
            }
        }

        if let Some(entry) = maybe_addr {
            println!("request to diassemble {}",entry);
            ret = true;
            try!(Function::disassemble::<amd64::Amd64>(func,amd64::Mode::Long,entry,&region));
        } else {
            break;
        }
    }

    Ok(ret)
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
            Some(&mut ControlFlowTarget::Unresolved(ref mut var@Rvalue::Variable{..})) => {
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
            Some(&mut ControlFlowTarget::Resolved(ref mut bb)) => {
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
