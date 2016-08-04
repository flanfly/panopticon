/*
 * Panopticon - A libre disassembler
 * Copyright (C) 2014,2015,2016 Kai Michaelis
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

use std::hash::Hash;
use std::fmt::Debug;
use std::collections::{HashSet,HashMap};
use std::iter::FromIterator;
use std::borrow::Cow;
use std::cmp;
use num::{Integer,Unsigned,Signed,abs,NumCast};
use num::integer::{lcm,gcd};
use std::ops::{Shl,Shr,BitOr,BitAnd,Div,BitXor};

use graph_algos::{
    GraphTrait,
    IncidenceGraphTrait,
    VertexListGraphTrait,
    BidirectionalGraphTrait,
};
use rustc_serialize::{Encodable,Decodable};
use graph_algos::dominator::{
    immediate_dominator,
};
use graph_algos::order::{
    weak_topo_order,
    HierarchicalOrdering,
};

use {
    Lvalue,Rvalue,
    Statement,Operation,execute,
    ControlFlowTarget,
    ControlFlowRef,
    ControlFlowGraph,
    Function,
    Guard,
    lift,
    Result,
    flag_operations,
};

pub enum Constraint {
    Equal(Rvalue),
    LessUnsigned(Rvalue),
    LessOrEqualUnsigned(Rvalue),
    LessSigned(Rvalue),
    LessOrEqualSigned(Rvalue),
}

#[derive(Debug,PartialEq,Eq,Clone,RustcDecodable,RustcEncodable,PartialOrd,Ord,Hash)]
pub struct ProgramPoint {
    address: u64,
    position: usize,
}

/// Models both under- and overapproximation
pub trait Avalue: Clone + PartialEq + Eq + Hash + Debug + Encodable + Decodable {
    fn abstract_value(&Rvalue) -> Self;
    fn abstract_constraint(&Constraint) -> Self;
    fn execute(&ProgramPoint,&Operation<Self>) -> Self;
    fn narrow(&self,&Self) -> Self;
    fn widen(&self,other: &Self) -> Self;
    fn combine(&self,&Self) -> Self;
    fn more_exact(&self,other: &Self) -> bool;
    fn initial() -> Self;
    fn extract(&self,size: usize,offset: usize) -> Self;
}

/// Bourdoncle: "Efficient chaotic iteration strategies with widenings"
pub fn approximate<A: Avalue>(func: &Function) -> Result<HashMap<Lvalue,A>> {
    if func.entry_point.is_none() {
        return Err("function has no entry point".into());
    }

    let wto = weak_topo_order(func.entry_point.unwrap(),&func.cflow_graph);
    let edge_ops = flag_operations(func);
    fn stabilize<A: Avalue>(h: &Vec<Box<HierarchicalOrdering<ControlFlowRef>>>, graph: &ControlFlowGraph,
                            constr: &HashMap<Lvalue,A>, sizes: &HashMap<Cow<'static,str>,usize>,
                            ret: &mut HashMap<(Cow<'static,str>,usize),A>) -> Result<()> {
        let mut stable = true;
        let mut iter_cnt = 0;
        let head = if let Some(h) = h.first() {
            match &**h {
                &HierarchicalOrdering::Element(ref vx) => vx.clone(),
                &HierarchicalOrdering::Component(ref vec) => return stabilize(vec,graph,constr,sizes,ret),
            }
        } else {
            return Ok(())
        };

        loop {
            for x in h.iter() {
                match &**x {
                    &HierarchicalOrdering::Element(ref vx) =>
                        stable &= !try!(execute(*vx,iter_cnt >= 2 && *vx == head,graph,constr,sizes,ret)),
                    &HierarchicalOrdering::Component(ref vec) => {
                        try!(stabilize(&*vec,graph,constr,sizes,ret));
                        stable = true;
                    },
                }
            }

            if stable {
                for (lv,a) in constr.iter() {
                    if let &Lvalue::Variable{ ref name, subscript: Some(ref subscript),.. } = lv {
                    if let Some(ref mut x) = ret.get_mut(&(name.clone(),*subscript)) {
                        let n = x.narrow(&a);
                        **x = n;
                    }
                    }
                }

                //execute(*vx,do_widen && vx == head,graph,ret),
                return Ok(());
            }

            stable = true;
            iter_cnt += 1;
        }
    }
    fn execute<A: Avalue>(t: ControlFlowRef, do_widen: bool, graph: &ControlFlowGraph,
                          _: &HashMap<Lvalue,A>, sizes: &HashMap<Cow<'static,str>,usize>,
                          ret: &mut HashMap<(Cow<'static,str>,usize),A>) -> Result<bool> {
        if let Some(&ControlFlowTarget::Resolved(ref bb)) = graph.vertex_label(t) {
            let mut change = false;
            let mut pos = 0usize;
            bb.execute(|i| {
                if let Statement{ ref op, assignee: Lvalue::Variable{ ref name, subscript: Some(ref subscript),.. } } = *i {
                    let pp = ProgramPoint{ address: bb.area.start, position: pos };
                    let new = A::execute(&pp,&lift(op,&|x| res::<A>(x,sizes,&ret)));
                    let assignee = (name.clone(),*subscript);
                    let cur = ret.get(&assignee).cloned();

                    if cur.is_none() {
                        change = true;
                        ret.insert(assignee,new);
                    } else {
                        if do_widen {
                            let c = cur.unwrap();
                            let w = c.widen(&new);

                            if w != c {
                                change = true;
                                ret.insert(assignee,w);
                            }
                        } else if new.more_exact(&cur.clone().unwrap()) {
                            change = true;
                            ret.insert(assignee,new);
                        }
                    }
                }

                pos += 1;
            });

            Ok(change)
        } else {
            Ok(false)
        }
    }
    fn res<A: Avalue>(v: &Rvalue, sizes: &HashMap<Cow<'static,str>,usize>, env: &HashMap<(Cow<'static,str>,usize),A>) -> A {
        if let &Rvalue::Variable{ ref name, subscript: Some(ref subscript), ref size, ref offset } = v {
            let nam = (name.clone(),*subscript);
            let t = env.get(&nam).unwrap_or(&A::initial()).clone();

            if *offset > 0 || *size != *sizes.get(&nam.0).unwrap_or(&0) {
                t.extract(*size,*offset)
            } else {
                t
            }
        } else {
            A::abstract_value(v)
        }
    };
    let mut ret = HashMap::<(Cow<'static,str>,usize),A>::new();
    let mut sizes = HashMap::<Cow<'static,str>,usize>::new();
    let mut constr = HashMap::<Lvalue,A>::new();

    for vx in func.cflow_graph.vertices() {
        if let Some(&ControlFlowTarget::Resolved(ref bb)) = func.cflow_graph.vertex_label(vx) {
            bb.execute(|i| {
                if let Lvalue::Variable{ ref name, ref size,.. } = i.assignee {
                    let t = *size;
                    let s = *sizes.get(name).unwrap_or(&t);
                    sizes.insert(name.clone(),cmp::max(s,t));
                }
            });
        }
    }

    for vx in func.cflow_graph.vertices() {
        for e in func.cflow_graph.in_edges(vx) {
            if let Some(&Guard::Predicate{ .. }) = func.cflow_graph.edge_label(e) {
                match edge_ops.get(&e).cloned() {
                    Some(Operation::Equal(left@Rvalue::Constant{ .. },right@Rvalue::Variable{ .. })) => {
                        constr.insert(Lvalue::from_rvalue(right).unwrap(),A::abstract_constraint(&Constraint::Equal(left.clone())));
                    },
                    Some(Operation::Equal(left@Rvalue::Variable{ .. },right@Rvalue::Constant{ .. })) => {
                        constr.insert(Lvalue::from_rvalue(left).unwrap(),A::abstract_constraint(&Constraint::Equal(right.clone())));
                    },
                    Some(Operation::LessUnsigned(left@Rvalue::Constant{ .. },right@Rvalue::Variable{ .. })) => {
                        constr.insert(Lvalue::from_rvalue(right).unwrap(),A::abstract_constraint(&Constraint::LessUnsigned(left.clone())));
                    },
                    Some(Operation::LessUnsigned(left@Rvalue::Variable{ .. },right@Rvalue::Constant{ .. })) => {
                        constr.insert(Lvalue::from_rvalue(left).unwrap(),A::abstract_constraint(&Constraint::LessUnsigned(right.clone())));
                    },
                    Some(Operation::LessSigned(left@Rvalue::Constant{ .. },right@Rvalue::Variable{ .. })) => {
                        constr.insert(Lvalue::from_rvalue(right).unwrap(),A::abstract_constraint(&Constraint::LessSigned(left.clone())));
                    },
                    Some(Operation::LessSigned(left@Rvalue::Variable{ .. },right@Rvalue::Constant{ .. })) => {
                        constr.insert(Lvalue::from_rvalue(left).unwrap(),A::abstract_constraint(&Constraint::LessSigned(right.clone())));
                    },
                    Some(Operation::LessOrEqualUnsigned(left@Rvalue::Constant{ .. },right@Rvalue::Variable{ .. })) => {
                        constr.insert(Lvalue::from_rvalue(right).unwrap(),A::abstract_constraint(&Constraint::LessOrEqualUnsigned(left.clone())));
                    },
                    Some(Operation::LessOrEqualUnsigned(left@Rvalue::Variable{ .. },right@Rvalue::Constant{ .. })) => {
                        constr.insert(Lvalue::from_rvalue(left).unwrap(),A::abstract_constraint(&Constraint::LessOrEqualUnsigned(right.clone())));
                    },
                    Some(Operation::LessOrEqualSigned(left@Rvalue::Constant{ .. },right@Rvalue::Variable{ .. })) => {
                        constr.insert(Lvalue::from_rvalue(right).unwrap(),A::abstract_constraint(&Constraint::LessOrEqualSigned(left.clone())));
                    },
                    Some(Operation::LessOrEqualSigned(left@Rvalue::Variable{ .. },right@Rvalue::Constant{ .. })) => {
                        constr.insert(Lvalue::from_rvalue(left).unwrap(),A::abstract_constraint(&Constraint::LessOrEqualSigned(right.clone())));
                    },
                    _ => {},
                }
            }
        }
    }

    match wto {
        HierarchicalOrdering::Component(ref v) => {
            try!(stabilize(v,&func.cflow_graph,&constr,&sizes,&mut ret));
        },
        HierarchicalOrdering::Element(ref v) => {
            try!(execute(*v,false,&func.cflow_graph,&constr,&sizes,&mut ret));
        },
    }

    Ok(HashMap::from_iter(ret.iter().filter_map(|(&(ref name,ref subscript),val)| {
        if let Some(sz) = sizes.get(name) {
            Some((Lvalue::Variable{
                name: name.clone(),
                subscript: Some(*subscript),
                size: *sz,
            },val.clone()))
        } else {
            None
        }
    })))
}

pub fn results<A: Avalue>(func: &Function,vals: &HashMap<Lvalue,A>) -> HashMap<(Cow<'static,str>,usize),A> {
    let cfg = &func.cflow_graph;
    let idom = immediate_dominator(func.entry_point.unwrap(),cfg);
    let mut ret = HashMap::<(Cow<'static,str>,usize),A>::new();
    let mut names = HashSet::<Cow<'static,str>>::new();

    for vx in cfg.vertices() {
        if let Some(&ControlFlowTarget::Resolved(ref bb)) = cfg.vertex_label(vx) {
            bb.execute(|i| {
                if let Lvalue::Variable{ ref name,.. } = i.assignee {
                    names.insert(name.clone());
                }
            });
        }
    }

    for v in cfg.vertices() {
        if cfg.out_degree(v) == 0 {
            if let Some(&ControlFlowTarget::Resolved(ref bb)) = cfg.vertex_label(v) {
                for lv in names.iter() {
                    let mut bbv = (bb,v);

                    loop {
                        let mut hit = false;
                        bb.execute_backwards(|i| {
                            if let Lvalue::Variable{ ref name, ref size,.. } = i.assignee {
                                if name == lv {
                                    hit = true;
                                    ret.insert((name.clone(),*size),vals.get(&i.assignee).unwrap_or(&A::initial()).clone());
                                }
                            }
                        });

                        if !hit {
                            let next_bb = idom.get(&bbv.1).cloned();
                            let fixpoint = { next_bb == Some(bbv.1) };

                            if !fixpoint {
                                if let Some(w) = next_bb {
                                    if let Some(&ControlFlowTarget::Resolved(ref bb)) = cfg.vertex_label(w) {
                                        bbv = (bb,w);
                                        continue;
                                    }
                                }
                            }
                        }

                        break;
                    }
                }
            }
        }
    }

    ret
}

const KSET_MAXIMAL_CARDINALITY: usize = 10;

#[derive(Debug,Eq,Clone,Hash,RustcDecodable,RustcEncodable)]
pub enum Kset {
    Join,
    Set(Vec<(u64,usize)>),
    Meet,
}

impl PartialEq for Kset {
    fn eq(&self,other: &Kset) -> bool {
        match (self,other) {
            (&Kset::Meet,&Kset::Meet) => true,
            (&Kset::Set(ref a),&Kset::Set(ref b)) =>
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(a,b)| a == b),
                (&Kset::Join,&Kset::Join) => true,
                _ => false
        }
    }
}

impl Avalue for Kset {
    fn abstract_value(v: &Rvalue) -> Self {
        if let &Rvalue::Constant{ ref value, ref size } = v {
            Kset::Set(vec![(if *size < 64 { *value % (1u64 << *size) } else { *value },*size)])
        } else {
            Kset::Join
        }
    }

    fn abstract_constraint(constr: &Constraint) -> Self {
        if let &Constraint::Equal(Rvalue::Constant{ ref value, ref size }) = constr {
            Kset::Set(vec![(if *size < 64 { *value % (1u64 << *size) } else { *value },*size)])
        } else {
            Kset::Join
        }
    }

    fn execute(_: &ProgramPoint, op: &Operation<Self>) -> Self {
        fn permute(_a: &Kset, _b: &Kset, f: &Fn(Rvalue,Rvalue) -> Rvalue) -> Kset {
            match (_a,_b) {
                (&Kset::Join,_) => Kset::Join,
                (_,&Kset::Join) => Kset::Join,
                (&Kset::Set(ref a),&Kset::Set(ref b)) => {
                    let mut ret = HashSet::<(u64,usize)>::new();
                    for &(_x,_xs) in a.iter() {
                        let x = Rvalue::Constant{ value: _x, size: _xs };
                        for &(_y,_ys) in b.iter() {
                            let y = Rvalue::Constant{ value: _y, size: _ys };
                            if let Rvalue::Constant{ value, size } = f(x.clone(),y) {
                                ret.insert((value,size));
                                if ret.len() > KSET_MAXIMAL_CARDINALITY {
                                    return Kset::Join;
                                }
                            }
                        }
                    }

                    if ret.is_empty() {
                        Kset::Meet
                    } else {
                        let mut v = ret.drain().collect::<Vec<(u64,usize)>>();
                        v.sort();
                        Kset::Set(v)
                    }
                },
                _ => Kset::Meet,
            }
        };
        fn map(_a: &Kset, f: &Fn(Rvalue) -> Rvalue) -> Kset {
            if let &Kset::Set(ref a) = _a {
                let mut s = HashSet::<(u64,usize)>::from_iter(
                    a.iter().filter_map(|&(a,_as)| {
                        if let Rvalue::Constant{ value, size } = f(Rvalue::Constant{ value: a, size: _as }) {
                            Some((value,size))
                        } else {
                            None
                        }
                    }));

                if s.len() > KSET_MAXIMAL_CARDINALITY {
                    Kset::Join
                } else if s.is_empty() {
                    Kset::Meet
                } else {
                    let mut v = s.drain().collect::<Vec<(_,_)>>();
                    v.sort();
                    Kset::Set(v)
                }
            } else {
                _a.clone()
            }
        };

        match *op {
            Operation::And(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::And(a,b))),
            Operation::InclusiveOr(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::InclusiveOr(a,b))),
            Operation::ExclusiveOr(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::ExclusiveOr(a,b))),
            Operation::Add(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::Add(a,b))),
            Operation::Subtract(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::Subtract(a,b))),
            Operation::Multiply(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::Multiply(a,b))),
            Operation::DivideSigned(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::DivideSigned(a,b))),
            Operation::DivideUnsigned(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::DivideUnsigned(a,b))),
            Operation::Modulo(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::Modulo(a,b))),
            Operation::ShiftRightSigned(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::ShiftRightSigned(a,b))),
            Operation::ShiftRightUnsigned(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::ShiftRightUnsigned(a,b))),
            Operation::ShiftLeft(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::ShiftLeft(a,b))),

            Operation::LessOrEqualSigned(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::LessOrEqualSigned(a,b))),
            Operation::LessOrEqualUnsigned(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::LessOrEqualUnsigned(a,b))),
            Operation::LessSigned(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::LessSigned(a,b))),
            Operation::LessUnsigned(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::LessUnsigned(a,b))),
            Operation::Equal(ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::Equal(a,b))),

            Operation::Move(ref a) =>
                map(a,&|a| execute(Operation::Move(a))),
            Operation::Call(ref a) =>
                map(a,&|a| execute(Operation::Call(a))),
            Operation::ZeroExtend(ref sz,ref a) =>
                map(a,&|a| execute(Operation::ZeroExtend(*sz,a))),
            Operation::SignExtend(ref sz,ref a) =>
                map(a,&|a| execute(Operation::SignExtend(*sz,a))),
            Operation::Select(ref off,ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::Select(*off,a,b))),

            Operation::Load(ref r,ref a) =>
                map(a,&|a| execute(Operation::Load(r.clone(),a))),
            Operation::Store(ref r,ref a) =>
                map(a,&|a| execute(Operation::Store(r.clone(),a))),

            Operation::Phi(ref ops) => {
                match ops.len() {
                    0 => unreachable!("Phi function w/o arguments"),
                    1 => ops[0].clone(),
                    _ => ops.iter().fold(Kset::Meet,|acc,x| acc.combine(&x))
                }
            }
        }
    }

    fn narrow(&self, a: &Self) -> Self {
        match a {
            &Kset::Meet => Kset::Meet,
            &Kset::Join => self.clone(),
            &Kset::Set(ref v) => {
                match self {
                    &Kset::Meet => Kset::Meet,
                    &Kset::Join => Kset::Set(v.clone()),
                    &Kset::Set(ref w) => {
                        let set = HashSet::<&(u64,usize)>::from_iter(v.iter());
                        Kset::Set(w.iter().filter(|x| set.contains(x)).cloned().collect::<Vec<_>>())
                    },
                }
            },
        }
    }

    fn combine(&self,a: &Self) -> Self {
        match (self,a) {
            (&Kset::Join,_) => Kset::Join,
            (_,&Kset::Join) => Kset::Join,
            (a,&Kset::Meet) => a.clone(),
            (&Kset::Meet,b) => b.clone(),
            (&Kset::Set(ref a),&Kset::Set(ref b)) => {
                let mut ret = HashSet::<&(u64,usize)>::from_iter(a.iter().chain(b.iter()))
                    .iter().cloned().cloned().collect::<Vec<(u64,usize)>>();
                ret.sort();
                if ret.is_empty() {
                    Kset::Meet
                } else if ret.len() > KSET_MAXIMAL_CARDINALITY {
                    Kset::Join
                } else {
                    Kset::Set(ret)
                }
            },
        }
    }

    fn widen(&self,s: &Self) -> Self {
        s.clone()
    }

    fn initial() -> Self {
        Kset::Meet
    }

    fn more_exact(&self, a: &Self) -> bool {
        if self == a {
            false
        } else {
            match (self,a) {
                (&Kset::Join,_) => true,
                (_,&Kset::Meet) => true,
                (&Kset::Set(ref a),&Kset::Set(ref b)) =>
                    HashSet::<&(u64,usize)>::from_iter(a.iter())
                    .is_superset(&HashSet::from_iter(b.iter())),
                    _ => false,
            }
        }
    }

    fn extract(&self,size: usize,offset: usize) -> Self {
        match self {
            &Kset::Join => Kset::Join,
            &Kset::Meet => Kset::Meet,
            &Kset::Set(ref v) =>
                Kset::Set(v.iter().map(|&(v,_)| {
                    ((v >> offset) % (1 << (size - 1)),size)
                }).collect::<Vec<_>>()),
        }
    }
}

/// Mihaila et.al. Widening Point cofibered domain
#[derive(Debug,PartialEq,Eq,Clone,Hash,RustcDecodable,RustcEncodable)]
pub struct Widening<A: Avalue> {
    value: A,
    point: Option<ProgramPoint>,
}

impl<A: Avalue> Avalue for Widening<A> {
    fn abstract_value(v: &Rvalue) -> Self {
        Widening{
            value: A::abstract_value(v),
            point: None,
        }
    }

    fn abstract_constraint(c: &Constraint) -> Self {
        Widening{
            value: A::abstract_constraint(c),
            point: None,
        }
    }

    fn execute(pp: &ProgramPoint, op: &Operation<Self>) -> Self {
        match op {
            &Operation::Phi(ref ops) => {
                let widen = ops.iter().map(|x| x.point.clone().unwrap_or(pp.clone())).max() > Some(pp.clone());

                Widening{
                    value: match ops.len() {
                        0 => unreachable!("Phi function w/o arguments"),
                        1 => ops[0].value.clone(),
                        _ => ops.iter().map(|x| x.value.clone()).fold(A::initial(),|acc,x| {
                            if widen {
                                acc.widen(&x)
                            } else {
                                acc.combine(&x)
                            }
                        }),
                    },
                    point: Some(pp.clone()),
                }
            },
            _ => Widening{
                value: A::execute(pp,&lift(op,&|x| x.value.clone())),
                point: Some(pp.clone()),
            }
        }
    }

    fn widen(&self,s: &Self) -> Self {
        Widening{
            value: self.value.widen(&s.value),
            point: self.point.clone(),
        }
    }

    fn combine(&self,s: &Self) -> Self {
        Widening{
            value: self.value.combine(&s.value),
            point: self.point.clone(),
        }
    }

    fn narrow(&self, _: &Self) -> Self {
        self.clone()
    }

    fn initial() -> Self {
        Widening{
            value: A::initial(),
            point: None,
        }
    }

    fn more_exact(&self, a: &Self) -> bool {
        self.value.more_exact(&a.value)
    }

    fn extract(&self,size: usize,offset: usize) -> Self {
        Widening{
            value: self.value.extract(size,offset),
            point: self.point.clone(),
        }
    }
}

/// Zhan and Koutsoukos: Generic Value-Set Analysis on Low-Level Code
#[derive(Debug,PartialEq,Eq,Clone,Hash,RustcDecodable,RustcEncodable)]
pub enum ExtStridedInterval {
    Join,
    Interval{
        stride: u64,
        first: u64,
        last: u64,
        size: usize,
    },
    Meet,
}

impl ExtStridedInterval {
    fn dsi(&self) -> Vec<ExtStridedInterval> {
        match *self {
            ExtStridedInterval::Meet => vec![],
            ExtStridedInterval::Interval{ stride, first, last, size } => {
                let signed_max = (1u64 << cmp::max(size - 1,63)) - 1;
                let l = if size < 64 { 0xffffffffffffffff % (1 << size) } else { 0xffffffffffffffff };
                if first > signed_max && last > 0 {
                    vec![
                        ExtStridedInterval::Interval{
                            stride: stride, first: 0, last: last, size: size },
                        ExtStridedInterval::Interval{
                            stride: stride, first: first, last: l, size: size }
                    ]
                } else {
                    vec![ExtStridedInterval::Interval{
                        stride: stride, first: first, last: last, size: size }]
                }
            },
            ExtStridedInterval::Join => vec![],
        }
    }
}

impl Avalue for ExtStridedInterval {
    fn abstract_value(v: &Rvalue) -> Self {
        if let &Rvalue::Constant{ ref value, ref size } = v {
            ExtStridedInterval::Interval{ stride: 0, first: *value, last: *value, size: *size }
        } else {
            ExtStridedInterval::Join
        }
    }

    fn extract(&self,size: usize,offset: usize) -> Self {
        unimplemented!()
    }

    fn abstract_constraint(constr: &Constraint) -> Self {
        unimplemented!()
    }

    fn execute(_: &ProgramPoint,_: &Operation<Self>) -> Self {
        unimplemented!()
    }

    /*
        match *op {
            //Operation::And(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::And(a,b))),
            //Operation::InclusiveOr(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::InclusiveOr(a,b))),
            //Operation::ExclusiveOr(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::ExclusiveOr(a,b))),
            Operation::Add(ExtStridedInterval::Interval{ stride: a_stride, first: a_first, last: a_last, size: a_size },
                           ExtStridedInterval::Interval{ stride: b_stride, first: b_first, last: b_last, size: b_size }) => {
                let stride = gcd(a_stride,b_stride);
                let size = cmp::max(a_size,b_size);
                let maybe_first = a_first.checked_add(b_first);
                let maybe_last = a_last.checked_add(b_last);

                match (maybe_first,maybe_last) {
                    (Some(first),Some(last)) => {
                        ExtStridedInterval::Interval{
                            stride: stride,
                            first: if size < 64 { first % (1 << size) } else { first },
                            last: if size < 64 { last % (1 << size) } else { last },
                            size: size,
                        }
                    },
                    _ => {
                        

                let last = (a_last + b_last) % (1 << size);

                ExtStridedInterval::Interval{
                    stride: stride,
                    first: first,
                    last: last,
                    size: size,
                }
            },
            Operation::Subtract(ExtStridedInterval::Interval{ stride: a_stride, first: a_first, last: a_last, size: a_size },
                                ExtStridedInterval::Interval{ stride: b_stride, first: b_first, last: b_last, size: b_size }) => {
                let stride = gcd(a_stride,b_stride);
                let size = cmp::max(a_size,b_size);
                let first = (a_first - b_last) % (1 << size);
                let last = (a_last - b_first) % (1 << size);

                ExtStridedInterval::Interval{
                    stride: stride,
                    first: first,
                    last: last,
                    size: size,
                }
            },
            //Operation::Multiply(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::Multiply(a,b))),
            //Operation::DivideSigned(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::DivideSigned(a,b))),
            //Operation::DivideUnsigned(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::DivideUnsigned(a,b))),
            //Operation::Modulo(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::Modulo(a,b))),
            //Operation::ShiftRightSigned(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::ShiftRightSigned(a,b))),
            //Operation::ShiftRightUnsigned(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::ShiftRightUnsigned(a,b))),
            //Operation::ShiftLeft(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::ShiftLeft(a,b))),

            //Operation::LessOrEqualSigned(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::LessOrEqualSigned(a,b))),
            //Operation::LessOrEqualUnsigned(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::LessOrEqualUnsigned(a,b))),
            //Operation::LessSigned(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::LessSigned(a,b))),
            //Operation::LessUnsigned(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::LessUnsigned(a,b))),
            //Operation::Equal(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::Equal(a,b))),

            //Operation::Move(ref a) =>
            //    map(a,&|a| execute(Operation::Move(a))),
            //Operation::Call(ref a) =>
            //    map(a,&|a| execute(Operation::Call(a))),
            //Operation::ZeroExtend(ref sz,ref a) =>
            //    map(a,&|a| execute(Operation::ZeroExtend(*sz,a))),
            //Operation::SignExtend(ref sz,ref a) =>
            //    map(a,&|a| execute(Operation::SignExtend(*sz,a))),

            //Operation::Load(ref r,ref a) =>
            //    map(a,&|a| execute(Operation::Load(r.clone(),a))),
            //Operation::Store(ref r,ref a) =>
            //    map(a,&|a| execute(Operation::Store(r.clone(),a))),

            //Operation::Phi(_) => unreachable!(),
            _ => ExtStridedInterval::Join,
        }
    }*/

    fn narrow(&self, a: &Self) -> Self {
        unimplemented!()
    }

    fn combine(&self,a: &Self) -> Self {
        ExtStridedInterval::Join
    }
    
    fn widen(&self,_: &Self) -> Self {
        ExtStridedInterval::Join
    }

    fn initial() -> Self {
        ExtStridedInterval::Meet
    }

    fn more_exact(&self, a: &Self) -> bool {
        unimplemented!()
    }
}

// Linus Kaellberg: "Circular Linear Progressions in SWEET"
#[derive(Debug,PartialEq,Eq,Clone,Hash,RustcDecodable,RustcEncodable)]
pub struct Clp<I: Integer + Signed + Decodable + Encodable + Clone + Shr<usize,Output=I> + Shl<usize,Output=I> + BitOr<Output=I> + BitAnd<Output=I>> {
    pub width: usize,
    pub base: I,
    pub stride: I,
    pub cardinality: I,
}


impl<I: Integer + NumCast + Signed + Decodable + Encodable + Debug + Clone + Copy + Shr<I,Output=I> + Shl<I,Output=I> + Shr<usize,Output=I> + Shl<usize,Output=I> + BitOr<Output=I> + BitAnd<Output=I> + Div + BitXor<Output=I>> Clp<I> {
    /// Computes the gcd of a and b, and the Bezout coeffcient of a
    fn eea(a: &I,b: &I) -> (I,I) {
        let mut s = I::zero();
        let mut prev_s = I::one();
        let mut r = b.clone();
        let mut prev_r = a.clone();

        while r != I::zero() {
            let q = prev_r / r;
            let tmp_r = r;
            let tmp_s = s;

            r = prev_r - q * r;
            prev_r = tmp_r;

            s = prev_s - q * s;
            prev_s = tmp_s;
        }

        (prev_r,prev_s)
    }

    fn count_ones(mut a: I) -> I {
        let mut ret = I::zero();

        while a != I::zero() {
            if a & I::one() == I::one() {
                ret = ret + I::one();
            }
            a = a >> 1;
        }

        ret
    }

    fn trailing_zeros(_a: &I) -> isize {
        let mut ret = 0;
        let mut a = _a.clone();

        if a == I::zero() { unreachable!() }

        while a & I::one() == I::zero() {
            ret += 1;
            a = a >> 1;
        }

        ret
    }

    fn most_significant_bit(_a: &I) -> isize {
        let mut ret = 0;
        let mut a = _a.clone();

        if a == I::zero() { unreachable!() }

        while a != I::zero() {
            ret += 1;
            a = a >> 1;
        }

        ret
    }

    pub fn is_bottom(&self) -> bool {
        self.cardinality == I::zero()
    }

    pub fn is_top(&self) -> bool {
        let c = cmp::max(I::zero(),self.cardinality);
        c <= Self::mask(self.width) && self.stride.is_odd()
    }

    pub fn last(&self) -> I {
        if self.cardinality <= I::zero() {
            unreachable!()
        } else {
            self.base + self.stride * (self.cardinality - I::one())
        }
    }

    // Arithmetic negation
    fn minus(a: &Clp<I>) -> Clp<I> {
        if a.is_bottom() {
            a.clone()
        } else {
            Clp::<I>{
                width: a.width,
                base: (I::zero() - I::one()) * a.last(),
                stride: a.stride,
                cardinality: a.cardinality
            }
        }
    }

    // Logic (bitwise) negation
    fn negate(a: &Clp<I>) -> Clp<I> {
        if a.is_bottom() {
            a.clone()
        } else {
            Clp::<I>{
                width: a.width,
                base: a.last() ^ Self::mask(a.width),
                stride: a.stride,
                cardinality: a.cardinality
            }
        }
    }

    fn mask(w: usize) -> I {
        let mut ret = I::one();

        for _ in 1..w {
            ret = ret << 1;
            ret = ret | I::one();
        }

        ret
    }

    fn intersection(_: &Clp<I>, _: &Clp<I>) -> Clp<I> {
        unimplemented!()
    }

    pub fn unsigned_progression(_a: &Clp<I>) -> Vec<Clp<I>> {
        let a = Self::canonize(_a);
        let mut i = I::zero();
        let mut j = I::zero();
        let msk = Self::mask(a.width);
        let split_pnt = msk + I::one();
        let mut ret = vec![];

        while i < a.cardinality {
            let first = a.base + (i * a.stride);
            let c = cmp::max(I::zero(),a.cardinality);
            let max = a.base + (c - I::one()) * a.stride;
            let last = cmp::min(max,split_pnt * (j + I::one()));
            let n = (last - first) / a.stride + I::one();

            if n <= I::zero() { break; }

            ret.push(Clp::<I>{
                width: a.width,
                base: first - (j * split_pnt),
                stride: a.stride,
                cardinality: n,
            });

            i = i + n;
            j = j + I::one();
        }

        ret
    }

    pub fn signed_progression(_a: &Clp<I>) -> Vec<Clp<I>> {
        let a = Self::canonize(_a);
        let mut i = I::zero();
        let mut j = I::zero();
        let span = Self::mask(a.width) + I::one();
        let split_pnt = span / (I::one() + I::one());
        let mut ret = vec![];

        while i < a.cardinality {
            let first = a.base + i * a.stride - j * span;
            let c = cmp::max(I::zero(),a.cardinality);
            let max = a.base + (c - I::one()) * a.stride - j * span;
            let last = cmp::min(max,split_pnt * (j + I::one()));
            let n = (last - first) / a.stride + I::one();

            if n <= I::zero() { break; }

            ret.push(Clp::<I>{
                width: a.width,
                base: first,
                stride: a.stride,
                cardinality: n,
            });

            i = i + n;
            j = j + I::one();
        }

        ret
    }

    pub fn union(_a: &Clp<I>, _b: &Clp<I>) -> Clp<I> {
        assert_eq!(_a.width, _b.width);

        let a = Clp::<I>::canonize(_a);
        let b = Clp::<I>::canonize(_b);

        if a.is_bottom() { return b; } else if b.is_bottom() { return a; }

        if a.cardinality == I::one() && b.cardinality == I::one() {
            return Clp::<I>{
                width: a.width,
                base: cmp::min(a.base,b.base),
                stride: abs(a.base - b.base),
                cardinality: I::one() + I::one(),
            };
        }

        fn _union<
            I: Integer + Signed + Decodable + Encodable + Clone + Copy + Debug + Shr<usize,Output=I> + Shl<usize,Output=I> + BitOr<Output=I> + BitAnd<Output=I>>(a: &Clp<I>, b: &Clp<I>) -> Clp<I> {
            let ca = cmp::max(I::zero(),a.cardinality);
            let cb = cmp::max(I::zero(),b.cardinality);
            let la = a.base + a.stride * (ca - I::one());
            let lb = b.base + b.stride * (cb - I::one());
            let base = cmp::min(a.base,b.base);
            let t1 = cmp::max(la,lb);
            let s = gcd(gcd(a.stride,b.stride),abs(a.base - b.base));

            Clp::<I>{
                width: a.width,
                base: base,
                stride: s,
                cardinality: cmp::max(I::zero(),(((t1 - base) / s) + I::one())),
            }
        }

        let w = Self::mask(a.width) + I::one();
        let mut ret: Option<Clp<I>> = None;
        let mut m = I::zero() - I::one();
        for _ in -1..2 {
            let x = _union(&a,&Clp::<I>{
                width: b.width,
                base: b.base + w * m,
                stride: b.stride,
                cardinality: b.cardinality
            });

            if ret.is_none() || ret.as_ref().unwrap().cardinality > x.cardinality {
                ret = Some(x)
            }

            m = m + I::one();
        }

        ret.unwrap()
    }

    pub fn canonize(a: &Clp<I>) -> Clp<I> {
        let msk = Self::mask(a.width);
        let w = msk + I::one();
        match a {
            &Clp::<I>{ width, cardinality: ref c,.. } if *c == I::zero() =>
                Clp::<I>{
                    width: width,
                    base: I::zero(),
                    stride: I::zero(),
                    cardinality: I::zero(),
                },
            &Clp::<I>{ width,ref base, cardinality: ref c,.. } if *c == I::one() =>
                Clp::<I>{
                    width: width,
                    base: *base & msk,
                    stride: I::zero(),
                    cardinality: I::one(),
                },
            &Clp::<I>{ width, base, stride, cardinality } => {
                let k = if stride == I::zero() { I::one() } else { lcm(w,stride) / stride };
                let c = cmp::max(I::zero(),cardinality);

                if c >= k && k >= I::one() + I::one() {
                    let s = gcd(stride,w) & msk;

                    Clp::<I>{
                        width: width,
                        base: base % s,
                        stride: s,
                        cardinality: cmp::max(I::zero(),k),
                    }
                } else if c == k - I::one() && c >= I::one() + I::one() {
                    let s = gcd(stride,w) & msk;

                    Clp::<I>{
                        width: width,
                        base: (base + (c * stride) + s) & msk,
                        stride: gcd(stride,w) & msk,
                        cardinality: cardinality,
                    }
                } else {
                    if stride & msk < w >> 1 {
                        Clp::<I>{
                            width: width,
                            base: base & msk,
                            stride: stride & msk,
                            cardinality: cardinality,
                        }
                    } else {
                        let b = (c - I::one()) * stride + base;
                        Clp::<I>{
                            width: width,
                            base: b & msk,
                            stride: (w - stride) & msk,
                            cardinality: cardinality,
                        }
                    }
                }
            },
        }
    }

    fn execute(pp: &ProgramPoint, op: &Operation<Self>) -> Self {
        fn permute<
            I: Integer + NumCast + Signed + Decodable + Encodable + Clone + Copy + Debug + Shr<I,Output=I> + Shl<I,Output=I> + Shr<usize,Output=I> + Shl<usize,Output=I> + BitOr<Output=I> + BitAnd<Output=I> + BitXor<Output=I>
            >(a: Vec<Clp<I>>, b: Vec<Clp<I>>, f: &Fn(Clp<I>,Clp<I>) -> Clp<I>) -> Clp<I> {
            let mut ret: Option<Clp<I>> = None;
            for x in a.iter() {
                for y in b.iter() {
                    let c = f(x.clone(),y.clone());
                    if let Some(ref mut t) = ret {
                        *t = Clp::<I>::union(t,&c);
                    } else {
                        ret = Some(c);
                    }
                }
            }

            ret.unwrap()
        }

        match *op {
            Operation::And(ref a,ref b) => {
                if a.is_bottom() { return a.clone(); }
                if b.is_bottom() { return b.clone(); }

                let a_aps = Self::unsigned_progression(a);
                let b_aps = Self::unsigned_progression(b);

                permute(a_aps,b_aps,&|a,b| {
                    if a.cardinality == I::one() && b.cardinality == I::one() {
                        Clp::<I>{
                            width: a.width,
                            base: a.base & b.base,
                            stride: I::zero(),
                            cardinality: I::one(),
                        }
                    } else if a.cardinality == I::one() && b.cardinality == I::one() + I::one() {
                        Clp::<I>{
                            width: a.width,
                            base: a.base & b.base,
                            stride: (a.base & b.last()) - (a.base & b.base),
                            cardinality: I::one() + I::one(),
                        }
                    } else if a.cardinality == I::one() + I::one() && b.cardinality == I::one() {
                        Clp::<I>{
                            width: a.width,
                            base: a.base & b.base,
                            stride: (a.last() & b.base) - (a.base & b.base),
                            cardinality: I::one() + I::one(),
                        }
                    } else {
                        let (l1, u1) = if a.cardinality == I::one() {
                            (a.width as isize,-1)
                        } else {
                            (Clp::<I>::trailing_zeros(&a.stride),Clp::<I>::most_significant_bit(&(a.base ^ a.last())))
                        };
                        let (l2, u2) = if b.cardinality == I::one() {
                            (b.width as isize,-1)
                        } else {
                            (Clp::<I>::trailing_zeros(&b.stride),Clp::<I>::most_significant_bit(&(b.base ^ b.last())))
                        };

                        let l = if l1 < l2 {
                            let msk = Self::mask((l2 - l1) as usize) << l1 as usize;
                            let v = b.base & msk;
                            if v == I::zero() { l2 } else { Clp::<I>::trailing_zeros(&v) }
                        } else if l1 > l2 {
                            let msk = Self::mask((l1 - l2) as usize) << l2 as usize;
                            let v = b.base & msk;
                            if v == I::zero() { l1 } else { Clp::<I>::trailing_zeros(&v) }
                        } else {
                            assert_eq!(l1, l2);
                            l1
                        };

                        let u = if u1 < u2 {
                            let msk = Self::mask((u2 - u1) as usize) << u1 as usize;
                            let v = b.base & msk;
                            if v == I::zero() { u2 } else { Clp::<I>::trailing_zeros(&v) }
                        } else if u1 > u2 {
                            let msk = Self::mask((u1 - u2) as usize) << u2 as usize;
                            let v = b.base & msk;
                            if v == I::zero() { u1 } else { Clp::<I>::trailing_zeros(&v) }
                        } else {
                            assert_eq!(u1, u2);
                            u1
                        };

                        if l <= u {
                            let uu = if u1 > u2 && u == u1 {
                                let mut r = u1;
                                for i in u1 as usize..b.width {
                                    if (b.base >> i) & I::one() == I::one() {
                                        r = i as isize;
                                    } else {
                                        break;
                                    }
                                }
                                r
                            } else if u1 < u2 && u == u2 {
                                let mut r = u2;
                                for i in u2 as usize..a.width {
                                    if (a.base >> i) & I::one() == I::one() {
                                        r = i as isize;
                                    } else {
                                        break;
                                    }
                                }
                                r
                            } else {
                                u + 1
                            };

                            let stride = if u1 > u2 && u == u1 && uu == l {
                                cmp::max(a.stride,I::one() << l as usize)
                            } else if u2 > u1 && u == u2 && uu == l {
                                cmp::max(b.stride,I::one() << l as usize)
                            } else {
                                I::one() << l as usize
                            };
                            let m = if l < uu { Self::mask((uu - l) as usize) << l as usize } else { Self::mask(a.width) };
                            let low = (a.base & b.base) & m;
                            let up = cmp::min((a.last() & b.last()) | m,cmp::min(a.last(),b.last()));
                            let t = low - (a.base & b.base);
                            let o = if t % stride > I::zero() { I::one() } else { I::zero() };
                            let base = (a.base & b.base) + stride * ((t / stride) + o);
                            let cardinality = (up - base) / stride + I::one();

                            Clp::<I>{
                                width: a.width,
                                base: base,
                                stride: stride,
                                cardinality: cardinality,
                            }
                        } else {
                            Clp::<I>{
                                width: a.width,
                                base: a.base & b.base,
                                stride: I::zero(),
                                cardinality: I::one(),
                            }
                        }
                    }
                })
            },
            Operation::InclusiveOr(ref a,ref b) => {
                Self::negate(&Clp::execute(pp,&Operation::And(Self::negate(a),Self::negate(b))))
            },
            Operation::ExclusiveOr(ref a,ref b) => {
                let x = Clp::execute(pp,&Operation::And(Self::negate(a),b.clone()));
                let y = Clp::execute(pp,&Operation::And(a.clone(),Self::negate(b)));
                Clp::execute(pp,&Operation::InclusiveOr(x,y))
            },
            Operation::Add(ref _a, ref _b) => {
                let a = Clp::canonize(_a);
                let b = Clp::canonize(_b);

                assert_eq!(a.width,b.width);

                if a.is_bottom() { return a; }
                if b.is_bottom() { return b; }

                let base = a.base + b.base;

                if a.cardinality == I::one() && b.cardinality == I::one() {
                    return Clp{
                        width: a.width,
                        base: base,
                        stride: I::zero(),
                        cardinality: I::one(),
                    }
                }

                let stride = gcd(a.stride,b.stride);
                let a_last = a.base + (a.cardinality - I::one()) * a.stride;
                let b_last = b.base + (b.cardinality - I::one()) * b.stride;
                let cardinality = (a_last + b_last - base) / stride + I::one();

                Clp{
                    width: a.width,
                    base: base,
                    stride: stride,
                    cardinality: cardinality,
                }
            },
            Operation::Subtract(ref a, ref b) => {
                Clp::execute(pp,&Operation::Add(a.clone(),Self::minus(b)))
            },
            Operation::Multiply(ref a,ref b) => {
                if a.is_bottom() { return a.clone(); }
                if b.is_bottom() { return b.clone(); }

                let w = cmp::max(a.width,b.width);
                let a_aps = Self::unsigned_progression(a);
                let b_aps = Self::unsigned_progression(b);

                permute(a_aps,b_aps,&|a,b| {
                    let base = a.base * b.base;
                    if a.cardinality == I::one() || b.cardinality == I::one() {
                        Clp::<I>{
                            width: w,
                            base: base,
                            stride: I::zero(),
                            cardinality: I::one()
                        }
                    } else {
                        let stride = gcd(gcd(
                                a.base * b.stride,
                                b.base * a.stride),
                                a.stride * b.stride);
                        let cardinality = (a.last() * b.last() - base) / stride + I::one();

                        Clp::<I>{
                            width: w,
                            base: base,
                            stride: stride,
                            cardinality: cardinality
                        }
                    }
                })
            },
            Operation::DivideSigned(ref a,ref b) => {
                if a.is_bottom() { return a.clone(); }
                if b.is_bottom() { return b.clone(); }
                if b.base == I::zero() {
                    return Clp::<I>{
                        width: b.width,
                        base: I::zero(),
                        stride: I::one(),
                        cardinality: Clp::<I>::mask(b.width),
                    };
                }

                let modu = Self::mask(a.width) + I::one();
                if (modu - b.base) % b.stride == I::zero() {
                    if (modu - b.base) - b.stride < b.cardinality {
                        return Clp::<I>{
                            width: b.width,
                            base: I::zero(),
                            stride: I::one(),
                            cardinality: Clp::<I>::mask(b.width),
                        };
                    }
                }
                
                let a_aps = Self::signed_progression(a);
                let mut b_aps = vec![];

                for b in Self::signed_progression(b) {
                    if b.base < I::zero() && b.last() >= I::zero() {
                        let c = ((I::zero() - I::one()) * b.base) / b.stride;
                        b_aps.push(Clp::<I>{
                            width: b.width,
                            base: b.base,
                            stride: b.stride,
                            cardinality: c
                        });
                        b_aps.push(Clp::<I>{
                            width: b.width,
                            base: b.base + c * b.stride,
                            stride: b.stride,
                            cardinality: b.cardinality - c
                        });
                    } else {
                        b_aps.push(b);
                    }
                }

                permute(a_aps,b_aps,&|a,b| {
                    if a.cardinality == I::one() && b.cardinality == I::one() {
                        return Clp::<I>{
                            width: a.width,
                            base: a.base / b.base,
                            stride: I::zero(),
                            cardinality: I::one(),
                        };
                    }


                    let base = cmp::min(a.base / b.base,
                        cmp::min(a.base / b.last(),
                        cmp::min(a.last() / b.base,
                        a.last() / b.last())));
                    let d = cmp::max(a.base / b.base,
                        cmp::max(a.base / b.last(),
                        cmp::max(a.last() / b.base,
                        a.last() / b.last())));
                    let stride = if b.cardinality <= I::from(10).unwrap() {
                            let mut c1 = true;
                            let mut c2 = true;
                            let mut r = None;
                            let mut i = I::zero();

                            while i < b.cardinality {
                                let v = b.base + i * b.stride;
                                let g = gcd(a.base / v - base,abs(a.stride / v));

                                c1 &= v.divides(&a.base) && v.divides(&a.stride);
                                c2 &= v.divides(&a.stride);

                                if r.is_none() { r = Some(g) } else { r = Some(gcd(g,r.unwrap())) }

                                i = i + I::one();
                            }

                            if c1 || c2 && (a.last() < I::zero() && a.base > I::zero()) && r.is_some() {
                                r.unwrap()
                            } else {
                                I::one()
                            }
                        } else {
                            I::one()
                        };
                    let cardinality = (d - base) / stride + I::one();

                    Clp::<I>{
                        width: a.width,
                        base: base,
                        stride: stride,
                        cardinality: cardinality
                    }
                })
            },
            Operation::DivideUnsigned(ref a,ref b) => {
                if a.is_bottom() { return a.clone(); }
                if b.is_bottom() { return b.clone(); }
                if b.base == I::zero() {
                    return Clp::<I>{
                        width: b.width,
                        base: I::zero(),
                        stride: I::one(),
                        cardinality: Clp::<I>::mask(b.width),
                    };
                }

                let modu = Self::mask(a.width) + I::one();
                if (modu - b.base) % b.stride == I::zero() {
                    if (modu - b.base) - b.stride < b.cardinality {
                        return Clp::<I>{
                            width: b.width,
                            base: I::zero(),
                            stride: I::one(),
                            cardinality: Clp::<I>::mask(b.width),
                        };
                    }
                }
                
                let a_aps = Self::signed_progression(a);
                let b_aps = Self::signed_progression(a);

                permute(a_aps,b_aps,&|a,b| {
                    if a.cardinality == I::one() && b.cardinality == I::one() {
                        return Clp::<I>{
                            width: a.width,
                            base: a.base / b.base,
                            stride: I::zero(),
                            cardinality: I::one(),
                        };
                    }

                    let base = a.base / b.last();
                    let stride = if b.cardinality <= I::from(10).unwrap() {
                            let mut c = true;
                            let mut r = None;
                            let mut i = I::zero();

                            while i < b.cardinality {
                                let v = b.base + i * b.stride;
                                let g = gcd(a.base / v - base,a.stride / v);

                                c &= v.divides(&a.stride);

                                if r.is_none() { r = Some(g) } else { r = Some(gcd(g,r.unwrap())) }
                                i = i + I::one();
                            }

                            if c && r.is_some() {
                                r.unwrap()
                            } else {
                                I::one()
                            }
                        } else {
                            I::one()
                        };
                    let cardinality = (a.last() / b.base - base) / stride + I::one();

                    Clp::<I>{
                        width: a.width,
                        base: base,
                        stride: stride,
                        cardinality: cardinality
                    }
                })
            },
            Operation::Modulo(ref a,ref b) => {
                let a_aps = Self::signed_progression(a);
                let mut b_aps = vec![];

                for b in Self::signed_progression(b) {
                    if b.base < I::zero() && b.last() >= I::zero() {
                        let c = ((I::zero() - I::one()) * b.base) / b.stride;
                        b_aps.push(Clp::<I>{
                            width: b.width,
                            base: b.base,
                            stride: b.stride,
                            cardinality: c
                        });
                        b_aps.push(Clp::<I>{
                            width: b.width,
                            base: b.base + c * b.stride,
                            stride: b.stride,
                            cardinality: b.cardinality - c
                        });
                    } else {
                        b_aps.push(b);
                    }
                }
                permute(a_aps,b_aps,&|a,b| {
                    let x = Clp::execute(pp,&Operation::DivideSigned(a.clone(),b.clone()));
                    let y = Clp::execute(pp,&Operation::Multiply(x,b.clone()));
                    Clp::execute(pp,&Operation::Subtract(a.clone(),y))
                })
            },
            Operation::ShiftRightSigned(ref a,ref b) => {
                if a.is_bottom() { return a.clone(); }
                if b.is_bottom() { return b.clone(); }
                
                let a_aps = Self::signed_progression(a);
                let b_aps = Self::unsigned_progression(a);

                permute(a_aps,b_aps,&|a,b| {
                    if a.cardinality == I::one() && b.cardinality == I::one() {
                        return Clp::<I>{
                            width: a.width,
                            base: a.base >> b.base,
                            stride: I::zero(),
                            cardinality: I::one(),
                        };
                    }

                    let base = if a.base >= I::zero() {
                        a.base >> b.last()
                    } else {
                        a.base >> b.base
                    };
                    let msk = (I::one() << b.last()) - I::one();
                    let d1 = a.stride & msk == I::zero();
                    let d2 = a.base & msk == I::zero();
                    let d3 = Clp::<I>::count_ones(a.base & msk) == b.last();
                    let stride = if (b.cardinality == I::one() && d1) || (d1 && d2) || (d1 && d3) {
                        gcd(a.stride >> b.last(),(a.base >> (b.last() - a.stride)) - (a.base >> b.last()))
                    } else {
                        I::one()
                    };
                    let cardinality = if a.base >= a.last() {
                        (((a.last() >> b.base) - base) / stride) + I::one()
                    } else {
                        (((a.last() >> b.last()) - base) / stride) + I::one()
                    };

                    Clp::<I>{
                        width: a.width,
                        base: base,
                        stride: stride,
                        cardinality: cardinality
                    }
                })
            },
            Operation::ShiftRightUnsigned(ref a,ref b) => {
                if a.is_bottom() { return a.clone(); }
                if b.is_bottom() { return b.clone(); }

                let a_aps = Self::unsigned_progression(a);
                let b_aps = Self::unsigned_progression(a);

                permute(a_aps,b_aps,&|a,b| {
                    if a.cardinality == I::one() && b.cardinality == I::one() {
                        return Clp::<I>{
                            width: a.width,
                            base: a.base >> b.base,
                            stride: I::zero(),
                            cardinality: I::one(),
                        };
                    }

                    let base = a.base >> b.last();
                    let msk = (I::one() << b.last()) - I::one();
                    let d1 = a.stride & msk == I::zero();
                    let d2 = a.base & msk == I::zero();
                    let d3 = Clp::<I>::count_ones(a.base & msk) == b.last();
                    let stride = if (b.cardinality == I::one() && d1) || (d1 && d2) || (d1 && d3) {
                        gcd(a.stride >> b.last(),(a.base >> (b.last() - a.stride)) - (a.base >> b.last()))
                    } else {
                        I::one()
                    };
                    let cardinality = (((a.last() >> b.base) - base) / stride) + I::one();

                    Clp::<I>{
                        width: a.width,
                        base: base,
                        stride: stride,
                        cardinality: cardinality
                    }
                })
            },
            Operation::ShiftLeft(ref a,ref b) => {
                if a.is_bottom() { return a.clone(); }
                if b.is_bottom() { return b.clone(); }
                
                let a_aps = vec![a.clone()];
                let b_aps = Self::unsigned_progression(a);

                permute(a_aps,b_aps,&|a,b| {
                    let base = a.base << b.base;
                    let stride = if b.cardinality == I::one() {
                        a.stride << b.base
                    } else {
                        gcd(a.base,a.stride)
                    };
                    let cardinality = (((a.last() << b.last()) - base) / stride) + I::one();

                    Clp::<I>{
                        width: a.width,
                        base: base,
                        stride: stride,
                        cardinality: cardinality
                    }
                })
            },

            Operation::LessOrEqualSigned(ref a,ref b) => {
                let x = Clp::execute(pp,&Operation::LessSigned(a.clone(),b.clone()));
                let y = Clp::execute(pp,&Operation::Equal(a.clone(),b.clone()));
                Clp::execute(pp,&Operation::InclusiveOr(x,y))
            },
            Operation::LessOrEqualUnsigned(ref a,ref b) => {
                let x = Clp::execute(pp,&Operation::LessUnsigned(a.clone(),b.clone()));
                let y = Clp::execute(pp,&Operation::Equal(a.clone(),b.clone()));
                Clp::execute(pp,&Operation::InclusiveOr(x,y))
            },
            //Operation::LessSigned(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::LessSigned(a,b))),
            //Operation::LessUnsigned(ref a,ref b) =>
            //    permute(a,b,&|a,b| execute(Operation::LessUnsigned(a,b))),
            Operation::Equal(ref a,ref b) => {
                if a.is_bottom() || b.is_bottom() {
                    Clp::<I>{
                        width: 1,
                        base: I::zero(),
                        stride: I::zero(),
                        cardinality: I::zero(),
                    }
                } else if a.cardinality == I::one() && b.cardinality == I::one() && a.base == b.base {
                    Clp::<I>{
                        width: 1,
                        base: I::one(),
                        stride: I::zero(),
                        cardinality: I::one(),
                    }
                } else if Clp::<I>::intersection(a,b).is_bottom() {
                    Clp::<I>{
                        width: 1,
                        base: I::zero(),
                        stride: I::zero(),
                        cardinality: I::one(),
                    }
                } else {
                    Clp::<I>{
                        width: b.width,
                        base: I::zero(),
                        stride: I::one(),
                        cardinality: Clp::<I>::mask(b.width),
                    }
                }
            },

            Operation::Move(ref a) => a.clone(),
            Operation::Call(ref a) => a.clone(),

            //Operation::ZeroExtend(ref sz,ref a) =>
            //    map(a,&|a| execute(Operation::ZeroExtend(*sz,a))),
            //Operation::SignExtend(ref sz,ref a) =>
            //    map(a,&|a| execute(Operation::SignExtend(*sz,a))),

            Operation::Load(ref r,ref a) => Clp::<I>{
                width: a.width,
                base: I::zero(),
                stride: I::one(),
                cardinality: Clp::<I>::mask(a.width),
            },
            Operation::Store(ref r,ref a) => a.clone(),

            Operation::Phi(ref v) => match v.len() {
                0 => unreachable!(),
                1 => v[0].clone(),
                _ => v.iter().skip(1).fold(v[0].clone(),|acc,x| {
                    Clp::<I>::union(&acc,x)
                }),
            },
            _ => unreachable!()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use {
        Statement,Operation,
        ControlFlowTarget,Function,ControlFlowGraph,
        Guard,
        Lvalue,Rvalue,
        Bound,Mnemonic,
        ssa_convertion,
        BasicBlock,
    };

    use graph_algos::{
        MutableGraphTrait,
    };
    use std::borrow::Cow;

    #[derive(Debug,Clone,PartialEq,Eq,Hash,RustcDecodable,RustcEncodable)]
    enum Sign {
        Join,
        Positive,
        Negative,
        Zero,
        Meet
    }

    impl Avalue for Sign {
        fn abstract_value(v: &Rvalue) -> Self {
            match v {
                &Rvalue::Constant{ value: c,.. } if c > 0 => Sign::Positive,
                &Rvalue::Constant{ value: 0,.. } => Sign::Zero,
                _ => Sign::Join,
            }
        }

        fn abstract_constraint(c: &Constraint) -> Self {
            match c {
                &Constraint::Equal(Rvalue::Constant{ value: 0,.. }) => Sign::Zero,
                &Constraint::LessUnsigned(Rvalue::Constant{ value: 1,.. }) => Sign::Zero,
                &Constraint::LessOrEqualUnsigned(Rvalue::Constant{ value: 0,.. }) => Sign::Zero,
                &Constraint::LessSigned(Rvalue::Constant{ value: 0,.. }) => Sign::Negative,
                &Constraint::LessOrEqualSigned(Rvalue::Constant{ value: v, size: s })
                    if s <= 64 && v & (1 << (s-1)) != 0 => Sign::Negative,
                &Constraint::LessSigned(Rvalue::Constant{ value: v, size: s })
                    if s <= 64 && v & (1 << (s-1)) != 0 => Sign::Negative,
                _ => Sign::Join,
            }
        }

        fn execute(_: &ProgramPoint, op: &Operation<Self>) -> Self {
            match op {
                &Operation::Add(Sign::Positive,Sign::Positive) => Sign::Positive,
                &Operation::Add(Sign::Positive,Sign::Zero) => Sign::Positive,
                &Operation::Add(Sign::Zero,Sign::Positive) => Sign::Positive,
                &Operation::Add(Sign::Negative,Sign::Negative) => Sign::Negative,
                &Operation::Add(Sign::Negative,Sign::Zero) => Sign::Negative,
                &Operation::Add(Sign::Zero,Sign::Negative) => Sign::Negative,
                &Operation::Add(Sign::Positive,Sign::Negative) => Sign::Join,
                &Operation::Add(Sign::Negative,Sign::Positive) => Sign::Join,
                &Operation::Add(_,Sign::Join) => Sign::Join,
                &Operation::Add(Sign::Join,_) => Sign::Join,
                &Operation::Add(ref a,Sign::Meet) => a.clone(),
                &Operation::Add(Sign::Meet,ref b) => b.clone(),

                &Operation::Subtract(Sign::Positive,Sign::Positive) => Sign::Join,
                &Operation::Subtract(Sign::Positive,Sign::Zero) => Sign::Positive,
                &Operation::Subtract(Sign::Zero,Sign::Positive) => Sign::Negative,
                &Operation::Subtract(Sign::Negative,Sign::Negative) => Sign::Join,
                &Operation::Subtract(Sign::Negative,Sign::Zero) => Sign::Negative,
                &Operation::Subtract(Sign::Zero,Sign::Negative) => Sign::Positive,
                &Operation::Subtract(Sign::Positive,Sign::Negative) => Sign::Positive,
                &Operation::Subtract(Sign::Negative,Sign::Positive) => Sign::Negative,
                &Operation::Subtract(_,Sign::Join) => Sign::Join,
                &Operation::Subtract(Sign::Join,_) => Sign::Join,
                &Operation::Subtract(ref a,Sign::Meet) => a.clone(),
                &Operation::Subtract(Sign::Meet,ref b) => b.clone(),

                &Operation::Multiply(Sign::Positive,Sign::Positive) => Sign::Positive,
                &Operation::Multiply(Sign::Negative,Sign::Negative) => Sign::Positive,
                &Operation::Multiply(Sign::Positive,Sign::Negative) => Sign::Negative,
                &Operation::Multiply(Sign::Negative,Sign::Positive) => Sign::Negative,
                &Operation::Multiply(_,Sign::Zero) => Sign::Zero,
                &Operation::Multiply(Sign::Zero,_) => Sign::Zero,
                &Operation::Multiply(_,Sign::Join) => Sign::Join,
                &Operation::Multiply(Sign::Join,_) => Sign::Join,
                &Operation::Multiply(ref a,Sign::Meet) => a.clone(),
                &Operation::Multiply(Sign::Meet,ref b) => b.clone(),

                &Operation::DivideSigned(Sign::Positive,Sign::Positive) => Sign::Positive,
                &Operation::DivideSigned(Sign::Negative,Sign::Negative) => Sign::Positive,
                &Operation::DivideSigned(Sign::Positive,Sign::Negative) => Sign::Negative,
                &Operation::DivideSigned(Sign::Negative,Sign::Positive) => Sign::Negative,
                &Operation::DivideSigned(_,Sign::Zero) => Sign::Zero,
                &Operation::DivideSigned(Sign::Zero,_) => Sign::Zero,
                &Operation::DivideSigned(_,Sign::Join) => Sign::Join,
                &Operation::DivideSigned(Sign::Join,_) => Sign::Join,
                &Operation::DivideSigned(ref a,Sign::Meet) => a.clone(),
                &Operation::DivideSigned(Sign::Meet,ref b) => b.clone(),

                &Operation::DivideUnsigned(Sign::Positive,Sign::Positive) => Sign::Positive,
                &Operation::DivideUnsigned(Sign::Negative,Sign::Negative) => Sign::Positive,
                &Operation::DivideUnsigned(Sign::Positive,Sign::Negative) => Sign::Negative,
                &Operation::DivideUnsigned(Sign::Negative,Sign::Positive) => Sign::Negative,
                &Operation::DivideUnsigned(_,Sign::Zero) => Sign::Zero,
                &Operation::DivideUnsigned(Sign::Zero,_) => Sign::Zero,
                &Operation::DivideUnsigned(_,Sign::Join) => Sign::Join,
                &Operation::DivideUnsigned(Sign::Join,_) => Sign::Join,
                &Operation::DivideUnsigned(ref a,Sign::Meet) => a.clone(),
                &Operation::DivideUnsigned(Sign::Meet,ref b) => b.clone(),

                &Operation::Modulo(Sign::Positive,Sign::Positive) => Sign::Positive,
                &Operation::Modulo(Sign::Negative,Sign::Negative) => Sign::Positive,
                &Operation::Modulo(Sign::Positive,Sign::Negative) => Sign::Negative,
                &Operation::Modulo(Sign::Negative,Sign::Positive) => Sign::Negative,
                &Operation::Modulo(_,Sign::Zero) => Sign::Zero,
                &Operation::Modulo(Sign::Zero,_) => Sign::Zero,
                &Operation::Modulo(_,Sign::Join) => Sign::Join,
                &Operation::Modulo(Sign::Join,_) => Sign::Join,
                &Operation::Modulo(ref a,Sign::Meet) => a.clone(),
                &Operation::Modulo(Sign::Meet,ref b) => b.clone(),

                &Operation::Move(ref a) => a.clone(),
                &Operation::ZeroExtend(_,Sign::Negative) => Sign::Join,
                &Operation::ZeroExtend(_,ref a) => a.clone(),
                &Operation::SignExtend(_,ref a) => a.clone(),

                &Operation::Phi(ref ops) => {
                    match ops.len() {
                        0 => unreachable!("Phi function w/o arguments"),
                        1 => ops[0].clone(),
                        _ => ops.iter().fold(Sign::Meet,|acc,x| acc.combine(&x))
                    }
                },

                _ => Sign::Join,
            }
        }

        fn narrow(&self, a: &Self) -> Self {
            match a {
                &Sign::Meet => Sign::Meet,
                &Sign::Join => self.clone(),
                &Sign::Positive | &Sign::Negative | &Sign::Zero => {
                    match self {
                        &Sign::Meet => Sign::Meet,
                        &Sign::Join => a.clone(),
                        a => if *a == *self {
                            a.clone()
                        } else {
                            Sign::Meet
                        },
                    }
                },
            }
        }

        fn combine(&self, b: &Self) -> Self {
            match (self,b) {
                (x,y) if x == y => x.clone(),
                (&Sign::Meet,x) => x.clone(),
                (x,&Sign::Meet) => x.clone(),
                _ => Sign::Join
            }
        }

        fn widen(&self, b: &Self) -> Self {
            if *b == *self {
                self.clone()
            } else {
                Sign::Join
            }
        }


        fn initial() -> Self {
            Sign::Meet
        }

        fn more_exact(&self, b: &Self) -> bool {
            self != b && match (self,b) {
                (&Sign::Meet,&Sign::Positive) | (&Sign::Meet,&Sign::Negative) | (&Sign::Meet,&Sign::Join) => false,
                (&Sign::Positive,&Sign::Join) | (&Sign::Negative,&Sign::Join) => false,
                _ => true
            }
        }

        fn extract(&self,size: usize,offset: usize) -> Self {
            match self {
                &Sign::Join => Sign::Join,
                &Sign::Meet => Sign::Meet,
                &Sign::Positive => Sign::Positive,
                &Sign::Negative => Sign::Negative,
                &Sign::Zero => Sign::Zero,
            }
        }
    }

    /*
     * x = 0;
     * n = 1;
     * while (n <= undef) {
     *  x = x + n;
     *  n = n + 1;
     * }
     */
    #[test]
    fn signedness_analysis() {
        let x_var = Lvalue::Variable{ name: Cow::Borrowed("x"), size: 32, subscript: None };
        let n_var = Lvalue::Variable{ name: Cow::Borrowed("n"), size: 32, subscript: None };
        let flag = Lvalue::Variable{ name: Cow::Borrowed("flag"), size: 1, subscript: None };
        let bb0 = BasicBlock::from_vec(vec![
                                       Mnemonic::new(0..1,"assign x".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(Rvalue::new_u64(0)), assignee: x_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(1..2,"assign n".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(Rvalue::new_u64(1)), assignee: n_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(2..3,"cmp n".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::LessOrEqualSigned(n_var.clone().into(),Rvalue::Undefined), assignee: flag.clone()}].iter()).ok().unwrap()]);
        let bb1 = BasicBlock::from_vec(vec![
                                       Mnemonic::new(3..4,"add x and n".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Add(x_var.clone().into(),n_var.clone().into()), assignee: x_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(4..5,"inc n".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Add(n_var.clone().into(),Rvalue::new_u64(1)), assignee: n_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(5..6,"cmp n".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::LessOrEqualSigned(n_var.clone().into(),Rvalue::Undefined), assignee: flag.clone()}].iter()).ok().unwrap()]);
        let bb2 = BasicBlock{ area: Bound::new(4,5), mnemonics: vec![] };
        let mut cfg = ControlFlowGraph::new();

        let g = Guard::from_flag(&flag.clone().into()).ok().unwrap();
        let v0 = cfg.add_vertex(ControlFlowTarget::Resolved(bb0));
        let v1 = cfg.add_vertex(ControlFlowTarget::Resolved(bb1));
        let v2 = cfg.add_vertex(ControlFlowTarget::Resolved(bb2));

        cfg.add_edge(g.negation(),v0,v2);
        cfg.add_edge(g.negation(),v1,v2);
        cfg.add_edge(g.clone(),v0,v1);
        cfg.add_edge(g.clone(),v1,v1);

        let mut func = Function::new("func".to_string(),"ram".to_string());

        func.cflow_graph = cfg;
        func.entry_point = Some(v0);

        ssa_convertion(&mut func);

        let vals = approximate::<Sign>(&func).ok().unwrap();
        let res = results::<Sign>(&func,&vals);

        assert_eq!(res[&(Cow::Borrowed("x"),32)],Sign::Join);
        assert_eq!(res[&(Cow::Borrowed("n"),32)],Sign::Positive);
    }

    /*
     * a = -256
     * b = 1
     * while(a <= 0) {
     *   a = a + 1
     *   b = a * 2
     * }
     * f(a)
     * f(b)
     */
    #[test]
    fn signedness_narrow() {
        let a_var = Lvalue::Variable{ name: Cow::Borrowed("a"), size: 32, subscript: None };
        let b_var = Lvalue::Variable{ name: Cow::Borrowed("b"), size: 32, subscript: None };
        let flag = Lvalue::Variable{ name: Cow::Borrowed("flag"), size: 1, subscript: None };
        let bb0 = BasicBlock::from_vec(vec![
                                       Mnemonic::new(0..1,"assign a".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(Rvalue::new_u64(0xffffffffffffff00)), assignee: a_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(1..2,"assign b".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(Rvalue::new_u64(1)), assignee: b_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(2..3,"cmp a".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::LessOrEqualSigned(a_var.clone().into(),Rvalue::new_u64(0)), assignee: flag.clone()}].iter()).ok().unwrap()]);
        let bb1 = BasicBlock::from_vec(vec![
                                       Mnemonic::new(3..4,"inc a".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Add(a_var.clone().into(),Rvalue::new_u64(1)), assignee: a_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(4..5,"mul a".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Multiply(a_var.clone().into(),Rvalue::new_u64(2)), assignee: b_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(5..6,"cmp a".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::LessOrEqualSigned(a_var.clone().into(),Rvalue::new_u64(0)), assignee: flag.clone()}].iter()).ok().unwrap()]);
        let bb2 = BasicBlock::from_vec(vec![
                                       Mnemonic::new(6..7,"use a".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(a_var.clone().into()), assignee: a_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(7..8,"use b".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(b_var.clone().into()), assignee: b_var.clone()}].iter()).ok().unwrap()]);
        let mut cfg = ControlFlowGraph::new();
        let v0 = cfg.add_vertex(ControlFlowTarget::Resolved(bb0));
        let v1 = cfg.add_vertex(ControlFlowTarget::Resolved(bb1));
        let v2 = cfg.add_vertex(ControlFlowTarget::Resolved(bb2));

        let g = Guard::from_flag(&flag.clone().into()).ok().unwrap();

        cfg.add_edge(g.negation(),v0,v2);
        cfg.add_edge(g.negation(),v1,v2);
        cfg.add_edge(g.clone(),v0,v1);
        cfg.add_edge(g.clone(),v1,v1);

        let mut func = Function::new("func".to_string(),"ram".to_string());

        func.cflow_graph = cfg;
        func.entry_point = Some(v0);

        ssa_convertion(&mut func);

        let vals = approximate::<Sign>(&func).ok().unwrap();
        let res = results::<Sign>(&func,&vals);

        println!("vals: {:?}",vals);
        println!("res: {:?}",res);

        assert_eq!(res.get(&(Cow::Borrowed("a"),32)),Some(&Sign::Positive));
        assert_eq!(res.get(&(Cow::Borrowed("b"),32)),Some(&Sign::Positive));
    }

    /*
     * a = 10
     * b = 0
     * c = 4
     * if (c == 1) {
     *   a += 5;
     *   b = a * c;
     *   c = 2
     * } else {
     *   while(a > 0) {
     *     a -= 1
     *     b += 3
     *     c = 3
     *   }
     * }
     * x = a + b;
     */
    #[test]
    fn kset_test() {
        let a_var = Lvalue::Variable{ name: Cow::Borrowed("a"), size: 32, subscript: None };
        let b_var = Lvalue::Variable{ name: Cow::Borrowed("b"), size: 32, subscript: None };
        let c_var = Lvalue::Variable{ name: Cow::Borrowed("c"), size: 32, subscript: None };
        let x_var = Lvalue::Variable{ name: Cow::Borrowed("x"), size: 32, subscript: None };
        let flag = Lvalue::Variable{ name: Cow::Borrowed("flag"), size: 1, subscript: None };
        let bb0 = BasicBlock::from_vec(vec![
                                       Mnemonic::new(0..1,"assign a".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(Rvalue::new_u32(10)), assignee: a_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(1..2,"assign b".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(Rvalue::new_u32(0)), assignee: b_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(2..3,"assign c".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(Rvalue::new_u32(4)), assignee: c_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(3..4,"cmp c".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Equal(c_var.clone().into(),Rvalue::new_u32(1)), assignee: flag.clone()}].iter()).ok().unwrap()]);

        let bb1 = BasicBlock::from_vec(vec![
                                       Mnemonic::new(4..5,"add a and 5".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Add(a_var.clone().into(),Rvalue::new_u32(5)), assignee: a_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(5..6,"mul a and c".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Add(a_var.clone().into(),c_var.clone().into()), assignee: b_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(6..7,"assign c".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(Rvalue::new_u32(2)), assignee: c_var.clone()}].iter()).ok().unwrap()]);
        let bb2 = BasicBlock::from_vec(vec![
                                       Mnemonic::new(7..8,"dec a".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Subtract(a_var.clone().into(),Rvalue::new_u32(1)), assignee: a_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(8..9,"add 3 to b".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Add(b_var.clone().into(),Rvalue::new_u32(3)), assignee: b_var.clone()}].iter()).ok().unwrap(),
                                       Mnemonic::new(9..10,"assign c".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Move(Rvalue::new_u32(3)), assignee: c_var.clone()}].iter()).ok().unwrap()]);
        let bb3 = BasicBlock::from_vec(vec![
                                       Mnemonic::new(10..11,"add a and b".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::Add(a_var.clone().into(),b_var.clone().into()), assignee: x_var.clone()}].iter()).ok().unwrap()]);
        let bb4 = BasicBlock::from_vec(vec![
                                       Mnemonic::new(11..12,"cmp a".to_string(),"".to_string(),vec![].iter(),vec![
                                                     Statement{ op: Operation::LessOrEqualSigned(a_var.clone().into(),Rvalue::new_u32(0)), assignee: flag.clone()}].iter()).ok().unwrap()]);


        let mut cfg = ControlFlowGraph::new();

        let v0 = cfg.add_vertex(ControlFlowTarget::Resolved(bb0));
        let v1 = cfg.add_vertex(ControlFlowTarget::Resolved(bb1));
        let v2 = cfg.add_vertex(ControlFlowTarget::Resolved(bb2));
        let v3 = cfg.add_vertex(ControlFlowTarget::Resolved(bb3));
        let v4 = cfg.add_vertex(ControlFlowTarget::Resolved(bb4));

        let g = Guard::from_flag(&flag.into()).ok().unwrap();

        cfg.add_edge(g.clone(),v0,v1);
        cfg.add_edge(g.negation(),v0,v4);
        cfg.add_edge(g.negation(),v4,v2);
        cfg.add_edge(g.clone(),v4,v3);
        cfg.add_edge(Guard::always(),v2,v4);
        cfg.add_edge(Guard::always(),v1,v3);

        let mut func = Function::new("func".to_string(),"ram".to_string());

        func.cflow_graph = cfg;
        func.entry_point = Some(v0);

        ssa_convertion(&mut func);

        let vals = approximate::<Kset>(&func).ok().unwrap();
        let res = results::<Kset>(&func,&vals);

        assert_eq!(res[&(Cow::Borrowed("a"),32)],Kset::Join);
        assert_eq!(res[&(Cow::Borrowed("b"),32)],Kset::Join);
        assert_eq!(res[&(Cow::Borrowed("c"),32)],Kset::Set(vec![(2,32),(3,32),(4,32)]));
        assert_eq!(res[&(Cow::Borrowed("x"),32)],Kset::Join);
    }

    #[test]
    fn bit_extract() {
        let p_var = Lvalue::Variable{ name: Cow::Borrowed("p"), size: 22, subscript: None };
        let r1_var = Lvalue::Variable{ name: Cow::Borrowed("r1"), size: 8, subscript: None };
        let r2_var = Lvalue::Variable{ name: Cow::Borrowed("r2"), size: 8, subscript: None };
        let next = Lvalue::Variable{ name: Cow::Borrowed("R30:R31"), size: 22, subscript: None };
        let bb0 = BasicBlock::from_vec(vec![
            Mnemonic::new(0..1,"init r1".to_string(),"".to_string(),vec![].iter(),vec![
                Statement{ op: Operation::Move(Rvalue::new_u8(7)), assignee: r1_var.clone()}].iter()).ok().unwrap(),
            Mnemonic::new(1..2,"init r2".to_string(),"".to_string(),vec![].iter(),vec![
                Statement{ op: Operation::Move(Rvalue::new_u8(88)), assignee: r2_var.clone()}].iter()).ok().unwrap()
        ]);
        let bb1 = BasicBlock::from_vec(vec![
            Mnemonic::new(2..3,"zext r1".to_string(),"".to_string(),vec![].iter(),vec![
                Statement{ op: Operation::ZeroExtend(22,r1_var.clone().into()), assignee: p_var.clone()}].iter()).ok().unwrap(),
            Mnemonic::new(3..4,"mov r2".to_string(),"".to_string(),vec![].iter(),vec![
                Statement{ op: Operation::Select(8,p_var.clone().into(),r2_var.clone().into()), assignee: p_var.clone()}].iter()).ok().unwrap(),
            Mnemonic::new(4..5,"mov 0".to_string(),"".to_string(),vec![].iter(),vec![
                Statement{ op: Operation::Select(16,p_var.clone().into(),Rvalue::Constant{ value: 0, size: 6 }), assignee: p_var.clone()}].iter()).ok().unwrap(),
            Mnemonic::new(5..6,"mov next".to_string(),"".to_string(),vec![].iter(),vec![
                Statement{ op: Operation::Move(p_var.clone().into()), assignee: next.clone()}].iter()).ok().unwrap()
        ]);
        let mut cfg = ControlFlowGraph::new();
        let v0 = cfg.add_vertex(ControlFlowTarget::Resolved(bb0));
        let v1 = cfg.add_vertex(ControlFlowTarget::Resolved(bb1));

        cfg.add_edge(Guard::always(),v0,v1);

        let mut func = Function::new("func".to_string(),"ram".to_string());

        func.cflow_graph = cfg;
        func.entry_point = Some(v0);

        ssa_convertion(&mut func);

        let vals = approximate::<Kset>(&func).ok().unwrap();

        for i in vals {
            println!("{:?}",i);
        }
    }

    #[test]
 /*   fn ext_strided_interval() {

        {
            let a = ExtStridedInterval::Interval{
                stride: 4, first: 0x7ff0, last: 0x7ffc, size: 16 };
            let b = ExtStridedInterval::Interval{
                stride: 0, first: 4, last: 4, size: 16 };
            let res = ExtStridedInterval::execute(&Operation::Add(a,b));
            let exp = ExtStridedInterval::Interval{
                stride: 4, first: 0x7ff4, last: 0x8000, size: 16 };

            assert_eq!(res, exp);
        }

        {
            let a = ExtStridedInterval::Interval{
                stride: 1, first: 10, last: 20, size: 16 };
            let b = ExtStridedInterval::Interval{
                stride: 1, first: 0xfffffffffffffffe, last: 2, size: 64 };
            let exp = vec![
                ExtStridedInterval::Interval{
                    stride: 1, first: 0, last: 2, size: 64 },
                ExtStridedInterval::Interval{
                    stride: 1, first: 0xfffffffffffffffe, last: 0xffffffffffffffff, size: 64 }
            ];

            assert_eq!(a.dsi(), vec![a]);
            assert_eq!(b.dsi(), exp);
        }
    }*/

    #[test]
    fn circular_linear_progression() {
        // eea
        {
            let (a,b) = Clp::<i64>::eea(&99,&78);
            assert_eq!(a, 3);
            assert_eq!(b, -11);

            let (a,b) = Clp::<i64>::eea(&78,&99);
            assert_eq!(a, 3);
            assert_eq!(b, 14);
        }

        // canonize
        {
            let a = Clp::<i64>{ width: 8, base: 216, stride: 48, cardinality: 19 };
            let c = Clp::<i64>{ width: 8, base: 8, stride: 16, cardinality: 16 };

            assert_eq!(c, Clp::canonize(&a));
            Clp::canonize(&Clp::<i64>{ width: 64, base: 216, stride: 48, cardinality: 19 });
        }

        {
            let a = Clp::<i64>{ width: 8, base: 216, stride: 48, cardinality: 15 };
            let c = Clp::<i64>{ width: 8, base: 184, stride: 16, cardinality: 15 };

            assert_eq!(c, Clp::canonize(&a));
            Clp::canonize(&Clp::<i64>{ width: 64, base: 216, stride: 48, cardinality: 15 });
        }

        {
            let a = Clp::<i64>{ width: 8, base: 90, stride: 132, cardinality: 7 };
            let c = Clp::<i64>{ width: 8, base: 114, stride: 124, cardinality: 7 };

            assert_eq!(c, Clp::canonize(&a));
            Clp::canonize(&Clp::<i64>{ width: 64, base: 90, stride: 132, cardinality: 7 });
        }

        // unsigned union
        {
            let c = Clp::<i64>{ width: 8, base: 60, stride: 30, cardinality: 10 };
            let u1 = Clp::<i64>{ width: 8, base: 60, stride: 30, cardinality: 7 };
            let u2 = Clp::<i64>{ width: 8, base: 14, stride: 30, cardinality: 3 };

            assert_eq!(c, Clp::union(&u1,&u2));
        }

        // signed union
        {
            let c = Clp{ width: 8, base: 60, stride: 30, cardinality: 10 };
            let u1 = Clp{ width: 8, base: 60, stride: 30, cardinality: 3 };
            let u2 = Clp{ width: 8, base: -106, stride: 30, cardinality: 7 };

            assert_eq!(c, Clp::union(&u1,&u2));
        }

        // unsigned AP
        {
            let c = Clp::<i64>{ width: 8, base: 60, stride: 30, cardinality: 10 };
            let ap = Clp::unsigned_progression(&c);
            let u1 = Clp::<i64>{ width: 8, base: 60, stride: 30, cardinality: 7 };
            let u2 = Clp::<i64>{ width: 8, base: 14, stride: 30, cardinality: 3 };

            assert_eq!(ap.len(), 2);
            assert!(ap[0] == u1 || ap[0] == u2);
            assert!(ap[1] == u1 || ap[1] == u2);
            assert!(ap[0] != ap[1]);

            assert_eq!(c, Clp::union(&u1,&u2));
        }

        // signed AP
        {
            let c = Clp::<i64>{ width: 8, base: 60, stride: 30, cardinality: 10 };
            let ap = Clp::signed_progression(&c);
            let u1 = Clp::<i64>{ width: 8, base: 60, stride: 30, cardinality: 3 };
            let u2 = Clp::<i64>{ width: 8, base: -106, stride: 30, cardinality: 7 };

            assert_eq!(ap.len(), 2);
            assert!(ap[0] == u1 || ap[0] == u2);
            assert!(ap[1] == u1 || ap[1] == u2);
            assert!(ap[0] != ap[1]);

            assert_eq!(c, Clp::union(&u1,&u2));
        }
    }
}
