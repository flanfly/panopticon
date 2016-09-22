/*
 * Panopticon - A libre disassembler
 * Copyright (C) 2014,2015,2016 Panopticon Authors
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

//! Abstract Interpretation Framework.
//!
//! Abstract Interpretation executes an program over sets of concrete values. Each operation is
//! extended to work on some kind of abstract value called abstract domain that approximates a
//! set of concrete values (called the concrete domain). A simple example is the domain of signs.
//! Each value can either be positive, negative, both or none. An abstract interpretation will first
//! replace all constant values with their signs and then execute all basic blocks using the
//! abstract sign domain. For example multiplying two positive values yields a positive value.
//! Adding a positive and a negative sign yields an abstract value representing both signs (called
//! join).

pub mod bounded_addr_track;
pub mod kset;

use std::hash::Hash;
use std::fmt::Debug;
use std::collections::{HashSet,HashMap};
use std::iter::FromIterator;
use std::borrow::Cow;
use std::cmp;
use std::num::Wrapping;
use num::{Integer,Unsigned,Signed,abs,FromPrimitive};
use num::integer::{lcm,gcd};
use std::result;

use graph_algos::{
    GraphTrait,
    IncidenceGraphTrait,
    VertexListGraphTrait,
    BidirectionalGraphTrait,
};
use rustc_serialize::{
    Encodable,Decodable,
    Decoder,Encoder
};
use graph_algos::dominator::{
    immediate_dominator,
};
use graph_algos::order::{
    weak_topo_order,
    HierarchicalOrdering,
};

use {
    Lvalue,Rvalue,
    Statement,Operation,
    ControlFlowTarget,
    ControlFlowRef,
    ControlFlowGraph,
    Function,
    Guard,
    lift,
    Result,
    flag_operations,
};

/// Linear constraint.
pub enum Constraint {
    /// True if equal to.
    Equal(Rvalue),
    /// True if less than (unsigned).
    LessUnsigned(Rvalue),
    /// True if less than or equal to (unsigned).
    LessOrEqualUnsigned(Rvalue),
    /// True if less than (signed).
    LessSigned(Rvalue),
    /// True if less than or equal to (signed).
    LessOrEqualSigned(Rvalue),
}

/// A program point is a unique RREIL instruction inside a function.
#[derive(Debug,PartialEq,Eq,Clone,RustcDecodable,RustcEncodable,PartialOrd,Ord,Hash)]
pub struct ProgramPoint {
    address: u64,
    position: usize,
}

/// Abstract Domain. Models both under- and over-approximation.
pub trait Avalue: Clone + PartialEq + Eq + Hash + Debug + Encodable + Decodable {
    /// Alpha function. Returns domain element that approximates the concrete value the best
    fn abstract_value(&Rvalue) -> Self;
    /// Alpha function. Returns domain element that approximates the concrete value that fullfil
    /// the constraint the best.
    fn abstract_constraint(&Constraint) -> Self;
    /// Execute the abstract version of the operation, yielding the result.
    fn execute(&ProgramPoint,&Operation<Self>) -> Self;
    /// Narrows `self` with the argument.
    fn narrow(&self,&Self) -> Self;
    /// Widens `self` with the argument.
    fn widen(&self,other: &Self) -> Self;
    /// Computes the lowest upper bound of self and the argument.
    fn combine(&self,&Self) -> Self;
    /// Returns true if `other` <= `self`.
    fn more_exact(&self,other: &Self) -> bool;
    /// Returns the meet of the domain
    fn initial() -> Self;
    /// Mimics the Select operation.
    fn extract(&self,size: usize,offset: usize) -> Self;
}

/// Does an abstract interpretation of `func` using the abstract domain `A`. The function uses a
/// fixed point iteration and the widening strategy outlined in
/// Bourdoncle: "Efficient chaotic iteration strategies with widenings".
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

/// Given a function and an abstract interpretation result this functions returns that variable
/// names and abstract values that live after the function returns.
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

const KSET_MAXIMAL_CARDINALITY: usize = 10000;

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
                            match f(x.clone(),y) {
                                Rvalue::Constant{ value, size } => {
                                    ret.insert((value,size));
                                    if ret.len() > KSET_MAXIMAL_CARDINALITY {
                                        return Kset::Join;
                                    }
                                }
                                Rvalue::Undefined => return Kset::Join,
                                _ => {}
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
                let mut s = HashSet::<(u64,usize)>::new();
                
                for &(a,_as) in a.iter() {
                    match f(Rvalue::Constant{ value: a, size: _as }) {
                        Rvalue::Constant{ value, size } => { s.insert((value,size)); }
                        Rvalue::Undefined => return Kset::Join,
                        _ => {}
                    }
                }

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
                permute(a,b,&|a,b| {
                    let x = execute(Operation::DivideSigned(a.clone(),b.clone()));
                    println!("{:?} / {:?} = {:?}",a,b,x);
                    x
                }),
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

/// Mihaila et.al. Widening Point inferring cofibered domain. This domain is parameterized with a
/// child domain.
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

// Linus Kaellberg: "Circular Linear Progressions in SWEET"
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub struct Clp {
    pub width: usize,
    pub base: Wrapping<i64>,
    pub stride: Wrapping<i64>,
    pub cardinality: Wrapping<i64>,
}

impl Decodable for Clp {
    fn decode<D: Decoder>(d: &mut D) -> result::Result<Clp, D::Error> {
        d.read_struct("Clp", 4, |d| {
            Ok(Clp{
                width: try!(d.read_struct_field("width", 0, |d| { d.read_usize() })),
                base: Wrapping(try!(d.read_struct_field("base", 1, |d| { d.read_i64() }))),
                stride: Wrapping(try!(d.read_struct_field("stride", 2, |d| { d.read_i64() }))),
                cardinality: Wrapping(try!(d.read_struct_field("cardinality", 3, |d| { d.read_i64() }))),
            })
        })
    }
}

impl Encodable for Clp {
    fn encode<S: Encoder>(&self, s: &mut S) -> result::Result<(), S::Error> {
        s.emit_struct("Clp", 4, |s| {
            try!(s.emit_struct_field("width", 0, |s| {
                s.emit_usize(self.width)
            }));
            try!(s.emit_struct_field("base", 1, |s| {
                s.emit_i64(self.base.0)
            }));
            try!(s.emit_struct_field("stride", 2, |s| {
                s.emit_i64(self.stride.0)
            }));
            try!(s.emit_struct_field("cardinality", 3, |s| {
                s.emit_i64(self.cardinality.0)
            }));
            Ok(())
        })
    }
}

impl Clp {
    /// Computes the gcd of a and b, and the Bezout coeffcient of a
    fn eea(a: &Wrapping<i64>,b: &Wrapping<i64>) -> (Wrapping<i64>,Wrapping<i64>) {
        let mut s = Wrapping(0i64);
        let mut prev_s = Wrapping(1i64);
        let mut r = b.clone();
        let mut prev_r = a.clone();

        while r != Wrapping(0i64) {
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

    fn count_ones(mut a: Wrapping<i64>) -> Wrapping<i64> {
        let mut ret = Wrapping(0i64);

        while a != Wrapping(0i64) {
            if a & Wrapping(1i64) == Wrapping(1i64) {
                ret = ret + Wrapping(1i64);
            }
            a = a >> 1;
        }

        ret
    }

    fn trailing_zeros(_a: &Wrapping<i64>) -> isize {
        let mut ret = 0;
        let mut a = _a.clone();

        if a == Wrapping(0i64) { unreachable!() }

        while a & Wrapping(1i64) == Wrapping(0i64) {
            ret += 1;
            a = a >> 1;
        }

        ret
    }

    fn most_significant_bit(_a: &Wrapping<i64>) -> isize {
        let mut ret = 0;
        let mut a = _a.clone();

        if a == Wrapping(0i64) { unreachable!() }

        while a != Wrapping(0i64) {
            ret += 1;
            a = a >> 1;
        }

        ret
    }

    pub fn is_bottom(&self) -> bool {
        self.cardinality == Wrapping(0i64)
    }

    pub fn is_top(&self) -> bool {
        let c = cmp::max(Wrapping(0i64),self.cardinality);
        c <= Self::mask(self.width) && self.stride.0.is_odd()
    }

    pub fn last(&self) -> Wrapping<i64> {
        if self.cardinality <= Wrapping(0i64) {
            unreachable!()
        } else {
            self.base + self.stride * (self.cardinality - Wrapping(1))
        }
    }

    // Arithmetic negation
    fn minus(a: &Clp) -> Clp {
        if a.is_bottom() {
            a.clone()
        } else {
            Clp{
                width: a.width,
                base: (Wrapping(0i64) - Wrapping(1i64)) * a.last(),
                stride: a.stride,
                cardinality: a.cardinality
            }
        }
    }

    // Logic (bitwise) negation
    fn negate(a: &Clp) -> Clp {
        if a.is_bottom() {
            a.clone()
        } else {
            Clp{
                width: a.width,
                base: a.last() ^ Self::mask(a.width),
                stride: a.stride,
                cardinality: a.cardinality
            }
        }
    }

    fn mask(w: usize) -> Wrapping<i64> {
        let mut ret = Wrapping(1i64);

        for _ in 1..w {
            ret = ret << 1;
            ret = ret | Wrapping(1i64);
        }

        ret
    }

    fn modulus(a: Wrapping<i64>, m: Wrapping<i64>) -> Wrapping<i64> {
        ((a % m) + m) % m
    }

    pub fn closest_element(c_: &Clp, l: &Wrapping<i64>) -> (Wrapping<i64>,Wrapping<i64>,Wrapping<i64>,Wrapping<i64>,Wrapping<i64>,Wrapping<i64>) {
        let c = Self::canonize(c_);
        let modu = Self::mask(c.width) + Wrapping(1);

        if c.cardinality == Wrapping(1i64) {
            let z = Wrapping(0i64);
            return (z,z,z,modu,modu,Self::modulus(c.base - *l,modu));
        }

        let mut ia = Wrapping(1i64);
        let mut ib = Wrapping(1i64);
        let mut alpha = c.stride;
        let mut beta = modu - c.stride;
        let (mut ic,mut gamma) = if Self::modulus(c.base - *l,modu) < Self::modulus(c.base + c.stride - *l,modu) {
            (Wrapping(0i64),Self::modulus(c.base - *l,modu))
        } else {
            (Wrapping(1i64),Self::modulus(c.base + c.stride - *l,modu))
        };

        while ia + ib < c.cardinality {
            assert!(gamma.0 <= cmp::min(alpha.0,beta.0));

            if alpha < beta {
                assert!(gamma < beta);

                let kk = {
                    let t = -gamma - beta;
                    if t % alpha == Wrapping(0i64) {
                        t / alpha
                    } else {
                        t / alpha + Wrapping(1i64)
                    }
                };

                if kk <= (c.cardinality - Wrapping(1i64) - (ic + ib)) / ia && -beta + kk * alpha < Wrapping(0i64) {
                    ic = ic + ib + kk * ia;
                    gamma = gamma - beta + kk * alpha;

                    assert!(gamma.0 >= 0);
                }

                let k = cmp::min((beta - Wrapping(1i64)) / alpha,(c.cardinality - Wrapping(1i64) - ib) / ia);
                ib = ib + k * ia;
                beta = beta - k * alpha;
            } else {
                let kk = cmp::min(gamma / beta,(c.cardinality - Wrapping(1i64) - ic) / ib);
                ic = ic + kk * ib;
                gamma = gamma - kk * beta;
                let k = cmp::min((alpha - Wrapping(1i64)) / beta,(c.cardinality - Wrapping(1i64) - ia) / ib);
                ia = ia + k * ib;
                alpha = alpha - k * beta;
            }
        }

        println!("Algorithm2(c = {:?}, l = {}): ia = {:?}, ib = {:?}, ic = {:?}, alpha = {:?}, beta = {:?}, gamma = {:?}",c,l,ia,ib,ic,alpha,beta,gamma);
        assert!(alpha + beta > gamma && gamma >= Wrapping(0));
        assert!(ia.0 >= 0 && ia < c.cardinality);
        assert!(ib.0 >= 0 && ib < c.cardinality);
        assert!(ic.0 >= 0 && ic < c.cardinality);

        (ia,ib,ic,alpha,beta,gamma)
    }

    fn unsigned_minmax(a: &Clp) -> (Wrapping<i64>,Wrapping<i64>) {
        let (ia,ib,min_idx,_,_,_) = Self::closest_element(a,&Wrapping(0i64));
        let modu = Self::mask(a.width) + Wrapping(1);
        fn pred(i: Wrapping<i64>,ia: Wrapping<i64>, ib: Wrapping<i64>, n: Wrapping<i64>) -> Wrapping<i64>{
            if i < n - ib {
                i + ib
            } else if n - ib <= i && i < ia {
                i - ia + ib
            } else {
                assert!(ia <= i);
                i - ia
            }
        }
        let max_idx = pred(min_idx,ia,ib,a.cardinality);

        assert!(min_idx < a.cardinality);
        assert!(max_idx < a.cardinality);

        (Self::modulus(a.base + min_idx * a.stride,modu),
         Self::modulus(a.base + max_idx * a.stride,modu))
    }

    fn signed_minmax(a: &Clp) -> (Wrapping<i64>,Wrapping<i64>) {
        let l = -(Wrapping(1i64) << (a.width - 2));
        let (_,_,min_idx,_,_,_) = Self::closest_element(&a,&l);
        let msk = Self::mask(a.width);
        let half_msk = msk >> 1;
        let min = (a.base + min_idx * a.stride) & msk;
        let max = (a.base + Self::modulus(min_idx - Wrapping(1i64),a.cardinality) * a.stride) & msk;

        (if min <= half_msk { min } else { min - msk },
         if max <= half_msk { max } else { max - msk })
    }

    fn intersection(a: &Clp, b: &Clp) -> Clp {
        if a.is_bottom() { return a.clone() }
        if b.is_bottom() { return b.clone() }

        let (d,s) = Self::eea(&a.stride,&(Self::mask(a.width) + Wrapping(1i64)));
        let (e,t) = Self::eea(&b.stride,&d);
        let j0 = Self::modulus(t * (a.base - b.base) / e,d / e);
        let i = Clp{
            width: a.width - cmp::max(2,Self::most_significant_bit(&d)) as usize - 1,
            base: s * (b.base - a.base * b.stride * j0) / d,
            stride: b.stride * s / e,
            cardinality: (b.cardinality - j0) / (d / e),
        };
        let (i0,i1) = Self::unsigned_minmax(&i);
        
        if e % (a.base - b.base) != Wrapping(0i64) ||
           j0 >= b.cardinality ||
           i0 >= a.cardinality {
            Clp{
                width: a.width,
                base: Wrapping(0i64),
                stride: Wrapping(0i64),
                cardinality: Wrapping(0i64),
            }
        } else {
            let (_,_,_,alpha,beta,_) = Self::closest_element(&i,&i.base);
            let stride = a.stride * Wrapping(gcd(gcd(alpha.0,beta.0),(alpha + beta).0));
            
            Clp{
                width: a.width,
                base: a.base + a.stride * i0,
                stride: stride,
                cardinality: ((a.base + a.stride * i1) / stride) + Wrapping(1i64),
            }
        }
    }

    fn progression(_a: &Clp, split_pnt: Wrapping<i64>, signed: bool) -> Vec<Clp> {
        let a = Self::canonize(_a);
        let mask = Self::mask(a.width);
        let modul = mask + Wrapping(1);
        let half_modul = modul >> 1;
        let mut ret = vec![];

        println!("canon: {:?}",a);

        if a.cardinality > Wrapping(0) {
            let mut stride = if a.stride != Wrapping(0) { a.stride } else { Wrapping(1) };
            let mut cur = Wrapping(0);

            if stride < Wrapping(0) && !signed {
                stride = stride & mask;
            }

            while cur < a.cardinality {
                let mut base = a.base + cur * a.stride;

                if signed && (base & half_modul) != Wrapping(0) {
                    base = (base - modul) % modul;
                } else {
                    base = base & mask;
                }

                let len = ((split_pnt - base) & mask) / stride + Wrapping(1);
                
                println!("cur: {:?}, len: {:?}, base: {:?}, rest: {:?}",cur,len,base,a.cardinality - cur);

                ret.push(Clp{
                    width: a.width,
                    base: base,
                    stride: a.stride,
                    cardinality: cmp::min(len,a.cardinality - cur),
                });

                cur += len;
            }
        } else {
            if signed {
                ret.push(a);
            } else {
                ret.push(Clp{
                    width: a.width,
                    base: a.base & mask,
                    stride: a.stride,
                    cardinality: a.cardinality,
                })
            }
        }

        return ret;
    }

    pub fn unsigned_progression(a: &Clp) -> Vec<Clp> {
        let split_pnt = Self::mask(a.width);
        Self::progression(a,split_pnt,false)
    }

    pub fn signed_progression(a: &Clp) -> Vec<Clp> {
        let span = Self::mask(a.width);
        Self::progression(a,span >> 1,true)
    }
    
    pub fn union(_a: &Clp, _b: &Clp) -> Clp {
        assert_eq!(_a.width, _b.width);

        let a = Clp::canonize(_a);
        let b = Clp::canonize(_b);

        if a.is_bottom() { return b; } else if b.is_bottom() { return a; }

        if a.cardinality == Wrapping(1) && b.cardinality == Wrapping(1) {
            return Clp{
                width: a.width,
                base: cmp::min(a.base,b.base),
                stride: Wrapping(abs((a.base - b.base).0)),
                cardinality: Wrapping(2),
            };
        }

        fn _union(a: &Clp, b: &Clp) -> Clp {
            let ca = cmp::max(Wrapping(0),a.cardinality);
            let cb = cmp::max(Wrapping(0),b.cardinality);
            let la = a.base + a.stride * (ca - Wrapping(1));
            let lb = b.base + b.stride * (cb - Wrapping(1));
            let base = cmp::min(a.base,b.base);
            let t1 = cmp::max(la,lb);
            let s = Wrapping(gcd(gcd(a.stride.0,b.stride.0),abs((a.base - b.base).0)));
            let cardinality = if s != Wrapping(0) {
                cmp::max(Wrapping(0),(((t1 - base) / s) + Wrapping(1)))
            } else {
                Wrapping(1)
            };

            Clp{
                width: a.width,
                base: base,
                stride: s,
                cardinality: cardinality,
            }
        }

        let w = Self::mask(a.width) + Wrapping(1);
        let mut ret: Option<Clp> = None;
        let mut m = Wrapping(-1);
        for _ in -1..2 {
            let x = _union(&a,&Clp{
                width: b.width,
                base: b.base + w * m,
                stride: b.stride,
                cardinality: b.cardinality
            });

            if ret.is_none() || ret.as_ref().unwrap().cardinality > x.cardinality {
                ret = Some(x)
            }

            m = m + Wrapping(1);
        }

        ret.unwrap()
    }

    pub fn canonize(a: &Clp) -> Clp {
        let msk = Self::mask(a.width);
        let w = msk + Wrapping(1i64);
        match a {
            &Clp{ width, cardinality: ref c,.. } if *c == Wrapping(0i64) =>
                Clp{
                    width: width,
                    base: Wrapping(0i64),
                    stride: Wrapping(0i64),
                    cardinality: Wrapping(0i64),
                },
            &Clp{ width,ref base, cardinality: ref c,.. } if *c == Wrapping(1i64) =>
                Clp{
                    width: width,
                    base: *base & msk,
                    stride: Wrapping(0i64),
                    cardinality: Wrapping(1i64),
                },
            &Clp{ width, base, stride, cardinality } => {
                let k = if stride == Wrapping(0i64) { Wrapping(1i64) } else { Wrapping(lcm(w.0,stride.0)) / stride };
                let c = cmp::max(Wrapping(0i64),cardinality);

                if c >= k && k >= Wrapping(2i64) {
                    let s = Wrapping(gcd(stride.0,w.0)) & msk;

                    Clp{
                        width: width,
                        base: Self::modulus(base,s),
                        stride: s,
                        cardinality: cmp::max(Wrapping(0i64),k),
                    }
                } else if c == k - Wrapping(1i64) && c >= Wrapping(2i64) {
                    let s = Wrapping(gcd(stride.0,w.0)) & msk;

                    Clp{
                        width: width,
                        base: (base + (c * stride) + s) & msk,
                        stride: s,
                        cardinality: cardinality,
                    }
                } else {
                    if stride & msk < w >> 1 {
                        Clp{
                            width: width,
                            base: base & msk,
                            stride: stride & msk,
                            cardinality: cardinality,
                        }
                    } else {
                        let b = (c - Wrapping(1i64)) * stride + base;
                        Clp{
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
        fn permute(w: usize, a: Vec<Clp>, b: Vec<Clp>, f: &Fn(Clp,Clp) -> Clp) -> Clp {
            if !a.is_empty() && !b.is_empty() {
                let mut ret: Option<Clp> = None;
                for x in a.iter() {
                    for y in b.iter() {
                        let c = f(x.clone(),y.clone());
                        if let Some(ref mut t) = ret {
                            print!("union {:?} and {:?} to ",t,c);
                            *t = Clp::union(t,&c);
                            println!("{:?}",t);
                        } else {
                            println!("got {:?}",c);
                            ret = Some(c);
                        }
                    }
                }

                ret.unwrap_or(Clp{
                    width: a[0].width,
                    base: Wrapping(0),
                    stride: Wrapping(1),
                    cardinality: Clp::mask(a[0].width) + Wrapping(1),
                })
            } else {
                Clp{
                    width: w,
                    base: Wrapping(0),
                    stride: Wrapping(0),
                    cardinality: Wrapping(0),
                }
            }
        }

        match *op {
            Operation::And(ref a,ref b) => {
                if a.is_bottom() { return a.clone(); }
                if b.is_bottom() { return b.clone(); }

                let a_aps = Self::unsigned_progression(a);
                let b_aps = Self::unsigned_progression(b);

                permute(a.width,a_aps,b_aps,&|a,b| {
                    println!("{:?} & {:?}",a,b);

                    if a.cardinality == Wrapping(1i64) && b.cardinality == Wrapping(1i64) {
                        Clp{
                            width: a.width,
                            base: a.base & b.base,
                            stride: Wrapping(0i64),
                            cardinality: Wrapping(1i64),
                        }
                    } else if a.cardinality == Wrapping(1i64) && b.cardinality == Wrapping(2i64){
                        Clp{
                            width: a.width,
                            base: a.base & b.base,
                            stride: (a.base & b.last()) - (a.base & b.base),
                            cardinality: Wrapping(1i64) + Wrapping(1i64),
                        }
                    } else if a.cardinality == Wrapping(2i64) && b.cardinality == Wrapping(1i64) {
                        Clp{
                            width: a.width,
                            base: a.base & b.base,
                            stride: (a.last() & b.base) - (a.base & b.base),
                            cardinality: Wrapping(2i64),
                        }
                    } else {
                        let (l1, u1) = if a.cardinality == Wrapping(1i64) {
                            (a.width as isize,-1)
                        } else {
                            (Clp::trailing_zeros(&a.stride),Clp::most_significant_bit(&(a.base ^ a.last())) - 1)
                        };
                        let (l2, u2) = if b.cardinality == Wrapping(1i64) {
                            (b.width as isize,-1)
                        } else {
                            (Clp::trailing_zeros(&b.stride),Clp::most_significant_bit(&(b.base ^ b.last())) - 1)
                        };

                        println!("l1: {:?}, u1: {:?}, l2: {:?}, u2: {:?}",l1,u1,l2,u2);

                        let l = if l1 < l2 {
                            let msk = Self::mask((l2 - l1) as usize) << l1 as usize;
                            let v = b.base & msk;
                            if v == Wrapping(0i64) { l2 } else { Clp::trailing_zeros(&v) }
                        } else if l1 > l2 {
                            let msk = Self::mask((l1 - l2) as usize) << l2 as usize;
                            let v = a.base & msk;
                            if v == Wrapping(0i64) { l1 } else { Clp::trailing_zeros(&v) }
                        } else {
                            assert_eq!(l1, l2);
                            l1
                        };

                        let u = if u1 < u2 {
                            let msk = Self::mask((u2 - u1) as usize) << (u1 + 1) as usize;
                            let v = a.base & msk;
                            if v == Wrapping(0i64) { u1 } else { Clp::most_significant_bit(&v) - 1 }
                        } else if u1 > u2 {
                            let msk = Self::mask((u1 - u2) as usize) << (u2 + 1) as usize;
                            let v = b.base & msk;
                            if v == Wrapping(0i64) { u2 } else { Clp::most_significant_bit(&v) - 1 }
                        } else {
                            assert_eq!(u1, u2);
                            u1
                        };

                        println!("l: {:?}, u: {:?}",l,u);

                        if l <= u {
                            let uu = if u1 > u2 {
                                if u == u1 {
                                    let mut r = u1;
                                    for i in u1 as usize..b.width {
                                        if (b.base >> i) & Wrapping(1i64) == Wrapping(1i64) {
                                            r = i as isize;
                                        } else {
                                            break;
                                        }
                                    }
                                    Some(r)
                                } else {
                                    Some(u + 1)
                                }
                            } else if u1 < u2 {
                                if u == u2 {
                                    let mut r = u2;
                                    for i in u2 as usize..a.width {
                                        if (a.base >> i) & Wrapping(1i64) == Wrapping(1i64) {
                                            r = i as isize;
                                        } else {
                                            break;
                                        }
                                    }
                                    Some(r)
                                } else {
                                    Some(u + 1)
                                }
                            } else {
                                None
                            };

                            println!("u': {:?}",uu);

                            let stride = if u1 > u2 && u == u1 && uu == Some(l) {
                                cmp::max(a.stride,Wrapping(1i64) << l as usize)
                            } else if u2 > u1 && u == u2 && uu == Some(l) {
                                cmp::max(b.stride,Wrapping(1i64) << l as usize)
                            } else {
                                Wrapping(1i64) << l as usize
                            };
                            let m = if uu.is_some() && l < uu.unwrap() {
                                Self::mask((uu.unwrap() - l) as usize) << l as usize
                            } else {
                                Self::mask(a.width)
                            };

                            println!("m: {:b}",m.0);

                            let low = (a.base & b.base) & !m;
                            let up = cmp::min((a.last() & b.last()) | m,cmp::min(a.last(),b.last()));
                            let t = low - (a.base & b.base);
                            let o = if Self::modulus(t,stride) > Wrapping(0i64) { Wrapping(1i64) } else { Wrapping(0i64) };
                            let base = (a.base & b.base) + stride * ((t / stride) + o);
                            let cardinality = (up - base) / stride + Wrapping(1i64);

                            Clp{
                                width: a.width,
                                base: base,
                                stride: stride,
                                cardinality: cardinality,
                            }
                        } else {
                            Clp{
                                width: a.width,
                                base: a.base & b.base,
                                stride: Wrapping(0i64),
                                cardinality: Wrapping(1i64),
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

                if a.cardinality == Wrapping(1i64) && b.cardinality == Wrapping(1i64) {
                    return Clp{
                        width: a.width,
                        base: base,
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(1i64),
                    }
                }

                let stride = Wrapping(gcd(a.stride.0,b.stride.0));
                let cardinality = (a.last() + b.last() - base) / stride + Wrapping(1i64);

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

                permute(a.width,a_aps,b_aps,&|a,b| {
                    let base = a.base * b.base;
                    if a.cardinality == Wrapping(1i64) && b.cardinality == Wrapping(1i64) {
                        Clp{
                            width: w,
                            base: base,
                            stride: Wrapping(0i64),
                            cardinality: Wrapping(1i64)
                        }
                    } else {
                        let mut stride = Wrapping(gcd(gcd(
                                (a.base * b.stride).0,
                                (b.base * a.stride).0),
                                (a.stride * b.stride).0));
                        if stride.0 == 0 { stride = Wrapping(1i64) };
                        let cardinality = (a.last() * b.last() - base) / stride + Wrapping(1i64);

                        Clp{
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
                if (b.stride.0 != 0 && (b.base % b.stride).0 == 0) || b.base.0 == 0 {
                    return Clp{
                        width: b.width,
                        base: Wrapping(0i64),
                        stride: Wrapping(1i64),
                        cardinality: Clp::mask(b.width) + Wrapping(1i64),
                    };
                }

                let a_aps = Self::signed_progression(a);
                let mut b_aps = vec![];

                for b in Self::signed_progression(b) {
                    if b.base < Wrapping(0) && b.last() >= Wrapping(0) {
                        let c = -b.base / b.stride;
                        let c1 = if -b.base % b.stride == Wrapping(0) { Wrapping(0) } else { Wrapping(1) };
                        b_aps.push(Clp{
                            width: b.width,
                            base: b.base,
                            stride: b.stride,
                            cardinality: c + c1
                        });

                        if c + c1 < b.cardinality {
                            b_aps.push(Clp{
                                width: b.width,
                                base: b.base + (c + c1) * b.stride,
                                stride: b.stride,
                                cardinality: b.cardinality - c - c1
                            });
                        }
                    } else {
                        b_aps.push(b);
                    }
                }

                let m = Self::mask(a.width) + Wrapping(1);
                permute(a.width,a_aps,b_aps,&|a,b| {
                    if a.cardinality == Wrapping(1i64) && b.cardinality == Wrapping(1i64) {
                        return Clp{
                            width: a.width,
                            base: a.base / b.base,
                            stride: Wrapping(0i64),
                            cardinality: Wrapping(1i64),
                        };
                    }

                    let base = cmp::min(a.base / b.base,
                               cmp::min(a.base / b.last() % m,
                               cmp::min(a.last() % m / b.base,
                                        a.last() % m / b.last() % m)));
                    let d = cmp::max(a.base / b.base,
                            cmp::max(a.base / b.last() % m,
                            cmp::max(a.last() % m / b.base,
                                     a.last() % m / b.last() % m)));
                    let stride = if b.cardinality <= Wrapping(10i64) {
                        let mut c1 = true;
                        let mut c2 = true;
                        let mut r = None;
                        let mut i = Wrapping(0i64);
                        let msk = Self::mask(a.width);

                        while i < b.cardinality {
                            let v = b.base + i * b.stride & msk;
                            let g = Wrapping(gcd((a.base / v - base).0,abs((a.stride / v).0)));

                            c1 &= a.base.0.is_multiple_of(&v.0) && a.stride.0.is_multiple_of(&v.0);
                            c2 &= a.stride.0.is_multiple_of(&v.0);

                            if r.is_none() { r = Some(g) } else { r = Some(Wrapping(gcd(g.0,r.unwrap().0))) }

                            i = i + Wrapping(1i64);
                        }

                        if c1 || c2 && (a.last() < Wrapping(0i64) && a.base > Wrapping(0i64)) && r.is_some() {
                            r.unwrap()
                        } else {
                            Wrapping(1i64)
                        }
                    } else {
                        Wrapping(1i64)
                    };
                    let cardinality = if stride != Wrapping(0) {
                        ((d - base) / stride) + Wrapping(1)
                    } else {
                        Wrapping(1)
                    };
                     
                    Clp{
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
                if (b.stride.0 != 0 && (b.base % b.stride).0 == 0) || b.base.0 == 0 {
                    return Clp{
                        width: b.width,
                        base: Wrapping(0i64),
                        stride: Wrapping(1i64),
                        cardinality: Clp::mask(b.width) + Wrapping(1i64),
                    };
                }
                
                let a_aps = Self::unsigned_progression(a);
                let b_aps = Self::unsigned_progression(b);
                let msk = Self::mask(a.width);

                permute(a.width,a_aps,b_aps,&|a,b| {
                    if a.cardinality == Wrapping(1i64) && b.cardinality == Wrapping(1i64) {
                        return Clp{
                            width: a.width,
                            base: (a.base & msk) / (b.base & msk),
                            stride: Wrapping(0i64),
                            cardinality: Wrapping(1i64),
                        };
                    }

                    let base = (a.base & msk) / (b.last() & msk);
                    let mut stride = if b.cardinality <= Wrapping(10i64) {
                        let mut c = true;
                        let mut r = None;
                        let mut i = Wrapping(0i64);

                        while i < b.cardinality {
                            let v = b.base + i * b.stride;
                            let g = Wrapping(gcd((a.base / v - base).0,(a.stride / v).0));

                            c &= a.stride.0.is_multiple_of(&v.0);

                            if r.is_none() { r = Some(g) } else { r = Some(Wrapping(gcd(g.0,r.unwrap().0))) }
                            i = i + Wrapping(1i64);
                        }

                        if c && r.is_some() {
                            r.unwrap()
                        } else {
                            Wrapping(1i64)
                        }
                    } else {
                        Wrapping(1i64)
                    };
                    let cardinality = if stride != Wrapping(0) {
                        ((((a.last() & msk) / (b.base & msk)) - base) / stride) + Wrapping(1i64)
                    } else {
                        Wrapping(1)
                    };

                    Clp{
                        width: a.width,
                        base: base,
                        stride: stride,
                        cardinality: cardinality
                    }
                })
            },
            Operation::Modulo(ref a,ref b) => {
                if a.is_bottom() { return a.clone(); }
                if b.is_bottom() { return b.clone(); }
                if (b.stride.0 != 0 && (b.base % b.stride).0 == 0) || b.base.0 == 0 {
                    return Clp{
                        width: b.width,
                        base: Wrapping(0i64),
                        stride: Wrapping(1i64),
                        cardinality: Clp::mask(b.width) + Wrapping(1i64),
                    };
                }
                let a_aps = Self::signed_progression(a);
                let mut b_aps = vec![];

                for b in Self::signed_progression(b) {
                    if b.base < Wrapping(0) && b.last() >= Wrapping(0) {
                        let c = -b.base / b.stride;
                        let c1 = if -b.base % b.stride == Wrapping(0) { Wrapping(0) } else { Wrapping(1) };
                        b_aps.push(Clp{
                            width: b.width,
                            base: b.base,
                            stride: b.stride,
                            cardinality: c + c1
                        });

                        if c + c1 < b.cardinality {
                            b_aps.push(Clp{
                                width: b.width,
                                base: b.base + (c + c1) * b.stride,
                                stride: b.stride,
                                cardinality: b.cardinality - c - c1
                            });
                        }
                    } else {
                        b_aps.push(b);
                    }
                }

                println!("perm: {:?} {:?}",a_aps,b_aps);

                permute(a.width,a_aps,b_aps,&|a,b| {
                    let x = Clp::execute(pp,&Operation::DivideSigned(a.clone(),b.clone()));
                    let y = Clp::execute(pp,&Operation::Multiply(x,b.clone()));
                    Clp::execute(pp,&Operation::Subtract(a.clone(),y))
                })
            },
            Operation::ShiftRightSigned(ref a,ref b) => {
                if a.is_bottom() { return a.clone(); }
                if b.is_bottom() { return b.clone(); }
                
                let a_aps = Self::signed_progression(a);
                let b_aps = Self::unsigned_progression(b);

                fn safe_shrs(a: &Wrapping<i64>, b: &Wrapping<i64>, w: usize) -> Wrapping<i64> {
                    if *b < Wrapping(0) || *b >= Wrapping(w as i64) {
                        if *a < Wrapping(0) { Wrapping(-1) } else { Wrapping(0) }
                    } else {
                        *a >> b.0 as usize
                    }
                }

                permute(a.width,a_aps,b_aps,&|a,b| {
                    if a.cardinality == Wrapping(1i64) && b.cardinality == Wrapping(1i64) {
                        return Clp{
                            width: a.width,
                            base: safe_shrs(&a.base,&b.base,a.width),
                            stride: Wrapping(0i64),
                            cardinality: Wrapping(1i64),
                        };
                    }

                    let base = if a.base >= Wrapping(0) {
                        safe_shrs(&a.base,&b.last(),a.width)
                    } else {
                        safe_shrs(&a.base,&b.base,a.width)
                    };
                    let stride = Wrapping(1);
                    let cardinality = if a.base <= a.last() {
                        let x = safe_shrs(&a.last(),&b.base,a.width);
                        ((x - base) / stride) + Wrapping(1)
                    } else {
                        let x = safe_shrs(&a.last(),&b.last(),a.width);
                        ((x - base) / stride) + Wrapping(1)
                    };

                    Clp{
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
                let b_aps = Self::unsigned_progression(b);

                fn safe_shru(a: &Wrapping<i64>, b: &Wrapping<i64>, w: usize) -> Wrapping<i64> {
                    if *b < Wrapping(0) || *b >= Wrapping(w as i64) {
                        Wrapping(0)
                    } else {
                        Wrapping((Wrapping(a.0 as u64) >> b.0 as usize).0 as i64)
                    }
                }

                permute(a.width,a_aps,b_aps,&|a,b| {
                    println!("{:?} >> {:?}",a,b);

                    if a.cardinality == Wrapping(1) && b.cardinality == Wrapping(1) {
                        return Clp{
                            width: a.width,
                            base: safe_shru(&a.base,&b.base,a.width),
                            stride: Wrapping(0),
                            cardinality: Wrapping(1),
                        };
                    }

                    let base = safe_shru(&a.base,&b.last(),a.width);
                    let stride = Wrapping(1);
                    let cardinality = if stride != Wrapping(0) {
                        let last = safe_shru(&a.last(),&b.base,a.width);
                        ((last - base) / stride) + Wrapping(1i64)
                    } else {
                        Wrapping(1)
                    };

                    Clp{
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
                
                let a_aps = vec![Self::canonize(a)];
                let b_aps = Self::unsigned_progression(b);
                let msk = Self::mask(a.width);

                permute(a.width,a_aps,b_aps,&|a,b| {
                    let base = a.base << (b.base.0 as usize);
                    let stride = if b.cardinality == Wrapping(1) {
                        a.stride << (b.base.0 as usize)
                    } else {
                        Wrapping(gcd(a.base.0,a.stride.0))
                    };
                    let cardinality = if stride != Wrapping(0) {
                        (((((a.last()) << (b.last()).0 as usize) ) - base) / stride) + Wrapping(1)
                    } else {
                        Wrapping(1)
                    };

                    Clp{
                        width: a.width,
                        base: base,
                        stride: stride % (msk + Wrapping(1)),
                        cardinality: if cardinality > Wrapping(0) {
                            cmp::min(Wrapping(cardinality.0.abs()),msk + Wrapping(2))
                        } else {
                            msk + Wrapping(2)
                        }
                    }
                })
            },

            Operation::LessOrEqualSigned(ref a,ref b) => {
                let x = Clp::execute(pp,&Operation::LessSigned(a.clone(),b.clone()));
                let y = Clp::execute(pp,&Operation::Equal(a.clone(),b.clone()));
                Clp::execute(pp,&Operation::ExclusiveOr(x,y))
            },

            Operation::LessOrEqualUnsigned(ref a,ref b) => {
                let x = Clp::execute(pp,&Operation::LessUnsigned(a.clone(),b.clone()));
                let y = Clp::execute(pp,&Operation::Equal(a.clone(),b.clone()));
                Clp::execute(pp,&Operation::ExclusiveOr(x,y))
            },

            Operation::LessSigned(ref a,ref b) => {
                if a.is_bottom() || b.is_bottom() {
                    return Clp{
                        width: 1,
                        base: Wrapping(0i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(0i64),
                    }
                }

                let (min1,max1) = Self::signed_minmax(a);
                let (min2,max2) = Self::signed_minmax(b);

                if max1 < min2 {
                    return Clp{
                        width: 1,
                        base: Wrapping(1i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(1i64),
                    }
                } else if min1 >= max2 {
                    return Clp{
                        width: 1,
                        base: Wrapping(0i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(1i64),
                    }
                } else {
                    return Clp{
                        width: 1,
                        base: Wrapping(0i64),
                        stride: Wrapping(1i64),
                        cardinality: Wrapping(1i64) + Wrapping(1i64),
                    }
                }
            },

            Operation::LessUnsigned(ref a,ref b) => {
                if a.is_bottom() || b.is_bottom() {
                    return Clp{
                        width: 1,
                        base: Wrapping(0i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(0i64),
                    }
                }

                let (min1,max1) = Self::unsigned_minmax(a);
                let (min2,max2) = Self::unsigned_minmax(b);

                println!("a: {:?}/{:?}, b: {:?}/{:?}",min1,max1,min2,max2);

                if max1 < min2 {
                    return Clp{
                        width: 1,
                        base: Wrapping(1i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(1i64),
                    }
                } else if min1 >= max2 {
                    return Clp{
                        width: 1,
                        base: Wrapping(0i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(1i64),
                    }
                } else {
                    return Clp{
                        width: 1,
                        base: Wrapping(0i64),
                        stride: Wrapping(1i64),
                        cardinality: Wrapping(2),
                    }
                }
            }, 

            Operation::Equal(ref a,ref b) => {
                if a.is_bottom() || b.is_bottom() {
                    Clp{
                        width: 1,
                        base: Wrapping(0i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(0i64),
                    }
                } else if a.cardinality == Wrapping(1i64) && b.cardinality == Wrapping(1i64) && a.base == b.base {
                    Clp{
                        width: 1,
                        base: Wrapping(1i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(1i64),
                    }
                } else if Clp::intersection(a,b).is_bottom() {
                    Clp{
                        width: 1,
                        base: Wrapping(0i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(1i64),
                    }
                } else {
                    Clp{
                        width: b.width,
                        base: Wrapping(0i64),
                        stride: Wrapping(1i64),
                        cardinality: Clp::mask(b.width),
                    }
                }
            },

            Operation::Move(ref a) => a.clone(),
            Operation::Call(ref a) => a.clone(),

            Operation::ZeroExtend(ref sz,ref a) => Clp{
                width: *sz,
                base: a.base,
                stride: a.stride,
                cardinality: a.cardinality,
            },

            Operation::SignExtend(ref sz,ref a) => Clp{
                width: *sz,
                base: a.base,
                stride: a.stride,
                cardinality: a.cardinality,
            },

            Operation::Select(ref off,ref a,ref b) => {
                let o = Clp{
                    width: a.width,
                    base: Wrapping(*off as i64),
                    stride: Wrapping(0i64),
                    cardinality: Wrapping(1i64),
                };
                let x = Clp::execute(pp,&Operation::ShiftRightUnsigned(a.clone(),o));
                Clp::execute(pp,&Operation::DivideUnsigned(x,b.clone()))
            },

            Operation::Load(_,ref a) => Clp{
                width: a.width,
                base: Wrapping(0i64),
                stride: Wrapping(1i64),
                cardinality: Clp::mask(a.width),
            },

            Operation::Store(_,ref a) => a.clone(),

            Operation::Phi(ref v) => match v.len() {
                0 => unreachable!(),
                1 => v[0].clone(),
                _ => v.iter().skip(1).fold(v[0].clone(),|acc,x| {
                    Clp::union(&acc,x)
                }),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::num::Wrapping;
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

        fn extract(&self,_: usize,_: usize) -> Self {
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

        assert!(ssa_convertion(&mut func).is_ok());

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

        assert!(ssa_convertion(&mut func).is_ok());

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
    fn clp_helper() {
        // eea
        {
            let (a,b) = Clp::eea(&Wrapping(99),&Wrapping(78));
            assert_eq!(a, Wrapping(3));
            assert_eq!(b, Wrapping(-11));

            let (a,b) = Clp::eea(&Wrapping(78),&Wrapping(99));
            assert_eq!(a, Wrapping(3));
            assert_eq!(b, Wrapping(14));
        }

        // canonize
        {
            let a = Clp{ width: 8, base: Wrapping(216), stride: Wrapping(48), cardinality: Wrapping(19) };
            let c = Clp{ width: 8, base: Wrapping(8), stride: Wrapping(16), cardinality: Wrapping(16) };

            assert_eq!(c, Clp::canonize(&a));
            Clp::canonize(&Clp{ width: 64, base: Wrapping(216), stride: Wrapping(48), cardinality: Wrapping(19) });
        }

        {
            let a = Clp{ width: 8, base: Wrapping(216), stride: Wrapping(48), cardinality: Wrapping(15) };
            let c = Clp{ width: 8, base: Wrapping(184), stride: Wrapping(16), cardinality: Wrapping(15) };

            assert_eq!(c, Clp::canonize(&a));
            Clp::canonize(&Clp{ width: 64, base: Wrapping(216), stride: Wrapping(48), cardinality: Wrapping(15) });
        }

        {
            let a = Clp{ width: 8, base: Wrapping(90), stride: Wrapping(132), cardinality: Wrapping(7) };
            let c = Clp{ width: 8, base: Wrapping(114), stride: Wrapping(124), cardinality: Wrapping(7) };

            assert_eq!(c, Clp::canonize(&a));
            Clp::canonize(&Clp{ width: 64, base: Wrapping(90), stride: Wrapping(132), cardinality: Wrapping(7) });
        }

        // unsigned union
        {
            let c = Clp{ width: 8, base: Wrapping(60), stride: Wrapping(30), cardinality: Wrapping(10) };
            let u1 = Clp{ width: 8, base: Wrapping(60), stride: Wrapping(30), cardinality: Wrapping(7) };
            let u2 = Clp{ width: 8, base: Wrapping(14), stride: Wrapping(30), cardinality: Wrapping(3) };

            assert_eq!(c, Clp::union(&u1,&u2));
        }

        // signed union
        {
            let c = Clp{ width: 8, base: Wrapping(60), stride: Wrapping(30), cardinality: Wrapping(10) };
            let u1 = Clp{ width: 8, base: Wrapping(60), stride: Wrapping(30), cardinality: Wrapping(3) };
            let u2 = Clp{ width: 8, base: Wrapping(-106), stride: Wrapping(30), cardinality: Wrapping(7) };

            assert_eq!(c, Clp::union(&u1,&u2));
        }

        // unsigned AP
        {
            let c = Clp{ width: 8, base: Wrapping(60), stride: Wrapping(30), cardinality: Wrapping(10) };
            let ap = Clp::unsigned_progression(&c);
            let u1 = Clp{ width: 8, base: Wrapping(60), stride: Wrapping(30), cardinality: Wrapping(7) };
            let u2 = Clp{ width: 8, base: Wrapping(14), stride: Wrapping(30), cardinality: Wrapping(3) };

            assert_eq!(ap.len(), 2);
            assert!(ap[0] == u1 || ap[0] == u2);
            assert!(ap[1] == u1 || ap[1] == u2);
            assert!(ap[0] != ap[1]);

            assert_eq!(c, Clp::union(&u1,&u2));
        }

        // signed AP
        {
            let c = Clp{ width: 8, base: Wrapping(60), stride: Wrapping(30), cardinality: Wrapping(10) };
            let ap = Clp::signed_progression(&c);
            let u1 = Clp{ width: 8, base: Wrapping(60), stride: Wrapping(30), cardinality: Wrapping(3) };
            let u2 = Clp{ width: 8, base: Wrapping(-106), stride: Wrapping(30), cardinality: Wrapping(7) };

            assert_eq!(ap.len(), 2);
            assert!(ap[0] == u1 || ap[0] == u2);
            assert!(ap[1] == u1 || ap[1] == u2);
            assert!(ap[0] != ap[1]);

            assert_eq!(c, Clp::union(&u1,&u2));
        }
    }

macro_rules! kset_clp_xcheck {
    ($op:path,$a:ident,$b:ident) => {{
        use std::iter::FromIterator;

        println!("in: {:?},{:?}",$a,$b);

        let mut a = $a;
        let mut b = $b;

        if a.1 == 0 && a.2 > 1 { a.1 = 1 }
        if b.1 == 0 && b.2 > 1 { b.1 = 1 }

        /*if a.2 + b.2 > 3 {
            if a.2 % 2 == 0 {
                a.2 = 2;
                b.2 = 1;
            } else {
                a.2 = 1;
                b.2 = 2;
            }
        }*/

        let clp_a = Clp{
            width: 16,
            base: Wrapping(a.0 as i64),
            stride: Wrapping(a.1 as i64),
            cardinality: Wrapping(a.2 as i64),
        };
        let clp_b = Clp{
            width: 16,
            base: Wrapping(b.0 as i64),
            stride: Wrapping(b.1 as i64),
            cardinality: Wrapping(b.2 as i64),
        };
        let pp = ProgramPoint{ address: 0, position: 0 };

        println!("{:?} + {:?} =",clp_a,clp_b);

        let clp_op = $op(clp_a,clp_b);
        let clp_res = Clp::execute(&pp,&clp_op);
        let kset_a = Kset::Set(Vec::<(u64,usize)>::from_iter((0..a.2).map(|i| 
            (a.0.wrapping_add(a.1.wrapping_mul(i as i16)) as u64 & 0xffff,16)
        )));
        let kset_b = Kset::Set(Vec::<(u64,usize)>::from_iter((0..b.2).map(|i| 
            (b.0.wrapping_add(b.1.wrapping_mul(i as i16)) as u64 & 0xffff,16)
        )));
        let kset_op = $op(kset_a,kset_b);
        let kset_res = Kset::execute(&pp,&kset_op);
        let msk = Wrapping(0xffffi64);

        println!("{:?}/{:?}",clp_res,kset_res);

        let ret = match kset_res {
            Kset::Meet => clp_res.cardinality.0 == 0,
            Kset::Set(ref v) => {
                if clp_res.cardinality.0 > 0xffff {
                    true
                } else {
                    if clp_res.cardinality.0 < v.len() as i64 {
                        println!("clp too small: {} kset: {}",clp_res.cardinality.0,v.len());
                        false
                    } else {
                        v.iter().all(|x| {
                            let l = Wrapping(x.0 as i64);
                            let ret = if clp_res.is_top() {
                                true
                            } else if clp_res.is_bottom() {
                                false
                            } else if clp_res.cardinality.0 == 1 {
                                clp_res.base & msk == l & msk
                            } else {
                                let mut ret = false;
                                for y in 0..clp_res.cardinality.0 {
                                    let i = Wrapping(y);
                                    ret |= (clp_res.base + clp_res.stride * i) & msk == l;
                                }
                                ret
                            };

                            if !ret {
                                println!("{} not in {:?}",x.0,clp_res);
                            }
                            ret
                        })
                    }
                }
            }
            Kset::Join => clp_res.cardinality.0 > 0xffff,
        };
        println!("");
        ret
    }
}}

    quickcheck! {
        /*fn clp_closest_element_qc(a_: (i16,i16,u16), l: i16) -> bool {
            use std::cmp;
            use std::i64;

            let mut a = a_;

            if a.1 == 0 && a.2 > 1 { a.1 = 1 }

            let clp_a = Clp{
                width: 16,
                base: Wrapping(a.0 as i64),
                stride: Wrapping(a.1 as i64),
                cardinality: Wrapping(a.2 as i64),
            };
            let msk = 0xffff;

            println!("clp: {:?}, l: {}",clp_a,l);

            if !clp_a.is_bottom() && !clp_a.is_top() {
                let (_,_,_,_,_,gamma) = Clp::closest_element(&clp_a,&Wrapping(l as i64));
                let mut gap = i64::MAX;
                for i in 0..(a.2 as i64) {
                    let v = (clp_a.base + clp_a.stride * Wrapping(i)) & Wrapping(0xffff);
                    if v.0 <= l as i64 {
                        gap = cmp::min(gap,(l as i64) - v.0);
                    }
                }

                if gamma.0 & msk != (clp_a.base.0 - (l as i64)) & msk && (-gamma.0) & msk != gap & msk {
                    println!("FAILED gap: {}, gamma: {}",(clp_a.base.0 - (l as i64)) & msk,gamma.0 & msk);
                    println!("ALT gap: {}, gamma: {}",gap & msk,(-gamma.0) & msk);
                    false
                } else {
                    true
                }
            } else {
                true
            }
        }*/

        fn clp_sub_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::Subtract,a_,b_)
        }

        fn clp_add_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::Add,a_,b_)
        }

        fn clp_mul_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::Multiply,a_,b_)
        }

        fn clp_divs_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::DivideSigned,a_,b_)
        }

        fn clp_divu_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::DivideUnsigned,a_,b_)
        }
        
        fn clp_mod_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::Modulo,a_,b_)
        }

        fn clp_shl_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::ShiftLeft,a_,b_)
        }

        fn clp_shru_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::ShiftRightUnsigned,a_,b_)
        }

        fn clp_shrs_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::ShiftRightSigned,a_,b_)
        }

        fn clp_and_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::And,a_,b_)
        }

        fn clp_or_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::InclusiveOr,a_,b_)
        }

        fn clp_xor_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::ExclusiveOr,a_,b_)
        }

        fn clp_eq_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::Equal,a_,b_)
        }

        fn clp_lu_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::LessUnsigned,a_,b_)
        }

        fn clp_ls_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::LessSigned,a_,b_)
        }

        fn clp_leu_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::LessOrEqualUnsigned,a_,b_)
        }

        fn clp_les_semantics_qc(a_: (i16,i16,u16), b_: (i16,i16,u16)) -> bool {
            kset_clp_xcheck!(Operation::LessOrEqualSigned,a_,b_)
        }

        /*
        &Operation::Select(ref off, _, _) => Operation::Select(*off,args[0].clone(),args[1].clone()),
        &Operation::ZeroExtend(ref sz, _) => Operation::ZeroExtend(*sz,args[0].clone()),
        &Operation::SignExtend(ref sz,_) => Operation::SignExtend(*sz,args[0].clone()),*/
    }
}
