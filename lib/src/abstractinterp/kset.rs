/*
 * Panopticon - A libre disassembler
 * Copyright (C) 2016 Panopticon Authors
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

//! Kindler et.al style Kset domain.
//!
//! TODO

use std::borrow::Cow;
use std::collections::{HashSet,HashMap};
use std::iter::FromIterator;
use std::ops::Range;

use {
    Rvalue,
    Avalue,
    Constraint,
    ProgramPoint,
    Operation,
    execute,
    Region,
};

/// Largest Kset cardinality before Join.
const KSET_MAXIMAL_CARDINALITY: usize = 10;

/// Kindler et.al style Kset domain. Domain elements are sets of concrete values. Sets have a
/// maximum cardinality. Every set larger than that is equal the lattice join. The partial order is
/// set inclusion.
#[derive(Debug,Eq,Clone,Hash,RustcDecodable,RustcEncodable)]
pub enum Kset {
    /// Lattice join. Sets larger than `KSET_MAXIMAL_CARDINALITY`.
    Join,
    /// Set of concrete values and their size in bits. The set is never empty and never larger than
    /// `KSET_MAXIMAL_CARDINALITY`.
    Set(Vec<(u64,usize)>),
    /// Lattice meet, equal to the empty set.
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

    fn execute(_: &ProgramPoint, op: &Operation<Self>, reg: Option<&Region>, _: &HashMap<Range<u64>,Cow<'static,str>>, _: &HashMap<(Cow<'static,str>,usize),Self>) -> Self {
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

        println!("exec {:?}",op);

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
            Operation::ZeroExtend(ref sz,ref a) =>
                map(a,&|a| execute(Operation::ZeroExtend(*sz,a))),
            Operation::SignExtend(ref sz,ref a) =>
                map(a,&|a| execute(Operation::SignExtend(*sz,a))),
            Operation::Select(ref off,ref a,ref b) =>
                permute(a,b,&|a,b| execute(Operation::Select(*off,a,b))),
            Operation::Initialize(_,_) =>
                Kset::Join,

            Operation::Load(ref r,ref endian,ref sz,ref a) =>
                map(a,&|a| {
                    println!("load from {:?}",a);
                    if let Some(ref reg) = reg {
                        if reg.name() == r {
                            if let Rvalue::Constant{ value, size } = a {
                                if let Some(Some(val)) = reg.iter().seek(value).next() {
                                    println!("read {:?}",val);
                                    return Rvalue::Constant{ value: val as u64, size: 8 };
                                }
                            }
                        }
                    }
                    Rvalue::Undefined
                }),
            Operation::Store(ref r,ref endian,ref sz,ref a) =>
                map(a,&|a| execute(Operation::Store(r.clone(),*endian,*sz,a))),

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

