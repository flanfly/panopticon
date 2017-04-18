/*
 * Panopticon - A libre disassembler
 * Copyright (C) 2017 Panopticon authors
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

//! Linus Kaellberg: "Circular Linear Progressions in SWEET"

use std::cmp;
use std::num::Wrapping;
use num::{Integer,abs};
use num::integer::{lcm,gcd};
use std::result;
use std::fmt::{
    Display,
    Formatter,
    Error,
};
use rustc_serialize::{
    Encodable,Decodable,
    Decoder,Encoder
};

use {
    Operation,
    ProgramPoint,
};

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

impl Display for Clp {
    fn fmt(&self, f: &mut Formatter) -> result::Result<(), Error> {
        if self.is_bottom() {
            f.write_str("⟂")
        } else if self.is_top() {
            f.write_str("⊤")
        } else {
            f.write_fmt(format_args!("CLP_{}({},{},{})",self.width,self.base,self.stride,self.cardinality))
        }
    }
}

impl Clp {
    pub fn new(w: usize, b: i64, s: i64, c: i64) -> Self {
        Clp{
            width: w,
            base: Wrapping(b),
            stride: Wrapping(s),
            cardinality: Wrapping(c),
        }
    }

    pub fn bottom(w: usize) -> Self {
        assert!(w > 0);

        Clp{
            width: w,
            base: Wrapping(0i64),
            stride: Wrapping(0i64),
            cardinality: Wrapping(0i64),
        }
    }

    /// Correct floor() function. Rounds to the largest integer less than or equal to `x`.
    fn gauss_floor(x: f32) -> Wrapping<i64> {
        if x < 0. {
            Wrapping(x.ceil() as i64)
        } else {
            Wrapping(x.floor() as i64)
        }
    }

    /// Correct ceil() function. Rounds to the smallest integer greater than or equal to `x`.
    fn gauss_ceil(x: f32) -> Wrapping<i64> {
        if x < 0. {
            Wrapping(x.floor() as i64)
        } else {
            Wrapping(x.ceil() as i64)
        }
    }

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

    fn most_significant_bit(a_: &Wrapping<i64>) -> isize {
        let mut ret = 0;
        let mut a = a_.clone();

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
        c > Self::mask(self.width) && self.stride.0.is_odd()
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

    pub fn closest_element(c: &Clp, l: &Wrapping<i64>) -> (Wrapping<i64>,Wrapping<i64>,Wrapping<i64>,Wrapping<i64>,Wrapping<i64>,Wrapping<i64>) {
        let c = Self::canonize(c);
        let modu = Self::mask(c.width) + Wrapping(1);

        assert!(!c.is_bottom() && !c.is_top());

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
            //assert!(gamma.0 <= cmp::min(alpha.0,beta.0));

            if alpha < beta {
                assert!(gamma < beta);

                let kk = -1. * (gamma - beta).0 as f32 / alpha.0 as f32;
                let kk = Self::gauss_ceil(kk);

                let x = (c.cardinality - Wrapping(1i64) - (ic + ib)).0 as f32 / ia.0 as f32;
                let x = Self::gauss_floor(x);

                if kk <= x && -beta + kk * alpha < Wrapping(0i64) {
                    ic = ic + ib + kk * ia;
                    gamma = gamma - beta + kk * alpha;

                    assert!(gamma.0 >= 0);
                }

                let k1 = (beta - Wrapping(1i64)).0 as f32 / alpha.0 as f32;
                let k1 = Self::gauss_floor(k1);

                let k2 = (c.cardinality - Wrapping(1i64) - ib).0 as f32 / ia.0 as f32;
                let k2 = Self::gauss_floor(k2);

                let k = cmp::min(k1,k2);

                ib = ib + k * ia;
                beta = beta - k * alpha;
            } else {
                let kk1 = gamma.0 as f32 / beta.0 as f32;
                let kk1 = Self::gauss_floor(kk1);

                let kk2 = (c.cardinality - Wrapping(1i64) - ic).0 as f32 / ib.0 as f32;
                let kk2 = Self::gauss_floor(kk2);

                let kk = cmp::min(kk1,kk2);

                ic = ic + kk * ib;
                gamma = gamma - kk * beta;

                let k1 = (alpha - Wrapping(1i64)).0 as f32 / beta.0 as f32;
                let k1 = Self::gauss_floor(k1);

                let k2 = (c.cardinality - Wrapping(1i64) - ia).0 as f32 / ib.0 as f32;
                let k2 = Self::gauss_floor(k2);

                let k = cmp::min(k1,k2);

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
        debug!("unsigned_minmax({})",a);

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

        debug!("min_idx={}, max_idx={}, cardinality={}",min_idx.0,max_idx.0,a.cardinality.0);
        assert!(min_idx < a.cardinality);
        assert!(max_idx < a.cardinality);

        debug!("min={}, max={}",Self::modulus(a.base + min_idx * a.stride,modu),Self::modulus(a.base + max_idx * a.stride,modu));

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

    pub fn intersection(a: &Clp, b: &Clp) -> Clp {
        debug!("intersection() a={}, b={}",a,b);

        if a.is_bottom() || b.is_top() { return a.clone() }
        if b.is_bottom() || a.is_top() { return b.clone() }

        let a = Self::canonize(a);
        let b = Self::canonize(b);

        println!("intersection() a={}, b={}",a,b);

        if a.cardinality == Wrapping(1) && b.cardinality == Wrapping(1) {
            if a.base == b.base {
                return a.clone();
            } else {
                return Self::bottom(a.width);
            }
        } else if a.cardinality == Wrapping(1) {
            if (a.base - b.base) % b.stride == Wrapping(0) {
                return a.clone();
            } else {
                return Self::bottom(a.width);
            }
        } else if b.cardinality == Wrapping(1) {
            if (b.base - a.base) % a.stride == Wrapping(0) {
                return b.clone();
            } else {
                return Self::bottom(a.width);
            }
        }
/*
        let s = a.stride.lcm(b.stride);
        let mut a;
        let mut b;

        if a.base > b.base {
            a = b.clone();
            b = a.clone();
        } else {
            a = a.clone();
            b = b.clone();
        }


*/

        let (d,s) = Self::eea(&a.stride,&(Self::mask(a.width) + Wrapping(1i64)));
        let (e,t) = Self::eea(&b.stride,&d);
        let j0 = Self::modulus(t * (a.base - b.base) / e,d / e);

        println!("(d,s) = ({},{})",d,s);
        println!("(e,t) = ({},{})",e,t);
        println!("j0 = {}",j0);

        println!("j0={}, (d,s)={:?}, (e,t)={:?}",j0,(d,s),(e,t));
        println!("(c2 - j0) / (d / e) = {} / {}",b.cardinality - j0,d / e);

        let n = (b.cardinality - j0).0 as f32 / (d.0 as f32 / e.0 as f32);
        let n = Self::gauss_floor(n);
        let w = (Self::mask(a.width).0 as f32 + 1.) / d.0 as f32;

        let i = Self::canonize(&Clp{
            width: w.log2() as usize,
            base: s * (b.base - a.base + b.stride * j0) / d,
            stride: b.stride * s / e,
            cardinality: n + Wrapping(0)
        });

        println!("intersection i={:?}",i);

        if (a.base - b.base) % e != Wrapping(0) {
            debug!("{} - {} does not divide {}",a.base,b.base,e);
            return Clp::bottom(a.width);
        }
        if j0 >= b.cardinality {
            debug!("j0 >= n2 ({} >= {})",j0,b.cardinality);
            return Clp::bottom(a.width);
        }

        let (i0,i1) = Self::unsigned_minmax(&i);

        if i0 >= a.cardinality {
            debug!("i0 >= n1 ({} >= {})",i0,a.cardinality);
            return Clp::bottom(a.width);
        }

        let (_,_,_,alpha,beta,_) = Self::closest_element(&i,&i.base);
        let stride = a.stride * Wrapping(gcd(gcd(alpha.0,beta.0),(alpha + beta).0));

        let r = Clp{
            width: a.width,
            base: a.base + a.stride * i0,
            stride: stride,
            cardinality: ((a.base + a.stride * i1) / stride) + Wrapping(1i64),
        };
        println!("intersection result={}",r);
        r
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
                    base = Self::modulus((base - modul),modul);
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
                               cmp::min(Self::modulus(a.base / b.last(), m),
                               cmp::min(Self::modulus(a.last(), m) / b.base,
                                        Self::modulus(a.last(), m) / Self::modulus(b.last(), m))));
                    let d = cmp::max(a.base / b.base,
                            cmp::max(Self::modulus(a.base / b.last(), m),
                            cmp::max(Self::modulus(a.last(), m) / b.base,
                                     Self::modulus(a.last(), m) / Self::modulus(b.last(), m))));
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
                    let stride = if b.cardinality <= Wrapping(10i64) {
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
                        stride: Self::modulus(stride, (msk + Wrapping(1))),
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
                debug!("{} == {}",a,b);

                if a.is_bottom() || b.is_bottom() {
                    debug!("1");
                    Clp{
                        width: 1,
                        base: Wrapping(0i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(0i64),
                    }
                } else if a.cardinality == Wrapping(1i64) && b.cardinality == Wrapping(1i64) && a.base == b.base {
                    debug!("2");
                    Clp{
                        width: 1,
                        base: Wrapping(1i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(1i64),
                    }
                } else if Clp::intersection(a,b).is_bottom() {
                    debug!("3");
                    Clp{
                        width: 1,
                        base: Wrapping(0i64),
                        stride: Wrapping(0i64),
                        cardinality: Wrapping(1i64),
                    }
                } else {
                    debug!("4");
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
    use {
        Operation,
    };

    /*
    use quickcheck::{Arbitrary,Gen};

    impl Arbitrary for Clp {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let base = g.gen_range(-32768,65536);
            let stride = g.gen_range(-32768,65536);
            let cardinality = g.gen_range(0,65536);

            Clp{
                width: 16,
                base: base,
                stride: if cardinality < 2 { 0 } else { stride },
                cardinality: cardinality,
            }
        }
    }*/

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
        use {Kset,Avalue,KSET_MAXIMAL_CARDINALITY};

        debug!("in: {:?},{:?}",$a,$b);

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
                        error!("clp too small: {} kset: {}",clp_res.cardinality.0,v.len());
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
            Kset::Join => clp_res.cardinality.0 > KSET_MAXIMAL_CARDINALITY as i64,
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

    #[test]
    fn clp_intersection() {
        use env_logger;

        env_logger::init().unwrap();
        //assert_eq!(Clp::intersection(&Clp::new(16,0,0,1),&Clp::new(16,0,6,21)), Clp::new(16,0,0,1));
        assert_eq!(Clp::intersection(&Clp::new(16,0,6,2),&Clp::new(16,1,1,6)), Clp::new(16,6,0,2));
        //assert_eq!(Clp::intersection(&Clp::new(16,0,-14,7),&Clp::new(16,-29,-13,2)), Clp::new(16,-42,0,1));
    }
}
