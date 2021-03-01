#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(unused_variables)]

use concordium_std::*;
use std::collections::*;

use core::marker::PhantomData;
use immutable_map::TreeMap;

// pub fn deserialize(...) -> &'a Msg<'a> {
//   let m : Msg<'a> = deserialize(...);
//   Box::leak(Box::new(m))
// }


fn __nat_succ(x: u64) -> u64 {
  x.checked_add(1).unwrap()
}

macro_rules! __nat_elim {
    ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {
        { let v = $val;
        if v == 0 { $zcase } else { let $pred = v - 1; $scase } }
    }
}

macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }
macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }

fn __pos_onebit(x: u64) -> u64 {
  x.checked_mul(2).unwrap() + 1
}

fn __pos_zerobit(x: u64) -> u64 {
  x.checked_mul(2).unwrap()
}

macro_rules! __pos_elim {
    ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {
        {
            let n = $val;
            if n == 1 {
                $onecase
            } else if (n & 1) == 0 {
                let $p2 = n >> 1;
                $zerobcase
            } else {
                let $p = n >> 1;
                $onebcase
            }
        }
    }
}

fn __Z_frompos(z: u64) -> i64 {
  use std::convert::TryFrom;

  i64::try_from(z).unwrap()
}

fn __Z_fromneg(z : u64) -> i64 {
  use std::convert::TryFrom;

  i64::try_from(z).unwrap().checked_neg().unwrap()
}

macro_rules! __Z_elim {
    ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {
        {
            let n = $val;
            if n == 0 {
                $zero_case
            } else if n < 0 {
                let $p2 = n.unsigned_abs();
                $neg_case
            } else {
                let $p = n as u64;
                $pos_case
            }
        }
    }
}

fn __N_frompos(z: u64) -> u64 {
  z
}

macro_rules! __N_elim {
    ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {
        { let $p = $val; if $p == 0 { $zero_case } else { $pos_case } }
    }
}

type __pair<A, B> = (A, B);

macro_rules! __pair_elim {
    ($fst:ident, $snd:ident, $body:expr, $p:expr) => {
        { let ($fst, $snd) = $p; $body }
    }
}

fn __mk_pair<A: Copy, B: Copy>(a: A, b: B) -> __pair<A, B> { (a, b) }

fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {
  f
}

type State<'a> = Storage<'a>;

#[derive(Debug, PartialEq, Eq)]
enum InitError {
   ParseParams,
   IError
}

impl<T : Default> From<T> for InitError {
    fn from(_: T) -> Self { InitError::ParseParams }
}

#[derive(Debug, PartialEq, Eq)]
enum ReceiveError {
    ParseParams,
    RError
}

impl<T : Default> From<T> for ReceiveError {
    fn from(_: T) -> Self { ReceiveError::ParseParams }
}

type SimpleCallCtx<'a> = ();

#[derive(Debug, Copy, Clone, Serial,Deserial)]
pub enum Unit<'a> {
  tt(PhantomData<&'a ()>)
}

impl<'a> Serial for &'a Unit<'a> {
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        (*self).serial(_out)
    }
}

// impl<'a> Deserial for &'a Unit<'a> {
//     fn deserial<R: Read>(_source: &mut R) -> ParseResult<Self> {
//       let v : Unit<'a> = Unit::deserial(_source)?;
//         Ok(Box::leak(Box::new(v)))
//     }
// }


#[derive(Debug, Copy, Clone)]
pub enum List<'a, A> {
  nil(PhantomData<&'a A>),
  cons(PhantomData<&'a A>, A, &'a List<'a, A>)
}

// TODO: to remove Copy, serialise the list in the same way as vector directly
impl<'a,A : Serial + Copy> Serial for List<'a,A> {
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        let mut init_v = self;
        let mut v = Vec::new();
        while let List::cons(_,hd, tl) = init_v {
            v.push(*hd);
            init_v = tl;
        }
        v.serial(_out)
    }
}

impl<'a,A : Serial + Copy> Serial for &'a List<'a,A> {
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        (*self).serial(_out)
    }
}


#[derive(Debug, Copy, Clone, Serialize, PartialEq)]
pub enum Value<'a> {
  BVal(PhantomData<&'a ()>, bool),
  ZVal(PhantomData<&'a ()>, i64)
}

impl<'a> Serial for &'a Value<'a> {
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        (*self).serial(_out)
    }
}


type Storage<'a> = &'a List<'a, &'a Value<'a>>;
// type Storage<'a> = Vec<Value<'a>>;

#[derive(Debug,Clone,Copy,Serialize,PartialEq)]
pub enum Op<'a> {
  Add(PhantomData<&'a ()>),
  Sub(PhantomData<&'a ()>),
  Mult(PhantomData<&'a ()>),
  Lt(PhantomData<&'a ()>),
  Le(PhantomData<&'a ()>),
  Equal(PhantomData<&'a ()>)
}

impl<'a> Serial for &'a Op<'a> {
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        (*self).serial(_out)
    }
}

// TODO: fix to DeserialAlloc
impl<'a> Deserial for &'a Op<'a> {
    fn deserial<R: Read>(_source: &mut R) -> ParseResult<Self> {
      let v = Op::deserial(_source)?;
        Ok(Box::leak(Box::new(v)))
    }
}


#[derive(Debug,Serialize,PartialEq,Eq,PartialOrd,Ord)]
pub enum coq_str {
    coqstr(String)
}


impl<'a> Serial for &'a coq_str {
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        (*self).serial(_out)
    }
}

// TODO: fix to DeserialAlloc
impl<'a> Deserial for &'a coq_str {
    fn deserial<R: Read>(_source: &mut R) -> ParseResult<Self> {
      let v : coq_str = coq_str::deserial(_source)?;
        Ok(Box::leak(Box::new(v)))
    }
}


#[derive(Debug,Serialize,PartialEq,Clone,Copy)]
pub enum Instruction<'a> {
  IPushZ(PhantomData<&'a ()>, i64),
  IPushB(PhantomData<&'a ()>, bool),
  IObs(PhantomData<&'a ()>, __pair<&'a coq_str, i64>),
  IIf(PhantomData<&'a ()>),
  IElse(PhantomData<&'a ()>),
  IEndIf(PhantomData<&'a ()>),
  IOp(PhantomData<&'a ()>, &'a Op<'a>)
}

impl<'a> Serial for &'a Instruction<'a> {
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        (*self).serial(_out)
    }
}

impl<'a> DeserialAlloc<'a> for &'a Instruction<'a>
{
    fn deserial_alloc<R: Read>(_source: &mut R, arena : &'a bumpalo::Bump) -> ParseResult<Self> {
        let v : Instruction = <_>::deserial(_source)?;
        Ok(my_alloc(arena,v))
    }
}


// impl<'a> Deserial for &'a Instruction<'a> {
//     fn deserial<R: Read>(_source: &mut R) -> ParseResult<Self> {
//       let v : Instruction<'a> = Instruction::deserial(_source)?;
//         Ok(Box::leak(Box::new(v)))
//     }
// }


type Ext_map<'a> = &'a immutable_map::TreeMap<(&'a coq_str,i64), Value<'a>>;


type Params<'a> = __pair<&'a List<'a, &'a Instruction<'a>>, Ext_map<'a>>;

type Action0<'a> = ();

struct Program<'a> {
  __alloc: bumpalo::Bump,
  __init: std::cell::Cell<std::option::Option<&'a dyn Fn(SimpleCallCtx<'a>) -> &'a dyn Fn(&'a Unit<'a>) -> Option<Storage<'a>>>>,
  __eqb: std::cell::Cell<std::option::Option<&'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool>>,
  __continue_: std::cell::Cell<std::option::Option<&'a dyn Fn(i64) -> bool>>,
  __lookup: std::cell::Cell<std::option::Option<&'a dyn Fn(__pair<&'a coq_str, i64>) -> &'a dyn Fn(Ext_map<'a>) -> Option<&'a Value<'a>>>>,
  __one: std::cell::Cell<std::option::Option<i64>>,
  __bool_to_cond: std::cell::Cell<std::option::Option<&'a dyn Fn(bool) -> i64>>,
  __add: std::cell::Cell<std::option::Option<&'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64>>,
  __flip: std::cell::Cell<std::option::Option<&'a dyn Fn(i64) -> i64>>,
  __leb: std::cell::Cell<std::option::Option<&'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool>>,
  __sub: std::cell::Cell<std::option::Option<&'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64>>,
  __reset_decrement: std::cell::Cell<std::option::Option<&'a dyn Fn(i64) -> i64>>,
  __mul: std::cell::Cell<std::option::Option<&'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64>>,
  __ltb: std::cell::Cell<std::option::Option<&'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool>>,
  __interp: std::cell::Cell<std::option::Option<&'a dyn Fn(Ext_map<'a>) -> &'a dyn Fn(&'a List<'a, &'a Instruction<'a>>) -> &'a dyn Fn(&'a List<'a, &'a Value<'a>>) -> &'a dyn Fn(i64) -> Option<&'a List<'a, &'a Value<'a>>>>>,
  __receive: std::cell::Cell<std::option::Option<&'a dyn Fn(Params<'a>) -> &'a dyn Fn(&'a List<'a, &'a Value<'a>>) -> Option<__pair<&'a List<'a, Action0<'a>>, Storage<'a>>>>>,
}

impl<'a> Program<'a> {
fn new() -> Self {
  Program {
    __alloc: bumpalo::Bump::new(),
    __init: std::cell::Cell::new(None),
    __eqb: std::cell::Cell::new(None),
    __continue_: std::cell::Cell::new(None),
    __lookup: std::cell::Cell::new(None),
    __one: std::cell::Cell::new(None),
    __bool_to_cond: std::cell::Cell::new(None),
    __add: std::cell::Cell::new(None),
    __flip: std::cell::Cell::new(None),
    __leb: std::cell::Cell::new(None),
    __sub: std::cell::Cell::new(None),
    __reset_decrement: std::cell::Cell::new(None),
    __mul: std::cell::Cell::new(None),
    __ltb: std::cell::Cell::new(None),
    __interp: std::cell::Cell::new(None),
    __receive: std::cell::Cell::new(None),
  }
}

fn alloc<T>(&'a self, t: T) -> &'a T {
  self.__alloc.alloc(t)
}

fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {
  self.__alloc.alloc(F)
}

fn fst<A: Copy, B: Copy>(&'a self, p: __pair<A, B>) -> A {
  __pair_elim!(
    x, y, {
      x
    },
    p)
}
fn fst__curried<A: Copy, B: Copy>(&'a self) -> &'a dyn Fn(__pair<A, B>) -> A {
  self.closure(move |p| {
    self.fst(
      p)
  })
}

fn snd<A: Copy, B: Copy>(&'a self, p: __pair<A, B>) -> B {
  __pair_elim!(
    x, y, {
      y
    },
    p)
}
fn snd__curried<A: Copy, B: Copy>(&'a self) -> &'a dyn Fn(__pair<A, B>) -> B {
  self.closure(move |p| {
    self.snd(
      p)
  })
}

fn init(&'a self, ctx: SimpleCallCtx<'a>, setup: &'a Unit<'a>) -> Option<Storage<'a>> {
  let ctx0 =
    ctx;
  let setup0 =
    setup;
  Some(
    self.alloc(
      List::nil(
        PhantomData)))
}
fn init__curried(&'a self) -> &'a dyn Fn(SimpleCallCtx<'a>) -> &'a dyn Fn(&'a Unit<'a>) -> Option<Storage<'a>> {
  self.closure(move |ctx| {
    self.closure(move |setup| {
      self.init(
        ctx,
        setup)
    })
  })
}

fn eqb(&'a self, a: i64, b: i64) -> bool { a == b }
fn eqb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.eqb(
        x,
        y)
    })
  })
}

fn continue_(&'a self, i: i64) -> bool {
  self.eqb(
    i,
    0)
}
fn continue___curried(&'a self) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |i| {
    self.continue_(
      i)
  })
}

fn lookup<V>(&'a self, key : __pair<&'a coq_str,i64> , m : &'a immutable_map::TreeMap<(&'a coq_str,i64), V>) -> Option<&'a V> {
   m.get(&key)
}
// fn lookup__curried(&'a self) -> &'a dyn Fn(__pair<&'a coq_str, i64>) -> &'a dyn Fn(Ext_map<'a>) -> Option<&'a Value<'a>> {
//   self.closure(move |k| {
//     self.closure(move |m| {
//       self.lookup(
//         k,
//         m)
//     })
//   })
// }

fn one(&'a self) -> i64 {
  __Z_frompos(
    1)
}

fn bool_to_cond(&'a self, b: bool) -> i64 {
  match b {
    true => {
      0
    },
    false => {
      self.one()
    },
  }
}
fn bool_to_cond__curried(&'a self) -> &'a dyn Fn(bool) -> i64 {
  self.closure(move |b| {
    self.bool_to_cond(
      b)
  })
}

fn add(&'a self, a: i64, b: i64) -> i64 { a.checked_add(b).unwrap() }
fn add__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |x| {
    self.closure(move |y| {
      self.add(
        x,
        y)
    })
  })
}

fn flip(&'a self, i: i64) -> i64 {
  match self.eqb(
          i,
          0) {
    true => {
      self.one()
    },
    false => {
      match self.eqb(
              i,
              self.one()) {
        true => {
          0
        },
        false => {
          i
        },
      }
    },
  }
}
fn flip__curried(&'a self) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |i| {
    self.flip(
      i)
  })
}

fn leb(&'a self, a: i64, b: i64) -> bool { a <= b }
fn leb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.leb(
        x,
        y)
    })
  })
}

fn sub(&'a self, a: i64, b: i64) -> i64 { a.checked_sub(b).unwrap() }
fn sub__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |m| {
    self.closure(move |n| {
      self.sub(
        m,
        n)
    })
  })
}

fn reset_decrement(&'a self, i: i64) -> i64 {
  match self.leb(
          i,
          self.one()) {
    true => {
      0
    },
    false => {
      self.sub(
        i,
        self.one())
    },
  }
}
fn reset_decrement__curried(&'a self) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |i| {
    self.reset_decrement(
      i)
  })
}

fn mul(&'a self, a: i64, b: i64) -> i64 { a.checked_mul(b).unwrap() }
fn mul__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |x| {
    self.closure(move |y| {
      self.mul(
        x,
        y)
    })
  })
}

fn ltb(&'a self, a: i64, b: i64) -> bool { a < b }
fn ltb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.ltb(
        x,
        y)
    })
  })
}

fn interp(&'a self, ext: Ext_map<'a>, insts: &'a List<'a, &'a Instruction<'a>>, s: &'a List<'a, &'a Value<'a>>, cond: i64) -> Option<&'a List<'a, &'a Value<'a>>> {
  match insts {
    &List::nil(_) => {
      Some(
        s)
    },
    &List::cons(_, hd, inst0) => {
      match hd {
        &Instruction::IPushZ(_, i) => {
          match self.continue_(
                  cond) {
            true => {
              self.interp(
                ext,
                inst0,
                self.alloc(
                  List::cons(
                    PhantomData,
                    self.alloc(
                      Value::ZVal(
                        PhantomData,
                        i)),
                    s)),
                cond)
            },
            false => {
              self.interp(
                ext,
                inst0,
                s,
                cond)
            },
          }
        },
        &Instruction::IPushB(_, b) => {
          match self.continue_(
                  cond) {
            true => {
              self.interp(
                ext,
                inst0,
                self.alloc(
                  List::cons(
                    PhantomData,
                    self.alloc(
                      Value::BVal(
                        PhantomData,
                        b)),
                    s)),
                cond)
            },
            false => {
              self.interp(
                ext,
                inst0,
                s,
                cond)
            },
          }
        },
        &Instruction::IObs(_, p) => {
          match self.continue_(
                  cond) {
            true => {
              match self.lookup(
                      p,
                      ext) {
                Some(v) => {
                  self.interp(
                    ext,
                    inst0,
                    self.alloc(
                      List::cons(
                        PhantomData,
                        v,
                        s)),
                    cond)
                },
                None => {
                  None
                },
              }
            },
            false => {
              self.interp(
                ext,
                inst0,
                s,
                cond)
            },
          }
        },
        &Instruction::IIf(_) => {
          match self.eqb(
                  cond,
                  0) {
            true => {
              match s {
                &List::nil(_) => {
                  None
                },
                &List::cons(_, v, s0) => {
                  match v {
                    &Value::BVal(_, b) => {
                      self.interp(
                        ext,
                        inst0,
                        s0,
                        self.bool_to_cond(
                          b))
                    },
                    &Value::ZVal(_, z) => {
                      None
                    },
                  }
                },
              }
            },
            false => {
              self.interp(
                ext,
                inst0,
                s,
                self.add(
                  self.one(),
                  cond))
            },
          }
        },
        &Instruction::IElse(_) => {
          self.interp(
            ext,
            inst0,
            s,
            self.flip(
              cond))
        },
        &Instruction::IEndIf(_) => {
          self.interp(
            ext,
            inst0,
            s,
            self.reset_decrement(
              cond))
        },
        &Instruction::IOp(_, op) => {
          match self.continue_(
                  cond) {
            true => {
              match op {
                Op::Add(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::ZVal(
                                            PhantomData,
                                            self.add(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
                Op::Sub(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::ZVal(
                                            PhantomData,
                                            self.sub(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
                Op::Mult(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::ZVal(
                                            PhantomData,
                                            self.mul(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
                Op::Lt(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::BVal(
                                            PhantomData,
                                            self.ltb(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
                Op::Le(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::BVal(
                                            PhantomData,
                                            self.leb(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
                Op::Equal(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::BVal(
                                            PhantomData,
                                            self.eqb(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
              }
            },
            false => {
              self.interp(
                ext,
                inst0,
                s,
                cond)
            },
          }
        },
      }
    },
  }
}
fn interp__curried(&'a self) -> &'a dyn Fn(Ext_map<'a>) -> &'a dyn Fn(&'a List<'a, &'a Instruction<'a>>) -> &'a dyn Fn(&'a List<'a, &'a Value<'a>>) -> &'a dyn Fn(i64) -> Option<&'a List<'a, &'a Value<'a>>> {
  self.closure(move |ext| {
    self.closure(move |insts| {
      self.closure(move |s| {
        self.closure(move |cond| {
          self.interp(
            ext,
            insts,
            s,
            cond)
        })
      })
    })
  })
}

fn receive(&'a self, p: Params<'a>, s: &'a List<'a, &'a Value<'a>>) -> Option<__pair<&'a List<'a, Action0<'a>>, Storage<'a>>> {
  let s0 =
    s;
  match self.interp(
          self.snd(
            p),
          self.fst(
            p),
          self.alloc(
            List::nil(
              PhantomData)),
          0) {
    Some(v) => {
      Some(
        __mk_pair(
          self.alloc(
            List::nil(
              PhantomData)),
          v))
    },
    None => {
      None
    },
  }
}
    fn receive__curried(&'a self) -> &'a dyn Fn(Params<'a>) -> &'a dyn Fn(&'a List<'a, &'a Value<'a>>) -> Option<__pair<&'a List<'a, Action0<'a>>, Storage<'a>>> {
  self.closure(move |p| {
    self.closure(move |s| {
      self.receive(
        p,
        s)
    })
  })
}
    // fn of_arr<A> (&'a self, insts : &'a [Value<'a>]) -> List<'a,A>
    // {
    //     let mut res : List<'a,A> = List::nil(PhantomData);
    //     for i in insts.iter()
    //     {
    //         let x : A = Value::deserial()?;
    //         res = List::cons(PhantomData,x)
    //     }
    //     res
    // }
    fn val_list_to_vec_aux (&'a self, res : &'a mut Vec<Value<'a>>, insts : &'a List<'a,&'a Value<'a>>) -> Vec<Value<'a>>
    {  match insts {
        List::nil(_) => res.to_vec(),
        List::cons(_,v,vs) => {
            res.push(**v);
            self.val_list_to_vec_aux(res,vs)
        }

    }}

    // fn val_list_to_vec_aux_mut (&'a self, insts : &'a List<'a,&'a Value<'a>>, res : &'a mut Vec<Value<'a>>)
    // {  match insts {
    //     List::nil(_) => return,
    //     List::cons(_,v,vs) => {
    //         res.push(**v);
    //         self.val_list_to_vec_aux(res,vs);
    //     }

    // }}


    // fn val_list_to_vec (&'a self, insts : &'a List<'a,&'a Value<'a>>) -> &'a Vec<Value<'a>> {
    //     let init = self.alloc(Vec::new_in(&self.__alloc));
    //     self.val_list_to_vec_aux_mut(insts,init);
    //     init
    // }

    fn vec_to_list<A> (&'a self, insts : &'a Vec<A>) -> &'a List<'a,&'a A> {
        let mut v = self.__alloc.alloc(List::nil(PhantomData));
        for i in insts.iter() {
            v = self.__alloc.alloc(List::cons(PhantomData,i,v));
        }
        v
    }

    // fn to_immutable_map (&'a self, m : &'a BTreeMap<(&'a coq_str,i64),Value<'a>>) -> &'a immutable_map::TreeMap<(&'a coq_str,i64),Value<'a>> {
    //     let mut res = self.__alloc.alloc(immutable_map::TreeMap::new());
    //     for (k,v) in m.iter() {
    //         *res = res.insert(*k,*v);
    //     }
    //     res
    // }
    fn ex1(&'a self) -> &'a List<'a, &'a Instruction<'a>> {
  self.alloc(
    List::cons(
      PhantomData,
      self.alloc(
        Instruction::IPushZ(
          PhantomData,
          __Z_frompos(
            1))),
      self.alloc(
        List::cons(
          PhantomData,
          self.alloc(
            Instruction::IPushZ(
              PhantomData,
              __Z_frompos(
                1))),
          self.alloc(
            List::cons(
              PhantomData,
              self.alloc(
                Instruction::IOp(
                  PhantomData,
                  self.alloc(
                    Op::Add(
                      PhantomData)))),
              self.alloc(
                List::nil(
                  PhantomData))))))))
    }
}

pub trait DeserialAlloc<'a>: Sized {
    fn deserial_alloc<R: Read>(_source: &mut R, arena : &'a bumpalo::Bump) -> ParseResult<Self>;
}

fn vec_to_list_arena<'a,A> (arena : &'a bumpalo::Bump, insts : &'a Vec<A>) -> &'a List<'a,&'a A> {
    let mut v = arena.alloc(List::nil(PhantomData));
    for i in insts.iter() {
        v = arena.alloc(List::cons(PhantomData,i,v));
    }
    v
}

fn my_alloc<T>(arena : &bumpalo::Bump, t: T) -> &T {
    arena.alloc(t)
}

fn deserial_list_arena<'a,A : Deserial, R : Read> (_source : &mut R, arena : &'a bumpalo::Bump) -> ParseResult<&'a List<'a,&'a A>> {
    let mut v : Vec<A> = Vec::deserial(_source)?;
    let mut l = my_alloc(arena,List::nil(PhantomData));
    v.reverse();
    for a in v {
        let alloc_a = my_alloc(arena,a);
        l = my_alloc(arena,List::cons(PhantomData, alloc_a, l))
        }
    Ok(l)
}

fn deserial_arena<'a,A : Deserial, R : Read> (_source : &mut R, arena : &'a bumpalo::Bump) -> ParseResult<&'a A> {
    let v : A = A::deserial(_source)?;
    Ok(my_alloc(arena,v))
}

impl<'a> DeserialAlloc<'a> for &'a Unit<'a>
{
    fn deserial_alloc<R: Read>(_source: &mut R, arena : &'a bumpalo::Bump) -> ParseResult<Self> {
        let v : Unit = <_>::deserial(_source)?;
        Ok(my_alloc(arena,v))
    }
}

impl<'a, K : Deserial + Ord + Clone, V : Deserial + Clone> DeserialAlloc<'a> for &'a TreeMap<K,V>
{
    fn deserial_alloc<R: Read>(_source: &mut R, arena : &'a bumpalo::Bump) -> ParseResult<Self> {
        let m : BTreeMap<K,V> = BTreeMap::deserial(_source)?;
        let m0 : TreeMap<K,V> = TreeMap::new();
        for (k,v) in m {
            m0.insert(k,v);
        }
        Ok(my_alloc(arena,m0))
    }
}

impl<'a, X : DeserialAlloc<'a>, Y : DeserialAlloc<'a>> DeserialAlloc<'a> for (X,Y)
{
    fn deserial_alloc<R: Read>(_source: &mut R, arena : &'a bumpalo::Bump) -> ParseResult<Self> {
        let x = X::deserial_alloc(_source,arena)?;
        let y = Y::deserial_alloc(_source,arena)?;
        Ok((x,y))
    }
}


impl<'a,A : Deserial> DeserialAlloc<'a> for &'a List<'a,&'a A>
{
    fn deserial_alloc<R: Read>(_source: &mut R, arena : &'a bumpalo::Bump) -> ParseResult<Self> {
        deserial_list_arena(_source,arena)
    }
}

type Ext_map0<'a> = BTreeMap<(&'a coq_str,i64), Value<'a>>;

#[init(contract = "interpreter",  enable_logger, low_level)]
fn contract_init<StateError:Default>(ctx: &impl HasInitContext<()>,
                     logger: &mut impl HasLogger,
                     state: &mut impl HasContractState<StateError>) ->  Result<(), InitError>  {
    let prg = Program::new();
    let params = <_>::deserial_alloc(&mut ctx.parameter_cursor(),&prg.__alloc)?;
    logger.log(&params);
    // call init
    let res = prg.init((),params);
    match res {
        Option::Some(init_v) => {
            init_v.serial(state)?;
            Ok(())
        },
        Option::None => Err(InitError::IError)
    }
}

#[receive(contract = "interpreter", name = "contract_receive", payable, enable_logger, low_level)]
fn contract_receive<A: HasActions,StateError: Default>(
    ctx: &impl HasReceiveContext<()>,
    amount: Amount,
    logger: &mut impl HasLogger,
    state: &mut impl HasContractState<StateError>)
    -> Result<A,ReceiveError> {
    let prg = Program::new();
    let msg : Params = <_>::deserial_alloc(&mut ctx.parameter_cursor(),&prg.__alloc)?;
    let state0 : State = <_>::deserial_alloc(state,&prg.__alloc)?;
    state.seek(SeekFrom::Start(0))?;
    let res = prg.receive(msg,state0);
    match res {
        Option::Some((_,res)) =>{
            res.serial(state)?;
            Ok(A::accept())},
        Option::None => Err(ReceiveError::RError)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use concordium_std::test_infrastructure::*;

    #[test]
    fn test_serial() {
        let data = Vec::new();
        let mut st = ContractStateTest::open(data);
        let blah : u8 = 100;
        blah.serial(&mut st).expect("Serialisation of blah failed");
    }

    #[test]
    fn test_bool_serial_deserial() {
        let data = Vec::new();
        println!("Initial vector {:?}",data);
        let mut st = ContractStateTest::open(data);
        let v : bool = true;
        v.serial(&mut st).expect("Serialisation of bool failed");
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        let p = st.read(&mut [1]);
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        println!("After serialisation: {:?}", p);
        let deserial_v : bool = bool::deserial(&mut st).expect("De-serialisation of bool failed");
        claim_eq!(deserial_v, v);
    }


    #[test]
    fn test_val_serial_deserial() {
        let data = Vec::new();
        let mut st = ContractStateTest::open(data);
        let blah : Value = Value::BVal(PhantomData,true);
        blah.serial(&mut st).expect("Serialisation of val failed");
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        let deserial_blah : Value = <_>::deserial(&mut st).expect("De-serialisation of val failed");
        claim_eq!(deserial_blah, blah);
    }

    #[test]
    fn test_vec_serial_deserial() {
        let data = Vec::new();
        let mut st = ContractStateTest::open(data);
        let val : Value = Value::BVal(PhantomData,true);
        let v = vec![val];
        v.serial(&mut st).expect("Serialisation of vec blah failed");
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        let deserial_v : Vec<Value> = <_>::deserial(&mut st).expect("De-serialisation of vec blah failed");
        println!("Deserialised vector of values: {:?}", deserial_v);
        claim_eq!(deserial_v, v);
    }

    #[test]
    fn test_vec_serial_deserial_as_list() {
        let data = Vec::new();
        let mut st = ContractStateTest::open(data);
        let val : Value = Value::BVal(PhantomData,true);
        let v = vec![val];
        v.serial(&mut st).expect("Serialisation of vec blah failed");
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        let mut arena = bumpalo::Bump::new();
        let deserial_v : &List<&Value> = <_>::deserial_alloc(&mut st,&mut arena).expect("De-serialisation of vec blah failed");
        println!("Deserialised list of values: {:?}", *deserial_v);
        let ok_res = if let List::cons(PhantomData, &Value::BVal(PhantomData,true), List::nil(PhantomData)) = deserial_v { true } else { false };
        claim!(ok_res, "Wrong deserialisation result");
    }


    #[test]
    fn test_params_serial_deserial() {
        let data = Vec::new();
        let mut st = ContractStateTest::open(data);
        let prg = Program::new();
        let data : Vec<u8> = Vec::new();
        let mut start_vec = Vec::new();
        let mut start_list = prg.ex1();
        while let List::cons(_,hd, tl) = start_list {
            start_vec.push(**hd);
            start_list = tl;
        }
        let v : (_, BTreeMap<&coq_str,i64>) = (prg.ex1(), BTreeMap::new());
        v.serial(&mut st).expect("Serialisation of params failed");
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        let arena = bumpalo::Bump::new();
        let deserial_v : Params = <_>::deserial_alloc(&mut st,&arena).expect("De-serialisation of params failed");
        claim_eq!(deserial_v.1.len(), 0);
        let mut deserial_vec = Vec::new();
        let mut deserial_list = deserial_v.0;
        while let List::cons(_,hd, tl) = deserial_list {
            deserial_vec.push(**hd);
            deserial_list = tl;
        }
        claim_eq!(deserial_vec, start_vec);
    }
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use concordium_std::test_infrastructure::*;

    #[concordium_test]
    fn test_init() {
        // Setup our example state the contract is to be run in.
        // First the context.
        let INIT_VALUE = Unit::tt(PhantomData);
        let data = Vec::new();
        let mut st = ContractStateTest::open(data);
        let mut v : Vec<Value> = Vec::new();
        let bval = Value::BVal(PhantomData,true);
        v.push(bval);
        v.serial(&mut st).expect("Serialisation of failed");
        let mut ctx = InitContextTest::empty();
        let param_bytes = to_bytes(&INIT_VALUE);
        ctx.set_parameter(&param_bytes);


        // set up the logger so we can intercept and analyze them at the end.
        let mut logger = LogRecorder::init();

        // call the init function
        let out = contract_init(&ctx, &mut logger, &mut st);

        // and inspect the result.
        let res = match out {
            Ok(res) => res,
            Err(_) => fail!("Contract initialization failed."),
        };
        claim_eq!(res, ());
        let arena = bumpalo::Bump::new();
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        let deserial_state : State = <_>::deserial_alloc(&mut st, &arena).expect("Deserialisation failed");
        let ok_res = if let List::cons(PhantomData, &Value::BVal(PhantomData,true), List::nil(PhantomData)) = deserial_state { true } else { false };
        claim!(ok_res, "Wrong deserialisation result");
    }

    #[concordium_test]
    fn test_receive() {
        let mut ctx = ReceiveContextTest::empty();
        let prg = Program::new();
        let mut data : Vec<u8> = Vec::new();
        let params : (_, BTreeMap<&coq_str,i64>) = (prg.ex1(), BTreeMap::new());
        params.serial(&mut data).expect("Serialisation failed");
        ctx.set_parameter(&data);
        let data_st : Vec<u8> = Vec::new();
        let mut st = ContractStateTest::open(data_st);
        let v : List<&Value> = List::nil(PhantomData);
        v.serial(&mut st).expect("Serialisation of failed");
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        // set up the logger so we can intercept and analyze them at the end.
        let mut logger = LogRecorder::init();
        let res: Result<ActionsTree, _> =
            contract_receive(&ctx, Amount::from_micro_gtu(11), &mut logger, &mut st);
        let actions = match res {
            Err(e) => fail!("Contract receive failed, but it should not have: {:?}",e),
            Ok(actions) => actions,
        };
        claim_eq!(actions, ActionsTree::Accept, "Contract receive produced incorrect actions.");
        let arena = bumpalo::Bump::new();
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        let deserial_state : State = <_>::deserial_alloc(&mut st, &arena).expect("Deserialisation failed");
        let ok_res = if let List::cons(PhantomData, &Value::ZVal(PhantomData,2), List::nil(PhantomData)) = deserial_state { true } else { false };
        claim!(ok_res, "Wrong deserialisation result: {:?}", deserial_state);
    }
}
