From Coq Require Import Arith.
From Coq Require Import Extraction.
From Coq Require Import NArith.
From Coq Require Import PArith.
From Coq Require Import ZArith.

Extract Inductive nat => "u64" ["0" "__nat_succ"] "__nat_elim!".
Extract Inductive positive => "u64" ["__pos_onebit" "__pos_zerobit" "1"] "__pos_elim!".
Extract Inductive N => "u64" ["0" "__N_frompos"] "__N_elim!".
Extract Inductive Z => "i64" ["0" "__Z_frompos" "__Z_fromneg"] "__Z_elim!".
Extract Inductive comparison =>
  "std::cmp::Ordering"
    ["std::cmp::Ordering::Equal"
     "std::cmp::Ordering::Less"
     "std::cmp::Ordering::Greater"].

Extract Constant BinPosDef.Pos.add => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a + b }".
Extract Constant BinPosDef.Pos.succ => "fn ##name##(&'a self, a: u64) -> u64 { a + 1 }".
Extract Constant BinPosDef.Pos.pred => "fn ##name##(&'a self, a: u64) -> u64 { a - 1 }".
Extract Constant BinPosDef.Pos.sub => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a - b }".
Extract Constant BinPosDef.Pos.mul => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a * b }".
Extract Constant BinPosDef.Pos.min => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::min(a, b) }".
Extract Constant BinPosDef.Pos.max => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::max(a, b) }".
Extract Constant BinPosDef.Pos.eqb => "fn ##name##(&'a self, a: u64, b: u64) -> bool { a == b }".
Extract Constant BinPosDef.Pos.compare =>
"fn ##name##(&'a self, a: u64, b: u64) -> std::cmp::Ordering {
  a.cmp(&b)
}".
Extract Constant BinPosDef.Pos.compare_cont =>
"fn ##name##(&'a self, cont: std::cmp::Ordering, a: u64, b: u64) -> std::cmp::Ordering {
  if a < b then
    std::cmp::Ordering::Less
  else if a == b then
    cont
  else
    std::cmp::Ordering::Greater".

Extract Constant BinNatDef.N.add => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a + b }".
Extract Constant BinNatDef.N.succ => "fn ##name##(&'a self, a: u64) -> u64 { a + 1 }".
Extract Constant BinNatDef.N.pred => "fn ##name##(&'a self, a: u64) -> u64 { a - 1 }".
Extract Constant BinNatDef.N.sub => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a - b }".
Extract Constant BinNatDef.N.mul => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a * b }".
Extract Constant BinNatDef.N.div => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a / b }".
Extract Constant BinNatDef.N.modulo => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a % b }".
Extract Constant BinNatDef.N.min => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::min(a, b) }".
Extract Constant BinNatDef.N.max => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::max(a, b) }".
Extract Constant BinNatDef.N.eqb => "fn ##name##(&'a self, a: u64, b: u64) -> bool { a == b }".
Extract Constant BinNatDef.N.compare =>
"fn ##name##(&'a self, a: u64, b: u64) -> std::cmp::Ordering { a.cmp(&b) }".

Extract Constant BinIntDef.Z.add => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a + b }".
Extract Constant BinIntDef.Z.succ => "fn ##name##(&'a self, a: i64) -> i64 { a + 1 }".
Extract Constant BinIntDef.Z.pred => "fn ##name##(&'a self, a: i64) -> i64 { a - 1 }".
Extract Constant BinIntDef.Z.sub => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a - b }".
Extract Constant BinIntDef.Z.mul => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a * b }".
Extract Constant BinIntDef.Z.opp => "fn ##name##(&'a self, a: i64) -> i64 { -a }".
Extract Constant BinIntDef.Z.min => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { std::cmp::min(a, b) }".
Extract Constant BinIntDef.Z.max => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { std::cmp::max(a, b) }".
Extract Constant BinIntDef.Z.eqb => "fn ##name##(&'a self, a: i64, b: i64) -> bool { a == b }".
(* TODO: div and modulo are nontrivial since Coq rounds towards negative infinity *)
(*Extract ConstanBinIntDef.t Z.div => "fn ##name##(a: i64, b: i64) -> i64 { a.checked_div(b).unwrap_or(0) }".
Extract Constant BinIntDef.Z.modulo => "fn ##name##(a: i64, b: i64) -> i64 { a.checked_rem(b).unwrap_or(a) }".*)
Extract Constant BinIntDef.Z.compare =>
"fn ##name##(&'a self, a: i64, b: i64) -> std::cmp::Ordering { a.cmp(&b) }".
Extract Constant BinIntDef.Z.of_N =>
"fn ##name##(&'a self, a: u64) -> i64 {
  use std::convert::TryFrom;
  i64::try_from(a).unwrap()
}".
Extract Constant BinIntDef.Z.abs_N => "fn ##name#(&'a self, a: i64) -> u64 { a.unsigned_abs() }".
