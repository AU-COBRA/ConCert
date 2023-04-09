From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.

From MetaCoq.Template Require Import All.
From MetaCoq.Common Require Import Kernames.
From RustExtraction Require Import StringExtra.
From ConCert.Execution Require Monad.
From ConCert.Execution Require Import Blockchain.
From RustExtraction Require Import Common.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import Optimize.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure.Typed Require Import Utils.
From RustExtraction Require Import RustExtract.
From ConCert.Extraction Require Import SpecializeChainBase.
From RustExtraction Require Import PrettyPrinterMonad.
From RustExtraction Require Import Printing.

Import MCMonadNotation.

Local Open Scope string_scope.
Local Notation bs_to_s := bytestring.String.to_string.
Local Notation s_to_bs := bytestring.String.of_string.

Local Coercion bytestring.String.of_string : String.string >-> bytestring.string.


Module ConcordiumRemap.

Definition lookup_const (TT : list (kername * bytestring.string))
                        (name : kername)
                        : option bytestring.string :=
  match find (fun '(key, _) => eq_kername key name) TT with
  | Some (_, val) => Some val
  | None => None
  end.

Open Scope bs_scope.

Definition remap (kn : kername) (new_name : string) := (kn, new_name).

Definition remap_pos_arith : list (kername * bytestring.string) :=
  [ remap <%% Pos.succ %%> "fn ##name##(&'a self, a: u64) -> u64 { a.checked_add(1).unwrap() }" ;
    remap <%% Pos.pred %%> "fn ##name##(&'a self, a: u64) -> u64 { if a == 1 { 1 } else { a.checked_sub(1).unwrap() } }" ;
    remap <%% Pos.add %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_add(b).unwrap() }" ;
    remap <%% Pos.sub %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { if a <= b { 1 } else { a.checked_sub(b).unwrap() } }" ;
    remap <%% Pos.mul %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_mul(b).unwrap() }" ;
    remap <%% Pos.eqb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a == b }" ;
    remap <%% Pos.leb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a <= b }" ;
    remap <%% Pos.ltb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a < b }" ;
    remap <%% Pos.min %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::min(a, b) }" ;
    remap <%% Pos.max %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::max(a, b) }"
  ].

Definition remap_nat_arith : list (kername * string) :=
  [ remap <%% Nat.succ %%> "fn ##name##(&'a self, a: u64) -> u64 { a.checked_add(1).unwrap() }" ;
    remap <%% Nat.pred %%> "fn ##name##(&'a self, a: u64) -> u64 { a.checked_sub(1).unwrap_or(0) }" ;
    remap <%% Nat.add %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_add(b).unwrap() }" ;
    remap <%% Nat.sub %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_sub(b).unwrap() }" ;
    remap <%% Nat.mul %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_mul(b).unwrap() }" ;
    remap <%% Nat.div %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_div(b).unwrap_or(0) }" ;
    remap <%% Nat.modulo %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { if b == 0 { 0 } else { a.checked_rem(b).unwrap() } }" ;
    remap <%% Nat.eqb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a == b }" ;
    remap <%% Nat.leb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a <= b }" ;
    remap <%% Nat.ltb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a < b }" ;
    remap <%% Nat.min %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::min(a, b) }" ;
    remap <%% Nat.max %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::max(a, b) }" ;
    remap <%% Nat.even %%> "fn ##name##(&'a self, a: u64) -> bool { a.checked_rem(2).unwrap() == 0 }" ;
    remap <%% Nat.odd %%> "fn ##name##(&'a self, a: u64) -> bool { a.checked_rem(2).unwrap() != 0 }"
  ].

Definition remap_N_arith : list (kername * string) :=
  [ remap <%% N.succ %%> "fn ##name##(&'a self, a: u64) -> u64 { a.checked_add(1).unwrap() }" ;
    remap <%% N.pred %%> "fn ##name##(&'a self, a: u64) -> u64 { a.checked_sub(1).unwrap_or(0) }" ;
    remap <%% N.add %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_add(b).unwrap() }" ;
    remap <%% N.sub %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_sub(b).unwrap() }" ;
    remap <%% N.mul %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_mul(b).unwrap() }" ;
    remap <%% N.div %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_div(b).unwrap_or(0) }" ;
    remap <%% N.modulo %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { if b == 0 { 0 } else { a.checked_rem(b).unwrap() } }" ;
    remap <%% N.eqb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a == b }" ;
    remap <%% N.leb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a <= b }" ;
    remap <%% N.ltb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a < b }" ;
    remap <%% N.min %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::min(a, b) }" ;
    remap <%% N.max %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::max(a, b) }" ;
    remap <%% N.even %%> "fn ##name##(&'a self, a: u64) -> bool { a.checked_rem(2).unwrap() == 0 }" ;
    remap <%% N.odd %%> "fn ##name##(&'a self, a: u64) -> bool { a.checked_rem(2).unwrap() != 0 }"
  ].

Definition remap_Z_arith : list (kername * string) :=
  [ remap <%% Z.succ %%> "fn ##name##(&'a self, a: i64) -> i64 { a.checked_add(1).unwrap() }" ;
    remap <%% Z.pred %%> "fn ##name##(&'a self, a: i64) -> i64 { a.checked_sub(1).unwrap() }" ;
    remap <%% Z.add %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_add(b).unwrap() }" ;
    remap <%% Z.sub %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_sub(b).unwrap() }" ;
    remap <%% Z.mul %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_mul(b).unwrap() }" ;
    (* TODO: add div and mod once `div_floor` becomes stable feature https://github.com/rust-lang/rust/issues/88581 *)
    (* remap <%% Z.div %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if b == 0 { 0 } else { a.div_floor(b) } }" ; *)
    (* remap <%% Z.modulo %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if b == 0 { 0 } else { a.checked_rem_euclid(b).unwrap() } }" ; *)
    remap <%% Z.eqb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a == b }" ;
    remap <%% Z.leb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a <= b }" ;
    remap <%% Z.ltb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a < b }" ;
    remap <%% Z.geb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a >= b }" ;
    remap <%% Z.gtb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a > b }" ;
    remap <%% Z.min %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { std::cmp::min(a, b) }" ;
    remap <%% Z.max %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { std::cmp::max(a, b) }" ;
    remap <%% Z.even %%> "fn ##name##(&'a self, a: i64) -> bool { a.checked_rem(2).unwrap() == 0 }" ;
    remap <%% Z.odd %%> "fn ##name##(&'a self, a: i64) -> bool { a.checked_rem(2).unwrap() != 0 }" ;
    remap <%% Z.opp %%> "fn ##name##(&'a self, a: i64) -> i64 { a.checked_neg().unwrap() }" ;
    remap <%% Z.abs_N %%> "fn ##name#(&'a self, a: i64) -> u64 { a.unsigned_abs() }" ;
    remap <%% Z.of_N %%>
"fn ##name##(&'a self, a: u64) -> i64 {
  use std::convert::TryFrom;
  i64::try_from(a).unwrap()
}" ;
    remap <%% Z.to_N %%> "fn ##name##(&'a self, a: i64) -> u64 { if a.is_negative() { 0 } else { a.unsigned_abs() } }"
  ].

Definition remap_arith : list (kername * string) :=
  remap_pos_arith ++
  remap_nat_arith ++
  remap_N_arith ++
  remap_Z_arith.

Definition remap_blockchain_consts : list (kername * string) :=
  [ remap <! @Address !> "type ##name##<'a> = concordium_std::Address;"
  (* Ideally we would have two impls here for performance, but Rust does not support this.
     https://github.com/rust-lang/rust/issues/62223 *)
  ; remap <! @address_eqb !>
          "fn ##name##(&'a self) -> impl Fn(concordium_std::Address) -> &'a dyn Fn(concordium_std::Address) -> bool { move |a| self.alloc(move |b| a == b) }" ].

Definition remap_inline_bool_ops := Eval compute in
  [ remap <%% andb %%> "__andb!"
  ; remap <%% orb %%> "__orb!" ].

Definition remap_nat : remapped_inductive :=
  {| re_ind_name := "u64";
     re_ind_ctors := ["0"; "__nat_succ"];
     re_ind_match := Some "__nat_elim!"
  |}.

Definition remap_N : remapped_inductive :=
  {| re_ind_name := "u64";
     re_ind_ctors := ["0"; "__N_frompos"];
     re_ind_match := Some "__N_elim!"
  |}.

Definition remap_positive : remapped_inductive :=
  {| re_ind_name := "u64";
     re_ind_ctors := ["__pos_onebit"; "__pos_zerobit"; "1"];
     re_ind_match := Some "__pos_elim!"
  |}.

Definition remap_Z : remapped_inductive :=
  {| re_ind_name := "i64";
     re_ind_ctors := ["0"; "__Z_frompos"; "__Z_fromneg"];
     re_ind_match := Some "__Z_elim!";
  |}.

Definition remap_bool : remapped_inductive :=
  {| re_ind_name := "bool";
     re_ind_ctors := ["true"; "false"];
     re_ind_match := None
  |}.

Definition remap_pair : remapped_inductive :=
  {| re_ind_name := "__pair";
     re_ind_ctors := ["__mk_pair"];
     re_ind_match := Some "__pair_elim!"
  |}.

Definition remap_option : remapped_inductive :=
  {| re_ind_name := "Option";
     re_ind_ctors := ["Some"; "None"];
     re_ind_match := None
  |}.

Definition remap_result : remapped_inductive :=
  {| re_ind_name := "Result";
     re_ind_ctors := ["Ok"; "Err"];
     re_ind_match := None
  |}.

Definition remap_unit : remapped_inductive :=
  {| re_ind_name := "()";
     re_ind_ctors := ["()"];
     re_ind_match := None
  |}.

Definition remap_string : remapped_inductive :=
  {| re_ind_name := "&'a String";
     re_ind_ctors := [];
     re_ind_match := None
  |}.

Definition remap_std_types :=
  [ (<! nat !>, remap_nat)
  ; (<! positive !>, remap_positive)
  ; (<! Z !>, remap_Z)
  ; (<! N !>, remap_N)
  ; (<! bool !>, remap_bool)
  ; (<! prod !>, remap_pair)
  ; (<! option !>, remap_option)
  ; (<! ConCert.Execution.ResultMonad.result !>, remap_result)
  ; (<! unit !>, remap_unit)
  ; (<! String.string !>, remap_string) ].

Definition remap_SerializedValue : remapped_inductive :=
  {| re_ind_name := "&'a SerializedValue<'a>";
     re_ind_ctors := ["__SerializedValue__Is__Opaque"];
     re_ind_match := None
  |}.

Definition remap_ActionBody : remapped_inductive :=
  {| re_ind_name := "ActionBody<'a>";
     re_ind_ctors := ["ActionBody::Transfer"; "ActionBody::Call"; "__Deploy__Is__Not__Supported"];
     re_ind_match := None
  |}.

Definition remap_blockchain_inductives : list (inductive * remapped_inductive) :=
  [ (<! Serializable.SerializedValue !>, remap_SerializedValue);
    (<! @ActionBody !>, remap_ActionBody)
  ].

Definition ignored_concert :=
  [ <%% Monad.Monad %%> ;
    <%% @RecordSet.SetterFromGetter %%>
  ].

Definition lookup_inductive
           (TT_inductives : list (inductive * remapped_inductive))
           (ind : inductive) : option remapped_inductive :=
  match find (fun '(key, _) => eq_inductive key ind) TT_inductives with
  | Some (_, val) => Some val
  | None => None
  end.

Definition build_remaps
           (TT_const : list (kername * string))
           (TT_const_inline : list (kername * string))
           (TT_inductives : list (inductive * remapped_inductive))
          : remaps :=
  {| remap_inductive := lookup_inductive TT_inductives;
     remap_constant := lookup_const TT_const;
     remap_inline_constant := lookup_const TT_const_inline;
  |}.

End ConcordiumRemap.

Module ConcordiumPreamble.
  Local Instance concordium_extract_preamble : Preamble :=
{| top_preamble := [
"#![allow(dead_code)]";
"#![allow(unused_imports)]";
"#![allow(unused_variables)]";
"#![allow(non_camel_case_types)]";
"#![allow(non_snake_case)]";
 "";
"use concordium_std::*;";
"use concert_std::{ActionBody, ConCertDeserial, ConCertSerial, SerializedValue};";
"use core::marker::PhantomData;";
"use immutable_map::TreeMap;";
"use std::convert::TryFrom;";
"";
"fn __nat_succ(x: u64) -> u64 {";
"  x.checked_add(1).unwrap()";
"}";
"";
"macro_rules! __nat_elim {";
"    ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {";
"        { let v = $val;";
"        if v == 0 { $zcase } else { let $pred = v - 1; $scase } }";
"    }";
"}";
"";
"macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }";
"macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }";
"";
"fn __pos_onebit(x: u64) -> u64 {";
"  x.checked_mul(2).unwrap() + 1";
"}";
"";
"fn __pos_zerobit(x: u64) -> u64 {";
"  x.checked_mul(2).unwrap()";
"}";
"";
"macro_rules! __pos_elim {";
"    ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {";
"        {";
"            let n = $val;";
"            if n == 1 {";
"                $onecase";
"            } else if (n & 1) == 0 {";
"                let $p2 = n >> 1;";
"                $zerobcase";
"            } else {";
"                let $p = n >> 1;";
"                $onebcase";
"            }";
"        }";
"    }";
"}";
"";
"fn __Z_frompos(z: u64) -> i64 {";
"  use std::convert::TryFrom;";
"";
"  i64::try_from(z).unwrap()";
"}";
"";
"fn __Z_fromneg(z : u64) -> i64 {";
"  use std::convert::TryFrom;";
"";
"  i64::try_from(z).unwrap().checked_neg().unwrap()";
"}";
"";
"macro_rules! __Z_elim {";
"    ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {";
"        {";
"            let n = $val;";
"            if n == 0 {";
"                $zero_case";
"            } else if n < 0 {";
"                let $p2 = n.unsigned_abs();";
"                $neg_case";
"            } else {";
"                let $p = n as u64;";
"                $pos_case";
"            }";
"        }";
"    }";
"}";
"";
"fn __N_frompos(z: u64) -> u64 {";
"  z";
"}";
"";
"macro_rules! __N_elim {";
"    ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {";
"        { let $p = $val; if $p == 0 { $zero_case } else { $pos_case } }";
"    }";
"}";
"";
"type __pair<A, B> = (A, B);";
"";
"macro_rules! __pair_elim {";
"    ($fst:ident, $snd:ident, $body:expr, $p:expr) => {";
"        { let ($fst, $snd) = $p; $body }";
"    }";
"}";
"";
"fn __mk_pair<A: Copy, B: Copy>(a: A, b: B) -> __pair<A, B> { (a, b) }";
"";
"fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {";
"  f";
"}";
"";
"#[derive(Debug, PartialEq, Eq)]";
"enum InitError {";
"   DeserialParams,";
"   SerialParams,";
"   Error(u64)";
"}";
"";
"impl From<InitError> for Reject {";
"    fn from(err: InitError) -> Self {";
"        let error_code = match err {";
"            InitError::DeserialParams => unsafe {";
"                crate::num::NonZeroI32::new_unchecked(-42000001)";
"            },";
"            InitError::SerialParams => unsafe {";
"                crate::num::NonZeroI32::new_unchecked(-42000002)";
"            },";
"            InitError::Error(error) => unsafe {";
"              match i32::try_from(error).ok() {";
"                Option::Some(0) => {";
"                  crate::num::NonZeroI32::new_unchecked(i32::MIN)";
"                },";
"                Option::Some(v) => {";
"                  crate::num::NonZeroI32::new_unchecked(v)";
"                },";
"                Option::None => {";
"                  crate::num::NonZeroI32::new_unchecked(i32::MIN)";
"                }";
"              }";
"            }";
"        };";
"        Self {";
"            error_code";
"        }";
"    }";
"}";
"";
"#[derive(Debug, PartialEq, Eq)]";
"enum ReceiveError {";
"    DeserialMsg,";
"    DeserialOldState,";
"    SerialNewState,";
"    ConvertActions, // Cannot convert ConCert actions to Concordium actions";
"    Error(u64)";
"}";
"";
"impl From<ReceiveError> for Reject {";
"    fn from(err: ReceiveError) -> Self {";
"        let error_code = match err {";
"            ReceiveError::DeserialMsg => unsafe {";
"                crate::num::NonZeroI32::new_unchecked(-42000001)";
"            },";
"            ReceiveError::DeserialOldState => unsafe {";
"                crate::num::NonZeroI32::new_unchecked(-42000002)";
"            },";
"            ReceiveError::SerialNewState => unsafe {";
"                crate::num::NonZeroI32::new_unchecked(-42000003)";
"            },";
"            ReceiveError::ConvertActions => unsafe {";
"                crate::num::NonZeroI32::new_unchecked(-42000004)";
"            },";
"            ReceiveError::Error(error) => unsafe {";
"              match i32::try_from(error).ok() {";
"                Option::Some(0) => {";
"                  crate::num::NonZeroI32::new_unchecked(i32::MIN)";
"                },";
"                Option::Some(v) => {";
"                  crate::num::NonZeroI32::new_unchecked(v)";
"                },";
"                Option::None => {";
"                  crate::num::NonZeroI32::new_unchecked(i32::MIN)";
"                }";
"              }";
"            }";
"        };";
"        Self {";
"            error_code";
"        }";
"    }";
"}"
];
program_preamble := [
"fn alloc<T>(&'a self, t: T) -> &'a T {";
"  self.__alloc.alloc(t)";
"}";
"";
"fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {";
"  self.__alloc.alloc(F)";
"}" ] |}.

End ConcordiumPreamble.

Import ConcordiumRemap.

Record ConcordiumMod (init_type receive_type : Type) :=
  { concmd_contract_name : string ;
    concmd_init : init_type;
    concmd_receive : receive_type;
    concmd_extra : list ({T : Type & T}); }.

Arguments concmd_contract_name {_ _}.
Arguments concmd_init {_ _}.
Arguments concmd_receive {_ _}.
Arguments concmd_extra {_ _}.

Definition get_fn_arg_type (Σ : Ex.global_env) (fn_name : kername) (n : nat)
  : result Ex.box_type string :=
  match Ex.lookup_env Σ fn_name with
  | Some (Ex.ConstantDecl cb) =>
    match decompose_TArr cb.(Ex.cst_type).2 with
    | (tys, _) =>
        match nth_error tys n with
        | Some v => Ok v
        | None => Err("No argument at position " ++ string_of_nat n)
        end
    end
  | _ => Err "Init declaration must be a constant in the global environment"
  end.

Definition specialize_extract_template_env
           (params : extract_template_env_params)
           (Σ : global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env _ :=
  extract_template_env_general SpecializeChainBase.specialize_ChainBase_env
                       params
                       Σ
                       seeds
                       ignore.

Section ConcordiumPrinting.

  Context `{RustPrintConfig}.

  Definition result_string_err A := result A bytestring.string.

  Existing Instance ConcordiumPreamble.concordium_extract_preamble.

  Definition extract_lines
             (seeds : KernameSet.t)
             (Σ : global_env)
             (remaps : remaps)
             (params : extract_template_env_params) : result_string_err (list String.string) :=
    let should_ignore kn :=
        if remap_inductive remaps (mkInd kn 0) then true else
        if remap_constant remaps kn then true else
          if remap_inline_constant remaps kn then true else false in
    Σ <- specialize_extract_template_env params Σ seeds should_ignore;;
    let attrs _ := bs_to_s "#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]" in
    let p := print_program Σ remaps attrs in
    '(_, s) <- timed (bs_to_s "Printing") (fun _ => map_error s_to_bs (finish_print_lines p));;
    ret s.

  Definition print_init_attrs (contract_name : string) : string :=
    "#[init(contract = """ ++ contract_name ++ """" ++ ", payable, enable_logger, low_level)]".

  Notation "<$ x ; y ; .. ; z $>" := (String.concat MCString.nl (cons x (cons y .. (cons z nil) ..))) : bs_scope.

  Definition init_wrapper (contract_name : string) (init_name : kername) :=
    <$ print_init_attrs contract_name ;
     "fn contract_init<StateError: Default>(";
     "    ctx: &impl HasInitContext<()>,";
     "    amount: concordium_std::Amount,";
     "    logger: &mut impl HasLogger,";
     "    state: &mut impl HasContractState<StateError>";
     ") -> Result<(), InitError> {";
     "    let prg = Program::new();";
     "    let params =";
     "        match <_>::concert_deserial(&mut ctx.parameter_cursor(), &prg.__alloc) {";
     "            Ok(p) => p,";
     "            Err(_) => return Err(InitError::DeserialParams)";
     "        };";
     "    let cchain =";
     "        " ++ RustExtract.ty_const_global_ident_of_kername <%% Chain %%> ++ "::build_chain(";
     "            PhantomData,";
     "            0, // No chain height";
     "            ctx.metadata().slot_time().timestamp_millis(),";
     "            0 // No finalized height";
     "        );";
     "    let cctx =";
     "        " ++ RustExtract.ty_const_global_ident_of_kername <%% @ContractCallContext %%> ++ "::build_ctx(";
     "            PhantomData,";
     "            Address::Account(ctx.init_origin()),";
     "            Address::Account(ctx.init_origin()),";
     "            Address::Contract(ContractAddress { index: 0, subindex: 0 }),";
     "            amount.micro_ccd as i64,";
     "            amount.micro_ccd as i64);";
     "    let res = prg." ++ RustExtract.const_global_ident_of_kername init_name ++ "(&cchain, &cctx, params);";
     "    match res {";
     "        Result::Ok(init_state) => {";
     "            match init_state.concert_serial(state) {";
     "                Ok(_) => Ok(()),";
     "                Err(_) => Err(InitError::SerialParams)";
     "            }";
     "        }";
     "        Result::Err(error) => Err(InitError::Error(error))";
     "    }";
"}" $>.

  Definition list_name : string :=
    RustExtract.ty_const_global_ident_of_kername <%% list %%>.

  Definition convert_actions : string :=
  <$
"fn convert_actions<A: HasActions>(acts: &" ++ list_name ++ "<ActionBody>) -> Result<A, ReceiveError> {";
"  match acts {";
"    &" ++ list_name ++ "::nil(_) => Ok(A::accept()),";
"    &" ++ list_name ++ "::cons(_, hd, tl) => {";
"      let cact =";
"        if let ActionBody::Transfer(Address::Account(acc), amount) = hd {";
"          let amount = convert::TryInto::try_into(amount).map_err(|_| ReceiveError::ConvertActions)?;";
"          A::simple_transfer(&acc, concordium_std::Amount::from_micro_ccd(amount))";
"        } else {";
"          return Err(ReceiveError::ConvertActions) // Cannot handle call to contract through ConCert, use Concordium functions instead";
"        };";
"      Ok(cact.and_then(convert_actions(tl)?))";
"    }";
"  }";
"}" $>.

  Definition print_receive_attrs (contract_name : string) (receive_name : kername) : string :=
    "#[receive(contract = """ ++ contract_name ++ """" ++
              ", name = """ ++ RustExtract.const_global_ident_of_kername receive_name ++ """" ++
              ", payable, enable_logger, low_level)]".

  Definition receive_wrapper
             (contract_name : string) (receive_name : kername) : string :=
    <$ print_receive_attrs contract_name receive_name;
     "fn contract_receive<A: HasActions, StateError: Default>(";
     "    ctx: &impl HasReceiveContext<()>,";
     "    amount: concordium_std::Amount,";
     "    logger: &mut impl HasLogger,";
     "    state: &mut impl HasContractState<StateError>,";
     ") -> Result<A, ReceiveError> {";
     "    let prg = Program::new();";
     "    let msg =";
     "        match <_>::concert_deserial(&mut ctx.parameter_cursor(), &prg.__alloc) {";
     "            Ok(m) => m,";
     "            Err(_) => return Err(ReceiveError::DeserialMsg)";
     "        };";
     "    let old_state =";
     "        match <_>::concert_deserial(state, &prg.__alloc) {";
     "            Ok(s) => s,";
     "            Err(_) => return Err(ReceiveError::DeserialOldState)";
     "        };";
     "    let cchain =";
     "        " ++ RustExtract.ty_const_global_ident_of_kername <%% Chain %%> ++ "::build_chain(";
     "            PhantomData,";
     "            0, // No chain height";
     "            ctx.metadata().slot_time().timestamp_millis(),";
     "            0 // No finalized height";
     "        );";
     "    let balance = if ctx.sender() != concordium_std::Address::Contract(ctx.self_address()) {";
     "   // if the contract is not calling itself, we add amount to the current balance";
     "   // as expeced by the ConCert execution model";
     "   (ctx.self_balance().micro_ccd + amount.micro_ccd) as i64";
     "    } else {";
     "        ctx.self_balance().micro_ccd as i64";
     "    };";
     "    let cctx =";
     "        " ++ RustExtract.ty_const_global_ident_of_kername <%% @ContractCallContext %%> ++ "::build_ctx(";
     "            PhantomData,";
     "            Address::Account(ctx.invoker()),";
     "            ctx.sender(),";
     "            Address::Contract(ctx.self_address()),";
     "            balance,";
     "            amount.micro_ccd as i64);";
     "    let res = prg." ++ RustExtract.const_global_ident_of_kername receive_name ++ "(&cchain, &cctx, old_state, msg);";
     "    match res {";
     "        Result::Ok((new_state, acts)) => {";
     "            state.truncate(0);";
     "            match new_state.concert_serial(state) {";
     "                Ok(_) => convert_actions(acts),";
     "                Err(_) => Err(ReceiveError::SerialNewState)";
     "            }";
     "        }";
     "        Result::Err(error) => Err(ReceiveError::Error(error))";
     "    }";
"}" $>.

  Definition print_lines (lines : list bytestring.string) : TemplateMonad unit :=
    monad_iter tmMsg lines.

  Open Scope bool.

  Definition WITH_UNIVERSES := false.

  Definition concordium_extraction
           {init_type receive_type : Type}
           (m : ConcordiumMod init_type receive_type)
           (remaps : remaps)
           (should_inline : kername -> bool) : TemplateMonad unit :=
  init_tm <- tmEval cbn m.(concmd_init);;
  recv_tm <- tmEval cbn m.(concmd_receive);;
  '(Σ,_) <- tmQuoteRecTransp (init_tm, recv_tm) false ;;
  init_nm <- extract_def_name m.(concmd_init);;
  receive_nm <- extract_def_name m.(concmd_receive);;
  extra <- monad_map extract_def_name_exists m.(concmd_extra);;
  let overridden_masks kn :=
      if eq_kername kn init_nm || eq_kername kn receive_nm then
        Some []
      else
        None in
  let seeds := KernameSetProp.of_list (init_nm :: receive_nm :: extra) in
  let params := extract_rust_within_coq overridden_masks should_inline in
  Σ <- tmEval lazy (if WITH_UNIVERSES then
                     Ast.Env.mk_global_env (Ast.Env.universes Σ) (declarations Σ) (Ast.Env.retroknowledge Σ)
                   else
                     Ast.Env.mk_global_env (ContextSet.empty) (declarations Σ) (Ast.Env.retroknowledge Σ));;
  Σ <- run_transforms Σ params;;
  res <- tmEval lazy (extract_lines seeds Σ remaps params);;
  match res with
  | Ok lines =>
    let init_wrapper := init_wrapper m.(concmd_contract_name) init_nm in
    let receive_wrapper := receive_wrapper m.(concmd_contract_name) receive_nm in
    print_lines (map s_to_bs lines ++ [""; init_wrapper; ""; convert_actions; ""; receive_wrapper])
  | Err e => tmFail e
  end.

End ConcordiumPrinting.

Module DefaultPrintConfig.

  Definition RustConfig : RustPrintConfig :=
    {| term_box_symbol := "()";
       type_box_symbol := "()";
       any_type_symbol := "()";
       print_full_names := true |}.

End DefaultPrintConfig.
