From MetaCoq Require Import monad_utils.
From MetaCoq Require Import utils.
From MetaCoq.Template Require Import All.
From MetaCoq.Template Require Import Kernames.

From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import RustExtract.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import SpecializeChainBase.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import Printing.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Utils.
From ConCert.Extraction.Examples Require Import CounterRefinementTypes.
From ConCert.Extraction.Examples Require Import RustExtractTests.
From ConCert.Utils Require Import StringExtra.

Module ConcordiumRemap.

Definition lookup_const (TT : list (kername * string)) (name : kername): option string :=
  match find (fun '(key, _) => eq_kername key name) TT with
  | Some (_, val) => Some val
  | None => None
  end.

Definition remap_arith : list (kername * string) := Eval compute in
  [  remap <%% BinPosDef.Pos.add %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_add(b).unwrap() }"
   ; remap <%% BinPosDef.Pos.succ %%> "fn ##name##(&'a self, a: u64) -> u64 { a.checked_add(1).unwrap() }"
   ; remap <%% Z.add %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_add(b).unwrap() }"
   ; remap <%% Z.sub %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_sub(b).unwrap() }"
   ; remap <%% Z.mul %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_mul(b).unwrap() }"
   ; remap <%% Z.eqb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a == b }"
   ; remap <%% Z.leb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a <= b }"
   ; remap <%% Z.ltb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a < b }" ].


Definition remap_inline_bool_ops := Eval compute in
      [ remap <%% andb %%> "__andb!"
      ; remap <%% orb %%> "__orb!"].

Definition remap_positive : remapped_inductive :=
  {| re_ind_name := "u64";
     re_ind_ctors := ["__pos_onebit"; "__pos_zerobit"; "1"];
     re_ind_match := None
  |}.

Definition remap_Z : remapped_inductive :=
  {| re_ind_name := "i64";
     re_ind_ctors := ["0"; "__Z_frompos"; "__Z_fromneg"];
     re_ind_match := None
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

Definition remap_unit : remapped_inductive :=
  {| re_ind_name := "()";
     re_ind_ctors := ["()"];
     re_ind_match := None
  |}.

Definition remap_std_types :=
  [ (<%% positive %%>, remap_positive)
  ; (<%% Z %%>,  remap_Z)
  ; (<%% bool %%>, remap_bool)
  ; (<%% prod %%>, remap_pair)
  ; (<%% option %%>, remap_option)
  ; (<%% unit %%>, remap_unit)].

Definition lookup_inductive (TT_inductives : list (kername * remapped_inductive))  (ind : inductive) : option remapped_inductive :=
  match find (fun '(key, _) => eq_kername key (inductive_mind ind)) TT_inductives with
  | Some (_, val) => Some val
  | None => None
  end.

Definition build_remaps
           (TT_const : list (kername * string))
           (TT_const_inline : list (kername * string))
           (TT_inductives : list (kername * remapped_inductive))
  : remaps :=
  {| remap_inductive := lookup_inductive TT_inductives;
     remap_constant := lookup_const TT_const;
     remap_inline_constant := lookup_const TT_const_inline; |}.

End ConcordiumRemap.

Module ConcordiumPreamble.
  Instance concordium_extract_preamble : Preamble :=
{| top_preamble := [
"#![allow(dead_code)]";
"#![allow(non_camel_case_types)]";
"#![allow(unused_imports)]";
"#![allow(non_snake_case)]";
"#![allow(unused_variables)]";
 "";
"use concordium_std::*;";
"use core::marker::PhantomData;";
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
"type State = Storage<'static>;";
"";
"#[derive(Debug, PartialEq, Eq)]";
"enum InitError {";
"   ParseParams,";
"   IError";
"}";
"";
"impl From<ParseError> for InitError {";
"    fn from(_: ParseError) -> Self { InitError::ParseParams }";
"}";
"";
"#[derive(Debug, PartialEq, Eq)]";
"enum ReceiveError {";
"    ParseParams,";
"    Error";
"}";
"";
"impl From<ParseError> for ReceiveError {";
"    fn from(_: ParseError) -> Self { ReceiveError::ParseParams }";
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
    concmd_extra : list ({T : Type & T});
    concmd_wrap_init : forall (contact_name init_name : string), string;
    concmd_wrap_receive : forall (contact_name receive_name : string), string;}.

Arguments concmd_contract_name {_ _}.
Arguments concmd_init {_ _}.
Arguments concmd_receive {_ _}.
Arguments concmd_extra {_ _}.
Arguments concmd_wrap_init {_ _}.
Arguments concmd_wrap_receive {_ _}.

Definition get_fn_arg_type (Σ : Ex.global_env) (fn_name : kername) (n : nat)
  : result Ex.box_type string :=
  match Ex.lookup_env Σ fn_name with
  | Some (Ex.ConstantDecl cb) =>
    match decompose_TArr cb.(Ex.cst_type).2 with
    | (tys, _) => result_of_option (nth_error tys n)
                                  ("No argument at position " ++ string_of_nat n)
    end
  | _ => Err "Init declaration must be a constant in the global environment"
  end.

Definition specilize_extract_template_env
           (params : extract_template_env_params)
           (Σ : global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := SafeTemplateChecker.fix_global_env_universes Σ in
  let Σ := TemplateToPCUIC.trans_global_decls Σ in
  Σ <- SpecializeChainBase.specialize_ChainBase_env Σ ;;
  wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.


Definition extract_lines
           (seeds : KernameSet.t)
           (Σ : global_env)
           (remaps : remaps)
           (ind_attrs : ind_attr_map)
           (should_inline : kername -> bool) : result (list string) string :=
  let without_deps kn :=
      if remap_inductive remaps (mkInd kn 0) then true else
      if remap_constant remaps kn then true else
      if remap_inline_constant remaps kn then true else false in
  Σ <- specilize_extract_template_env
         (extract_rust_within_coq should_inline)
         Σ seeds without_deps;;
  let p :=  print_program Σ remaps ind_attrs in
      (* TODO: wrappers to integrate with the Concordium infrastructure go here *)
  '(_, s) <- timed "Printing" (fun _ => finish_print_lines p);;
  ret s.

Open Scope string.

Definition print_init_attrs (contract_name : string) : string :=
  "#[init(contract = """ ++ contract_name ++ """" ++ ",  enable_logger)]".

Definition init_wrapper (contract_name init_name : string) :=
  <$ print_init_attrs contract_name ;
     "fn contract_init(ctx: &impl HasInitContext<()>,";
     "                 logger: &mut impl HasLogger) -> Result<State, InitError> {";
     "let v = ctx.parameter_cursor().get()?;";
     "logger.log(&v);";
     "let prg = Program::new();";
     "let res = prg." ++ init_name ++ "((),v);";
     "match res {";
     "   Option::Some(init_v) => Ok(init_v),";
     "   Option::None => Err(InitError::IError)";
"    }";
"}" $>.

Definition print_receive_attrs (contract_name receive_name : string) : string :=
  "#[receive(contract = """ ++ contract_name ++
                        """, name = """ ++ receive_name ++ """, payable, enable_logger)]".



Definition receive_wrapper_no_calls (contract_name receive_name : string)
  : string :=
  <$ print_receive_attrs contract_name receive_name;
     "fn contract_receive<A: HasActions>(";
     "   ctx: &impl HasReceiveContext<()>,";
     "   amount: Amount,";
     "    logger: &mut impl HasLogger,";
     "    state: &mut State )";
     "    -> Result<A, ReceiveError> {";
     "    let prg = Program::new();";
     "    let msg = ctx.parameter_cursor().get()?;";
     "    let res = prg." ++ receive_name ++ "(&msg,*state);";
     "    match res {";
     "        Option::Some(v) =>{";
     "            *state = v.1;";
     "            Ok(A::accept())},";
     "        Option::None => Err(ReceiveError::Error)";
     "    }";
"}" $>.

Definition rust_extraction {init_type receive_type : Type} (m : ConcordiumMod init_type receive_type) (remaps : remaps) (ind_attrs : ind_attr_map) (should_inline : kername -> bool) : TemplateMonad _ :=
  '(Σ,_) <- tmQuoteRecTransp m false ;;
  init_nm <- extract_def_name m.(concmd_init);;
  receive_nm <- extract_def_name m.(concmd_receive);;
  extra <- monad_map extract_def_name_exists m.(concmd_extra);;
  res <- tmEval lazy (extract_lines (KernameSetProp.of_list (init_nm :: receive_nm :: extra)) Σ remaps ind_attrs should_inline);;
  match res with
  | Ok lines =>
    let init_wrapper :=
        m.(concmd_wrap_init) m.(concmd_contract_name) init_nm.2 in
    let receive_wrapper :=
        m.(concmd_wrap_receive) m.(concmd_contract_name) receive_nm.2 in
    tmEval lazy (String.concat nl lines ++ nl ++ nl
                               ++ init_wrapper ++ nl ++ nl
                               ++ receive_wrapper)
  | Err e => tmFail e
  end.
