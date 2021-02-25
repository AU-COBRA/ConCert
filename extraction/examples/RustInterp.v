From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Bool.

From ConCert.Extraction Require Import RustExtract.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Utils Require Import StringExtra.

From ConCert.Extraction.Examples Require Import StackInterpreter.

From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import Printing.

Open Scope string.
Module SI := StackInterpreter.Interpreter.

Instance RustCounterConfig : RustPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     print_full_names := false |}.

Definition remap_blockchain : list (kername * string) := Eval compute in
      [ remap <%% PreludeExt.SimpleCallCtx %%> "type SimpleCallCtx<'a> = ();" ].

Definition map_lookup : string :=
  <$ "fn lookup<V>(&'a self, key : (String,i64) , m : &'a immutable_map::TreeMap<(String,i64), V>) -> Option<&'a V> {";
     "   m.get(&key)";
     "}" $>.


Definition remap_extra : list (kername * string) := Eval compute in
      [ remap <%% SI.lookup %%> map_lookup
      ; remap <%% SI.ext_map %%> "type Ext_map<'a> = &'a immutable_map::TreeMap<(String,i64), Value<'a>>;"].


Definition remap_address : remapped_inductive :=
  {| re_ind_name := "AccountAddress";
     re_ind_ctors := [];
     re_ind_match := None |}.

Definition remap_string : remapped_inductive :=
  {| re_ind_name := "String";
     re_ind_ctors := [];
     re_ind_match := None |}.


Definition remap_map : remapped_inductive :=
  {| re_ind_name := "immutable_map::TreeMap<(String,i64), value>";
     re_ind_ctors := [];
     re_ind_match := None |}.


Definition attrs : ind_attr_map :=
  fun kn => if eq_kername <%% SI.op %%> kn || eq_kername <%% SI.instruction %%> kn  then ["#[derive(Debug,Serialize)]"]
         else ["#[derive(Debug, Copy, Clone)]"].


Definition STACK_INTERP_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "interpreter";
     concmd_init := SI.init;
     concmd_receive := SI.receive;
     concmd_wrap_init := init_wrapper;
     concmd_wrap_receive := receive_wrapper_no_calls |}.

Import Blockchain.

Open Scope list.

Definition types_remap :=
  [ (<%% positive %%>, ConcordiumRemap.remap_positive)
  ; (<%% Z %%>,  ConcordiumRemap.remap_Z)
  ; (<%% bool %%>, ConcordiumRemap.remap_bool)
  ; (<%% prod %%>, ConcordiumRemap.remap_pair)
  ; (<%% option %%>, ConcordiumRemap.remap_option)
  ; (<%% @ActionBody %%>,  ConcordiumRemap.remap_unit )
       (* ; (<%% SI.ext_map %%>, remap_map) *)
  ; (<%% string %%>, remap_string)].

MetaCoq Run (t <- tmQuoteRecTransp STACK_INTERP_MODULE false ;;
             tmDefinition "ENV" t.1).

Open Scope string.

(* Definition rust_interp := Eval vm_compute in *)
(*   let init_nm := <%% SI.init %%> in *)
(*   let receive_nm := <%% SI.receive %%> in *)
(*   let res := extract_lines init_nm receive_nm ENV *)
(*                  (ConcordiumRemap.build_remaps *)
(*                     (ConcordiumRemap.remap_arith ++ remap_blockchain ++ remap_extra) *)
(*                     (remap_inline ++ ConcordiumRemap.remap_inline_bool_ops) *)
(*                     types_remap) *)
(*                  attrs *)
(*                  (fun kn => eq_kername <%% bool_rec %%> kn *)
(*                          || eq_kername <%% bool_rect %%> kn) in *)
(*   res. *)

(* Definition unwrap_result (r : result (list string) string) : list string := *)
(*   match r with *)
(*   | Ok lines => lines *)
(*   | Err _ => [] *)
(*   end. *)

(* Fixpoint print_lines (s : list string) : TemplateMonad unit := *)
(*   match s with *)
(*   | [] => tmMsg "" *)
(*   | l :: s => tmMsg l;; *)
(*               print_lines s *)
(*   end. *)

(* Redirect "interp.rs" MetaCoq Run (print_lines (unwrap_result rust_interp)). *)

Definition ex1 := [SI.IPushZ 1; SI.IPushZ 1; SI.IOp SI.Add].

MetaCoq Quote Recursively Definition blah := ex1.

Compute (t <- (extract_lines (KernameSetProp.of_list [ (MPfile ["RustInterp"; "Examples"; "Extraction"; "ConCert"], "ex1")])
                       blah.1
           (ConcordiumRemap.build_remaps
                            (ConcordiumRemap.remap_arith ++ remap_blockchain ++ remap_extra)
                            ( ConcordiumRemap.remap_inline_bool_ops)
                            types_remap)
                         attrs
                         (fun kn => eq_kername <%% bool_rec %%> kn
                                 || eq_kername <%% bool_rect %%> kn));;
             ret (String.concat nl t)).

(* This leads to stack overflow, because the number of lines is too large and String.concat overflows *)
MetaCoq Run (res <- rust_extraction STACK_INTERP_MODULE
                           (ConcordiumRemap.build_remaps
                              (ConcordiumRemap.remap_arith ++ remap_blockchain ++ remap_extra)
                              ( ConcordiumRemap.remap_inline_bool_ops)
                              types_remap)
                           attrs
                           (fun kn => eq_kername <%% bool_rec %%> kn
                                   || eq_kername <%% bool_rect %%> kn);;
            tmMsg res).
