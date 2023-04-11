From ConCert.Examples.StackInterpreter Require Import StackInterpreter.
From RustExtraction Require Import RustExtract.
From RustExtraction Require Import Printing.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From RustExtraction Require Import StringExtra.
From MetaCoq.Template Require Import All.
From MetaCoq.TemplatePCUIC Require Import PCUICToTemplate.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Bool.

Open Scope string.

Module SI := StackInterpreter.

Definition map_lookup : string :=
  <$ "fn ##name##<V>(&'a self, key : (&'a String,i64) , m : &'a immutable_map::TreeMap<(&'a String,i64), V>) -> Option<&'a V> {";
     "   m.get(&key)";
     "}" $>.

Definition remap_extra_consts : list (kername * string) := Eval compute in
      [ remap <%% SI.lookup %%> map_lookup
      ; remap <%% SI.ext_map %%> "type Ext_map<'a> = &'a immutable_map::TreeMap<(&'a String, i64), Value<'a>>;"].

Definition ex1 := [SI.IPushZ 1; SI.IPushZ 1; SI.IOp SI.Add].

Definition STACK_INTERP_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "interpreter"%bs;
     concmd_init := @SI.init;
     concmd_receive := @SI.receive;
     (* Extracting the example as well *)
     concmd_extra := [@existT _ (fun T : Type => T) _ ex1]; |}.

Open Scope list.

#[local]
Instance RustConfig : RustPrintConfig :=
    {| term_box_symbol := "()";
       type_box_symbol := "()";
       any_type_symbol := "()";
       print_full_names := false |}.

Redirect "../extraction/tests/extracted-code/concordium-extract/interp.rs"
MetaCoq Run (concordium_extraction
               STACK_INTERP_MODULE
               (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_Z_arith
                     ++ ConcordiumRemap.remap_blockchain_consts
                     ++ map (on_snd String.of_string) remap_extra_consts)
                  ConcordiumRemap.remap_inline_bool_ops
                  (ConcordiumRemap.remap_std_types
                     ++ ConcordiumRemap.remap_blockchain_inductives))
               (fun kn => eq_kername <%% bool_rec %%> kn
                          || eq_kername <%% bool_rect %%> kn)).
