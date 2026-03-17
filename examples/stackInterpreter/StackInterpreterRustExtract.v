From ConCert.Examples.StackInterpreter Require Import StackInterpreter.
From TypedExtraction Require Import RustExtract.
From TypedExtraction Require Import Printing.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From TypedExtraction Require Import StringExtra.
From MetaRocq.Template Require Import All.
From MetaRocq.TemplatePCUIC Require Import PCUICToTemplate.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.



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

#[export]
Instance RustConfig : RustPrintConfig :=
    {| term_box_symbol := "()";
       type_box_symbol := "()";
       any_type_symbol := "()";
       print_full_names := false |}.
