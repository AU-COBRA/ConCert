From MetaCoq.Common Require Import BasicAst.
From MetaCoq.Utils Require Import MCString.

Record remapped_inductive := build_remapped_inductive {
  re_ind_name : string;
  re_ind_ctors : list string;
  re_ind_match : option string;
  }.

Record remaps := {
  remap_inductive : inductive -> option remapped_inductive;
  remap_constant : kername -> option string;
  remap_inline_constant : kername -> option string;
  }.

Definition no_remaps :=
  {| remap_inductive _ := None;
     remap_constant _ := None;
     remap_inline_constant _ := None |}.
