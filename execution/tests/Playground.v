From ConCert Require Import Serializable.
(* Remove Hints BoundedN_equivalence. *)
Set Typeclasses Debug Verbosity 1.
(* Existing Instance ser_value_equivalence | 0. *)
(* Check deserialize. *)
(* Print All Dependencies Serializable. *)
(* Transparent deserialize. *)


Check deserialize.
Typeclasses eauto := debug.

Example ex2 : SerializedValue := serialize 2.
Existing Instance nat_serializable | 0.
Existing Instance bool_serializable | 0.
Example ex3 := deserialize ex2.
Compute ex3.
Compute (deserialize ex2).
Check (deserialize ex2).
