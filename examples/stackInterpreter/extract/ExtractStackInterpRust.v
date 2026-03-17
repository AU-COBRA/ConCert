From ConCert.Examples.StackInterpreter Require Import StackInterpreterRustExtract.
From TypedExtraction Require Import RustExtract.
From TypedExtraction Require Import Printing.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From MetaRocq.Template Require Import All.
From Stdlib Require Import List.
From Stdlib Require Import Bool.



Redirect "concordium-extract/interp.rs"
MetaRocq Run (concordium_extraction
               STACK_INTERP_MODULE
               (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_Z_arith
                     ++ ConcordiumRemap.remap_blockchain_consts
                     ++ remap_extra_consts)
                  ConcordiumRemap.remap_inline_bool_ops
                  (ConcordiumRemap.remap_std_types
                     ++ ConcordiumRemap.remap_blockchain_inductives))
               (fun kn => eq_kername <%% bool_rec %%> kn
                          || eq_kername <%% bool_rect %%> kn)).
