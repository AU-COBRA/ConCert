(** * Extraction of an interpreter for a stack based DSL *)
From MetaRocq.Template Require Import All.
From ConCert.Extraction Require Import LiquidityPretty.
From ConCert.Extraction Require Import LiquidityExtract.
From ConCert.Examples.StackInterpreter Require Import StackInterpreterLiquidityExtract.

Import LiquidityInterp.
Import MonadNotation.



(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaRocq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)

Time MetaRocq Run
      (t <- liquidity_extraction PREFIX TT_remap TT_rename [] INTERP_MODULE ;;
      tmDefinition INTERP_MODULE.(lmd_module_name) t
      ).

(** The extracted program can be printed and copy-pasted to the online Liquidity editor *)
(* MetaRocq Run (tmMsg liquidity_interp). *)

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "liquidity-extract/StackInterpreter.liq"
  MetaRocq Run (tmMsg liquidity_interp).
