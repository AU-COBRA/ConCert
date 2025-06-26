(** * Extraction of an interpreter for a stack based DSL *)
From MetaRocq.Template Require Import All.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Execution Require Import Blockchain.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require LiquidityPretty.
From ConCert.Extraction Require LiquidityExtract.
From ConCert.Examples.StackInterpreter Require Import StackInterpreterExtract.
From ConCert.Utils Require Import BSEnv.
From Stdlib Require Import ZArith.
Local Open Scope string_scope.
Import MRMonadNotation.
Import Interpreter.


Module LiquidityInterp.

  Definition PREFIX := "".

  Import LiquidityExtract LiquidityPretty.

  (** A translation table for various constants we want to rename *)
  Definition TT_remap : list (kername * string) :=
    [ (* remapping types *)
        remap <%% Z %%> "int"
      ; remap <%% bool %%> "bool"
      ; remap <%% unit %%> "unit"
      ; remap <%% option %%> "option"
      ; remap <%% ConCert.Execution.ResultMonad.result %%> "result"
      ; remap <%% Amount %%> "tez"
      ; remap <%% address_rocq %%> "address"
      ; remap <%% time_rocq %%> "timestamp"
      ; remap <%% list %%> "list"
      ; remap <%% String.string %%> "string"
      ; remap <%% ext_map %%> (print_finmap_type "string * int" "value")
      ; remap <%% action %%> "operation"
      (* remapping operations *)
      ; remap <%% Z.add %%> "addInt"
      ; remap <%% Z.mul %%> "mulInt"
      ; remap <%% Z.sub %%> "subInt"
      ; remap <%% Z.eqb %%> "eqInt"
      ; remap <%% Z.leb %%> "leInt"
      ; remap <%% Z.ltb %%> "ltInt"
      ; remap <%% @lookup %%> "Map.find"
      ; remap <%% @fst %%> "fst"
      ; remap <%% @snd %%> "snd"
      ; remap <%% andb %%> "andb"
      ; remap <%% one %%> "1"
    ].

  Definition TT_rename : env string :=
    (* constructors *)
    [ ("Z0" ,"0")
    ; ("O", "0")
    ; ("Ok", "Ok")
    ; ("Err", "Err")
    ; ("nil", "[]")].

  Definition INTERP_MODULE : LiquidityMod params _ _ storage action Error :=
    {| (* a name for the definition with the extracted code *)
       lmd_module_name := "liquidity_interp" ;

       (* definitions of operations on ints, bools, pairs, ect. *)
       lmd_prelude := prod_ops ++ nl ++ int_ops ++ nl ++ bool_ops ++ nl ++ result_def;

       lmd_init := init ;

       lmd_init_prelude := "";

       lmd_receive := receive ;

       (* code for the entry point *)
       lmd_entry_point :=
             printWrapper (PREFIX ++ "receive")
                          ++ nl
                          ++ printMain
    |}.

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

End LiquidityInterp.
