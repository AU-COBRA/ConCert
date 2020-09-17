From Coq Require Import PeanoNat ZArith Notations Bool.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.
From MetaCoq.PCUIC Require Import TemplateToPCUIC PCUICTyping.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Extraction Require Import LPretty LiquidityExtract
     Erasure Common PreludeExt.
From ConCert.Execution Require Import Containers Blockchain.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Definition PREFIX := "".

Definition map_key_type := (string * Z).
Definition action := ActionBody.

Module Interpreter.

  Inductive op : Set := Add | And | Equal.

  Inductive instruction :=
  | IPushZ : Z -> instruction
  | IPushB : bool -> instruction
  | IObs : string -> Z -> instruction
  | IOp : op -> instruction.

  Inductive value : Set := BVal : bool -> value | ZVal : Z -> value.

  Definition ext_map := FMap (string * Z) value.
  Definition lookup (k : string * Z) (m : ext_map) := FMap.find k m.

  Definition storage := list value.

  Definition init (ctx : SimpleCallCtx) (setup : unit) : option storage :=
    let ctx' := ctx in (* prevents optimisations from removing unused [ctx]  *)
    Some [].

  Definition params := list instruction * ext_map.

  Definition obs0 s := IObs s 0.

  Fixpoint interp (ext : ext_map) (insts : list instruction) (s : list value) :=
    match insts with
    | [] => Some s
    | hd :: inst' =>
      match hd with
      | IPushZ i => interp ext inst' (ZVal i :: s)
      | IPushB b => interp ext inst' (BVal b :: s)
      | IObs l i => match lookup (l,i) ext with
                   | Some v => interp ext inst' (v :: s)
                   | None => None
                   end
      | IOp op => match op with
                   | Add => match s with
                            | ZVal i :: ZVal j :: s' => interp ext inst' (ZVal (i+j) :: s')%Z
                            | _ => None
                            end
                   | And => match s with
                            | BVal i :: BVal j :: s' => interp ext inst' (BVal (i && j) :: s')%Z
                            | _ => None
                           end
                   | Equal => match s with
                            | ZVal i :: ZVal j :: s' => interp ext inst' (BVal (i =? j) :: s')%Z
                            | _ => None
                             end
                 end
      end
    end.

  Definition receive (p : params) (s : list value)
    : option (list action * storage) :=
    let s' := s in (* prevents optimisations from removing unused [s]  *)
    match interp p.2 p.1 [] with
    | Some v => Some ([],v)
    | None => None
    end.

End Interpreter.

Import Interpreter.

(** Input for the interpreter in Liquidity: *)
(** ([IPushZ 0; IObs ("blah",0); IOp Add; IPushZ 1; IOp Equal], (Map [(("blah", 0), (ZVal 1))])) *)
Example test_interp :
  let env  := FMap.of_list [(("blah", 0%Z), (ZVal 1))] in
  interp env [IPushZ 0; IObs "blah" 0; IOp Add; IPushZ 1; IOp Equal] [] =
  Some [BVal true].
Proof. reflexivity. Qed.

Definition print_finmap_type (prefix ty_key ty_val : string) :=
  parens false (ty_key ++ "," ++ prefix ++ ty_val) ++ " map".

(** A translation table for various constants we want to rename *)
Definition TT_remap : list (kername * string) :=
  [   (* remapping types *)
       remap <% Z %> "int"
     ; remap <% bool %> "bool"
     ; remap <% unit %> "unit"
     ; remap <% option %> "option"
     ; remap <% Amount %> "tez"
     ; remap <% address_coq %> "address"
     ; remap <% time_coq %> "timestamp"
     ; remap <% list %> "list"
     ; remap <% string %> "string"
     ; remap <% ext_map %> (print_finmap_type PREFIX "string * int" "value")
     ; remap <% action %> "operation"
     (* remapping operations *)
     ; remap <% Z.add %> "addInt"
     ; remap <% Z.eqb %> "eqInt"
     ; remap <% @lookup %> "Map.find"
     ; remap <% @fst %> "fst"
     ; remap <% @snd %> "snd"
       ; remap <% andb %> "andb" ].

Definition TT_rename : MyEnv.env string :=
     (* constructors *)
     [ ("Z0" ,"0")
     ; ("nil", "[]")].

Definition INTERP_MODULE : LiquidityMod params _ _ storage action :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "liquidity_interp" ;

     (* definitions of operations on ints, bools, pairs, ect. *)
     lmd_prelude := prod_ops ++ nl ++ int_ops ++ nl ++ bool_ops;

     lmd_init := init ;

     lmd_init_prelude := "";

     lmd_receive := receive ;

     (* code for the entry point *)
     lmd_entry_point :=
           printWrapper (PREFIX ++ "receive")
                        ++ nl
                        ++ printMain |}.

(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)

Time MetaCoq Run
     (t <- liquitidy_extraction PREFIX TT_remap TT_rename INTERP_MODULE ;;
      tmDefinition INTERP_MODULE.(lmd_module_name) t
     ).

(** The extracted program can be printed and copy-pasted to the online Liquidity editor *)
Print liquidity_interp.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "./extraction/examples/liquidity-extract/StackInterpreter.liq" Compute liquidity_interp.
