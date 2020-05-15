From Coq Require Import PeanoNat ZArith Notations Bool.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Extraction Require Import LPretty Certified Extra.
From ConCert.Execution Require Import Containers.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Definition PREFIX := "".

(** Quoting this runs forever, because of many dependencies *)
Definition lookup (m : FMap string Z) (k : string) := FMap.find k m.
(* Quote Recursively Definition lookup_quoted :=lookup. *)

Definition map_key_type := (string * Z).

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

  Definition params := list instruction * ext_map.

  Definition obs0 s := IObs s 0.

  Definition key_eq (k1 : string * Z) (k2 : string * Z)
    := (k1.1 =? k2.1) && (k1.2 =? k2.2)%Z.

  Fixpoint interp (ext : ext_map) (insts : list instruction) (s : list value) :=
    match insts with
    | [] => Some s
    | hd :: inst' =>
      match hd with
      | IPushZ i => interp ext inst' (ZVal i :: s)
      | IPushB b => interp ext inst' (BVal b :: s)
      | IObs l i => match lookup (l,i) ext with
                   | Some v => Some (v :: s)
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

End Interpreter.

Import Interpreter.

Definition local_def := local PREFIX.

Definition print_finmap_type (prefix ty_key ty_val : string) :=
  parens false (ty_key ++ "," ++ prefix ++ ty_val) ++ " map".

(** A translation table for various constants we want to rename *)
Definition TT : env string :=
  [   (* remapping types *)
       remap <% Z %> "int"
     ; remap <% bool %> "bool"
     ; remap <% nat %> "address"
     ; remap <% list %> "list"
     ; remap <% string %> "string"
     ; remap <% ext_map %> (print_finmap_type PREFIX "string * int" "value")

     (* remapping operations *)
     ; remap <% Z.add %> "addInt"
     ; remap <% Z.eqb %> "eqInt"
     ; remap <% @lookup %> "Map.find"
     ; remap <% @fst %> "fst"
     ; remap <% @snd %> "snd"
     ; remap <% andb %> "andb"

     (* remapping constructors *)
     ; ("Some", "Some")
     ; ("None", "None")
     ; ("true", "true")
     ; ("false", "false")

     ; ("Z0" ,"0")
     ; ("nil", "[]")

     (* local types *)
     ; local_def <% storage %>
     ; local_def <% instruction %>
     ; local_def <% value %>
     ; local_def <% op %>
  ].

(** A wrapper for calling the main functionality. It is important to be explicit about types for all the parameters of entry points *)
Definition print_main (Σ : global_env) (param_type : term) : string :=
  let param_liq_type := print_liq_type PREFIX TT param_type in
  let func_name := PREFIX ++ "interp" in
  "let%entry main (prog : " ++ param_liq_type ++ ")" ++ " s ="
    ++ nl
    ++ "let s = " ++ func_name ++ "(prog.(1), prog.(0) ,[]) in"
    ++ nl
    ++ "match s with"
    ++ nl
    ++ "| Some res -> ( [], res ) "
    ++ nl
    ++ "| _ -> Current.failwith s".

(** Adds a definition containing a "program" corresponding to the [interp] function. The "program" is a global environment containing all dependencies required for erasure and validation to go through and a quoted term*)
Run TemplateProgram (t <- erasable_program "interp"  ;;
                     tmDefinition "interp_quoted" t).


Definition GE := interp_quoted.1.

Definition INTERP_MODULE : LiquidityModule :=
  {| lm_module_name := "liquidity_interp" ;
     lm_prelude := prod_ops ++ nl ++ int_ops ++ nl ++ bool_ops;
     lm_adts := ["op";"instruction";"value"];
     lm_functions := ["params"; "storage";"obs0";"interp"];
     lm_entry_point := print_main GE <% unfolded params %>;
     lm_init := "[]" |}.

(** We translate required definitions and print them into a single string containing the whole program. The definition with the corresponding code is added to Coq's environment. *)
Time Run TemplateProgram (printLiquidityModule PREFIX GE TT INTERP_MODULE).

(** The extracted program can be printed and copy-pasted to the online Liquidity editor *)
Print liquidity_interp.

(** or redirected to a file, creating "interp.liq.out".
 The contents require further post-processing to be compiled with the Liquidity compiler.*)
Redirect "interp.liq" Compute liquidity_interp. (* creates "interp.liq.out"*)
