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

  Definition receive (p : params) (s : list value) := interp p.2 p.1 s.

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
     ; local_def <% params %>
     ; local_def <% interp %>
     ; local_def <% instruction %>
     ; local_def <% value %>
     ; local_def <% op %>
  ].

(** A wrapper for calling the main functionality [func_name]. It is important to be explicit about types for all the parameters of entry points *)
Definition print_main (func_name : string): string :=
  let func_name := PREFIX ++ func_name in
  let params_name := PREFIX ++ "params" in
  "let%entry main (p : " ++ params_name ++ ")" ++ " s ="
    ++ nl
    ++ "match " ++ func_name ++ " p s"  ++ " with"
    ++ nl
    ++ "| Some res -> ( [], res ) "
    ++ nl
    ++ "| _ -> Current.failwith s".

Fixpoint combine_global_envs (Σ Σ' : global_env) : global_env :=
  match Σ' with
  | [] => Σ
  | (nm,d) :: Σ'' => match (lookup_env Σ nm) with
                   | Some _ => (combine_global_envs Σ Σ'')%list
                   | None => ((nm,d) :: combine_global_envs Σ Σ'')%list
                   end
  end.

Definition INTERP_MODULE : LiquidityModule :=
  {| (* a name for the definition with the extracted code *)
     lm_module_name := "liquidity_interp" ;

     (* definitions of operations on ints, bools, pairs, ect. *)
     lm_prelude := prod_ops ++ nl ++ int_ops ++ nl ++ bool_ops;

     (* inductives *)
     lm_adts := ["op";"instruction";"value"];

     (* definitions: type abbreviations and functions *)
     lm_defs := ["params"; "storage";"obs0";"interp";"receive"];

     (* code for the entry point *)
     lm_entry_point := print_main "receive";

     (* initial storage *)
     lm_init := "[]" |}.

(** Adds a definition containing a global environment containing all dependencies required for erasure *)

Run TemplateProgram (ps <- monad_map erasable_program (List.rev INTERP_MODULE.(lm_defs)) ;;
                     let env := fold_left combine_global_envs (map fst ps) [] in
                     res <- tmEval all env ;;
                     tmDefinition "GE" res).

(** We translate required definitions and print them into a single string containing the whole program. The definition with the corresponding code is added to Coq's environment. *)
Time Run TemplateProgram (printLiquidityModule PREFIX GE TT INTERP_MODULE).

(** The extracted program can be printed and copy-pasted to the online Liquidity editor *)
Print liquidity_interp.

(** or redirected to a file, creating "interp.liq.out".
 The contents require further post-processing to be compiled with the Liquidity compiler.*)
Redirect "interp.liq" Compute liquidity_interp. (* creates "interp.liq.out"*)
