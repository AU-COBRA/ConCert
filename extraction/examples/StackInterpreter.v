From Coq Require Import PeanoNat ZArith Notations Bool.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.
From MetaCoq.PCUIC Require Import TemplateToPCUIC PCUICTyping.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Extraction Require Import LPretty Certified Extra Erasure Common.
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

  Definition receive (p : params) (s : list value) := interp p.2 p.1 s.

End Interpreter.

(* Erase the unignored global declarations by the specified names and
   their non-erased dependencies recursively. *)
(* Fixpoint q_rec *)
(*         (Σ : P.global_env) *)
(*         (ignored : list kername) *)
(*         (include : list kername): global_env:= *)
(*   match Σ with *)
(*   | [] => [] *)
(*   | (kn, decl) :: Σ => *)
(*     if contains kn include && negb (contains kn ignored)  then *)
(*       (kn, decl) :: q_rec Σ ignored (decl_deps include decl) *)
(*     else *)
(*       q_rec Σ _ include *)
(*   end. *)
(* Next Obligation. now sq; inversion wfΣ. Qed. *)
(* Next Obligation. now sq; inversion wfΣ. Qed. *)
(* Next Obligation. now sq; inversion wfΣ. Qed. *)
(* Next Obligation. now sq; inversion wfΣ. Qed. *)


(* Import Interpreter. *)
(* Input for the interpreter in Liquidity:

([IPushZ 0; IObs ("blah",0); IOp Add; IPushZ 1; IOp Equal], (Map [(("blah", 0), (ZVal 1))])) *)
(* Example test_interp : *)
(*   let env  := FMap.of_list [(("blah", 0%Z), (ZVal 1))] in *)
(*   interp env [IPushZ 0; IObs "blah" 0; IOp Add; IPushZ 1; IOp Equal] [] = Some [BVal true]. *)
(* Proof. reflexivity. Qed. *)

Module Interpreter1.

  Inductive op : Set := Add | And | Equal.

  Inductive instruction :=
  | IPushZ : Z -> instruction
  | IPushB : bool -> instruction
  | IOp : op -> instruction.

  Inductive value : Set := BVal : bool -> value | ZVal : Z -> value.

  Definition storage := list value.

  Definition params := list instruction.

  Fixpoint interp (insts : list instruction) (s : list value) :=
    match insts with
    | [] => Some s
    | hd :: inst' =>
      match hd with
      | IPushZ i => interp inst' (ZVal i :: s)
      | IPushB b => interp inst' (BVal b :: s)
      | IOp op => match op with
                   | Add => match s with
                            | ZVal i :: ZVal j :: s' => interp inst' (ZVal (i+j) :: s')%Z
                            | _ => None
                            end
                   | And => match s with
                            | BVal i :: BVal j :: s' => interp inst' (BVal (i && j) :: s')%Z
                            | _ => None
                           end
                   | Equal => match s with
                            | ZVal i :: ZVal j :: s' => interp inst' (BVal (i =? j) :: s')%Z
                            | _ => None
                             end
                 end
      end
    end.

  Definition receive (p : params) (s : list value) := interp p s.

End Interpreter1.


Import Interpreter.

Definition local_def := local PREFIX.

Definition print_finmap_type (prefix ty_key ty_val : string) :=
  parens false (ty_key ++ "," ++ prefix ++ ty_val) ++ " map".

(** A translation table for various constants we want to rename *)
Definition TT_remap : MyEnv.env string :=
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
     ; ("nil", "[]") ].

Definition TT_remap_names  :=
  [
       <%% Z %%>
     ; <%% bool %%>
     ; <%% nat %%>
     ; <%% list %%>
     ; <%% string %%>
     ; <%% ext_map %%>
     ; <%% Z.add %%>
     ; <%% Z.eqb %%>
     ; <%% @fst %%>
     ; <%% @snd %%>
     ; <%% andb %%>
     ; <%% @lookup %%>].


Definition TT_local :=
    (* local types *)
  [    local_def <% storage %>
     ; local_def <% params %>
     ; local_def <% interp %>
     ; local_def <% instruction %>
     ; local_def <% value %>
     ; local_def <% op %>].

Definition TT := (TT_remap ++ TT_local)%list.

(** A wrapper for calling the main functionality [func_name]. It is important to be explicit about types for all the parameters of entry points *)
Definition print_main (func_name : string): string :=
  let func_name := PREFIX ++ func_name in
  let params_name := PREFIX ++ "params" in
  "let%entry main (p : " ++ params_name ++ ")" ++ " s ="
    ++ nl
    ++ "match " ++ func_name ++ " p []"  ++ " with"
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

     (* inductives -- in the order that respect dependency *)
     lm_adts := [<%% op %%>;<%% instruction %%>;<%% value %%>];

     (* definitions: type abbreviations and functions -- in the order that respect dependency *)
     (* lm_defs := [<%% params %%>; <%% storage %%>; *)
     (*                 <%% obs0 %%>; *)
     (*                 <%% interp %%>; <%% receive %%>]; *)
     lm_defs := [<%% params %%>;<%% receive %%>] ;

     (* code for the entry point *)
     lm_entry_point := print_main "receive";

     (* initial storage *)
     lm_init := "[]" |}.

(** Adds a definition containing a global environment containing all dependencies required for erasure *)

Time MetaCoq Run (t <- tmQuoteRecTransp Interpreter.receive false ;;
             tmDefinition "GE" t.1).

Compute (List.length GE).

(* Time Compute (specialize_erase_debox_template_env GE [<%% interp %%>] TT_remap_names ). *)

(* Metacoq Run (ps <- monad_map erasable_program (List.rev INTERP_MODULE.(lm_defs)) ;; *)
(*              (* let env := fold_left combine_global_envs (map rev (map (fst) ps)) [] in *) *)
(*              let env := List.concat (map (fst) ps) in *)
(*              res <- tmEval all env ;; *)
(*              tmDefinition "GE" res). *)
(* Compute GE. *)

Definition clear_bodies (Σ : global_env) :=
  map (fun '(kn,gd) => (kn, match gd with
                         | ConstantDecl c => ConstantDecl
                                              (Build_constant_body
                                                 c.(cst_type)
                                                 None
                                                 c.(cst_universes))
                         | _ => gd
                         end)) Σ.

Definition GE' := List.filter (fun '(n, _) => negb (eq_kername n <%% interp %%> )%string) GE.

Import ResultMonad.

Definition e_glob_dec Σ :=
  match erase_global_decls TT_remap_names Σ (todo "") with
  | Err c => inr (string_of_erase_global_decl_error c)
  | Ok e => inl e
  end.

Definition e_glob_dec_rec Σ seeds :=
  match erase_global_decls_deps_recursive TT_remap_names Σ (todo "") seeds with
  | Err c => inr (string_of_erase_global_decl_error c)
  | Ok e => inl e
  end.

Time MetaCoq Run (
         Σ' <- tmEval lazy (Tglobal_decls_deps_recursive TT_remap_names GE [<%% receive %%>]) ;;
         tmDefinition "GE_interp" Σ').

Compute List.length GE_interp.

Definition GE_interp' := List.filter (fun '(n, _) => negb (eq_kername n <%% ext_map %%> )%string) GE_interp.

Compute List.length GE_interp'.

(* Succeeds *)
Time Compute (let Σ := (trans_global (Ast.empty_ext GE_interp)).1 in
              e_glob_dec Σ).

(* Fails and complains about dependencies *)
Compute (
    let Σ := (trans_global (Ast.empty_ext GE_interp)).1 in
    e_glob_dec_rec Σ [<%% interp %%>]).

Compute (specialize_erase_debox_template_env GE_interp [<%% interp %%>] TT_remap_names).

(* Hangs forever *)
Compute (specialize_erase_debox_template_env GE [<%% interp %%>] TT_remap_names).


(* Hangs forever*)
(* Compute ( *)
(*     let Σ := (trans_global (Ast.empty_ext GE)).1 in *)
(*     SafeErasureFunction.erase_global Σ (todo "")). *)


Time Compute (let Σ := (trans_global (Ast.empty_ext (firstn 182 GE))).1 in
          e_glob_dec Σ).

Time MetaCoq Run (
       c <- tmQuoteConstant <%% interp %%> false ;;
       print_nf (erase_print_deboxed_all_applied "" TT (clear_bodies GE) <%% interp %%> c)).
(*           ). *)
(* MetaCoq Run ( *)
(*           let GE' := List.filter (fun '(n, _) => negb (eq_kername n <%% interp %%> )%string) GE in *)
(*           let Σ := (trans_global (Ast.empty_ext GE')).1 in *)
(*           p <- tmQuoteConstant <%% interp %%> false;; *)
(*           let pp := (trans_constant_body p) in *)
(*           match erase_constant_decl (P.empty_ext Σ) (todo "") pp (todo "") with *)
(*           | ResultMonad.Ok t1 => *)
(*             let GE' := (GE' ++ [(<%%interp%%>,ConstantDecl t1)])%list in *)
(*             print_nf GE' *)
(*             (* tmDefinition "GE'" (GE' ++ [(<%%interp%%>,t1)])%list *) *)
(*           | ResultMonad.Err e => print_nf e *)
(*           end). *)
(** We translate required definitions and print them into a single string containing the whole program. The definition with the corresponding code is added to Coq's environment. *)
Time MetaCoq Run (printLiquidityModule PREFIX GE TT INTERP_MODULE).

(** The extracted program can be printed and copy-pasted to the online Liquidity editor *)
Print liquidity_interp.

(** or redirected to a file, creating "interp.liq.out".
 The contents require further post-processing to be compiled with the Liquidity compiler.*)
Redirect "interp.liq" Compute liquidity_interp. (* creates "interp.liq.out"*)
