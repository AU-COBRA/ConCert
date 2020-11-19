From Coq Require Import PeanoNat ZArith.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require ErasureFunction.
From MetaCoq.Template Require Import Kernames config.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC.

From MetaCoq.Template Require Pretty.

From ConCert.Execution Require Import Blockchain Serializable.

From ConCert.Embedding Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.

From ConCert.Extraction Require Import LPretty
     Common ExAst Erasure Optimize Extraction.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import AcornBlockchain.
Import MonadNotation.
Import ResultMonad.

Definition to_constant_decl (gd : option Ast.global_decl) :=
  match gd with
  | Some (ConstantDecl cst_body) => ret cst_body
  | Some (InductiveDecl cst_body) => tmFail "Error (constant expected, given inductive)"
  | None => tmFail "Error (expected constant with a body)"
  end.

Record LiquidityMod (msg init_ctx params storage operation : Type) :=
  { lmd_module_name : string ;
    lmd_prelude : string ;
    lmd_init : init_ctx -> params -> option storage;
    lmd_init_prelude : string ;
    lmd_receive : msg -> storage -> option (list operation * storage);
    lmd_entry_point : string }.

Arguments lmd_module_name {_ _ _ _ _}.
Arguments lmd_prelude {_ _ _ _ _}.
Arguments lmd_init {_ _ _ _ _}.
Arguments lmd_init_prelude {_ _ _ _ _}.
Arguments lmd_receive {_ _ _ _ _}.
Arguments lmd_entry_point {_ _ _ _ _}.


Definition printLiquidityDefs (prefix : string) (Σ : global_env)
           (TT : MyEnv.env string)
           (ignore : list kername)
           (build_call_ctx : string)
           (init_prelude : string)
           (init : kername)
           (receive : kername)
  : string + string :=
  let seeds := KernameSet.union (KernameSet.singleton init) (KernameSet.singleton receive) in
  match extract_template_env_within_coq Σ seeds (fun k => List.existsb (eq_kername k) ignore) with
  | Ok eΣ =>
    (* dependencies should be printed before the dependent definitions *)
    let ldef_list := List.rev (print_global_env prefix TT eΣ) in
    (* filtering empty strings corresponding to the ignored definitions *)
    let ldef_list := filter (negb ∘ (String.eqb "") ∘ snd) ldef_list in
    match ExAst.lookup_env eΣ init with
    | Some (ExAst.ConstantDecl init_cst) =>
      match print_init prefix TT build_call_ctx init_prelude eΣ init_cst with
      | Some init_code =>
        (* filtering out the definition of [init] and projecting the code *)
        let defs :=
            map snd (filter (negb ∘ (eq_kername init) ∘ fst) ldef_list) in
        let res :=
            concat (nl ++ nl) (defs ++[ init_code ]) %list in
        inl res
      | None => inr "Error: Empty body for init"
      end
    | Some _ => inr "Error: init must be a constant"
    | None => inr "Error: No init found"
    end
  | Err e => inr e
  end.

Definition liquidity_ignore_default :=
  [<%% prod %%>].

(* We assume the structure of the context from the [PreludeExt]:
  current_time , sender_addr, sent_amount, acc_balance *)
Definition liquidity_call_ctx :=
  "(Current.time (),
   (Current.sender (),
   (Current.amount (),
    Current.balance ())))".

Definition liquidity_extract_args :=
  {| check_wf_env_func := check_wf_env_func extract_within_coq;
     pcuic_args :=
       {| optimize_prop_discr := true;
          transforms := [dearg_transform
                           true
                           false (* cannot have partially applied ctors *)
                           true
                           true
                           true] |} |}.

Definition liquidity_simple_extract
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (extract_deps : bool)
           (p : program) : string + string :=
  match p.2 with
  | tConst kn _ =>
    let seeds := KernameSet.singleton kn in
    let ignore := if extract_deps then fun _ => false else fun kn' => negb (eq_kername kn' kn)  in
    let TT :=
      (TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
    match extract_template_env liquidity_extract_args p.1 seeds ignore with
    | Ok eΣ =>
      (* dependencies should be printed before the dependent definitions *)
      let ldef_list := List.rev (print_global_env "" TT eΣ) in
      (* filtering empty strings corresponding to the ignored definitions *)
      let ldef_list := filter (negb ∘ (String.eqb "") ∘ snd) ldef_list in
      let defs := map snd ldef_list in
      inl (concat (nl ++ nl) defs) %list
    | Err e => inr e
    end
  | _ => inr "Constant expected"
  end.

Definition wrap_in_delimiters s :=
  String.concat nl ["";"(*START*)"; s; "(*END*)"].

Definition liquidity_extraction {msg ctx params storage operation : Type}
           (prefix : string)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (m : LiquidityMod msg ctx params storage operation) :=
  '(Σ,_) <- tmQuoteRecTransp m false ;;
  init_nm <- extract_def_name m.(lmd_init);;
  receive_nm <- extract_def_name m.(lmd_receive);;
  let ignore := (map fst TT_defs ++ liquidity_ignore_default)%list in
  let TT :=
      (TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
  p <- tmEval lazy
             (printLiquidityDefs prefix Σ TT ignore
                                 liquidity_call_ctx
                                 m.(lmd_init_prelude)
                                 init_nm receive_nm) ;;
  match p with
  | inl s =>
    tmEval lazy
           (wrap_in_delimiters (concat (nl ++ nl) [m.(lmd_prelude); s; m.(lmd_entry_point)]))
  | inr s => tmFail s
  end.
