From Coq Require Import PeanoNat ZArith.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import SafeTemplateErasure.
From MetaCoq.Erasure Require ErasureFunction.
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.Template Require Import Kernames config.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC.

From MetaCoq.Template Require Pretty.

From ConCert.Extraction Require Import ResultMonad.
From ConCert.Execution Require Import Blockchain Serializable.

From ConCert.Extraction Require Import CameLIGOPretty
     Common ExAst Erasure Optimize Extraction TypeAnnotations Annotations Utils.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.


Definition to_constant_decl (gd : option T.global_decl) :=
  match gd with
  | Some (ConstantDecl cst_body) => ret cst_body
  | Some (InductiveDecl cst_body) => tmFail "Error (constant expected, given inductive)"
  | None => tmFail "Error (expected constant with a body)"
  end.

Record CameLIGOMod {Base : ChainBase} (msg ctx setup storage operation : Type) :=
  { lmd_module_name : string ;
    lmd_prelude : string ;
    lmd_init : ctx -> setup -> option storage;
    lmd_init_prelude : string ;
    lmd_receive : Chain -> ctx -> storage -> option msg -> option (list operation * storage);
    lmd_entry_point : string }.

Arguments lmd_module_name {_ _ _ _ _ _}.
Arguments lmd_prelude {_ _ _ _ _ _}.
Arguments lmd_init {_ _ _ _ _ _}.
Arguments lmd_init_prelude {_ _ _ _ _ _}.
Arguments lmd_receive {_ _ _ _ _ _}.
Arguments lmd_entry_point {_ _ _ _ _ _}.

Definition printCameLIGODefs (prefix : string) (Σ : global_env)
           (TT : MyEnv.env string)
           (temp_env : extract_template_env_params)
           (ignore : list kername)
           (build_call_ctx : string)
           (init_prelude : string)
           (init : kername)
           (receive : kername)
  : string + string :=
  let seeds := KernameSet.union (KernameSet.singleton init) (KernameSet.singleton receive) in
  match annot_extract_template_env_specalize temp_env Σ seeds (fun k => List.existsb (eq_kername k) ignore) with
  (* match extract_template_env_within_coq Σ seeds (fun k => List.existsb (eq_kername k) ignore) with *)
  | Ok (eΣ; annots) => 
    (* dependencies should be printed before the dependent definitions *)
    let ldef_list := List.rev (print_global_env prefix TT eΣ annots) in
    (* filtering empty strings corresponding to the ignored definitions *)
    let ldef_list := filter (negb ∘ (String.eqb "") ∘ snd) ldef_list in
    match bigprod_find (fun '(k, _, _) _ => eq_kername k init) annots with
    | Some ((_, ExAst.ConstantDecl init_cst); annots) =>
      match print_init prefix TT build_call_ctx init_prelude eΣ init_cst annots with
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


Definition CameLIGO_ignore_default {Base : ChainBase} :=
  [<%% prod %%>; <%% @Chain %%>; <%% ChainBase %%>].

(* We assume the structure of the context from the [PreludeExt]:
  current_time , sender_addr, sent_amount, acc_balance *)
Definition CameLIGO_call_ctx :=
  "(Tezos.now,
   (Tezos.source,
   (Tezos.amount,
    Tezos.balance)))".

Definition CameLIGO_extract_args :=
  {| check_wf_env_func := check_wf_env_func extract_within_coq;
     pcuic_args :=
       {| dearg_args :=
            Some
              {| do_trim_const_masks := true;
                 do_trim_ctor_masks := false; (* cannot have partially applied ctors *)
                 check_closed := true;
                 check_expanded := true;
                 check_valid_masks := true |} |} |}.

Definition wrap_in_delimiters s :=
  String.concat nl [""; s].

Definition CameLIGO_extraction {Base : ChainBase} {msg ctx params storage operation : Type}
           (prefix : string)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (m : CameLIGOMod msg ctx params storage operation) :=
  '(Σ,_) <- tmQuoteRecTransp m false ;;
  init_nm <- extract_def_name m.(lmd_init);;
  receive_nm <- extract_def_name m.(lmd_receive);;
  let ignore := (map fst TT_defs ++ CameLIGO_ignore_default)%list in
  let TT :=
      (TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
  p <- tmEval lazy
             (printCameLIGODefs prefix Σ TT CameLIGO_extract_args ignore
                                 CameLIGO_call_ctx
                                 m.(lmd_init_prelude)
                                 init_nm receive_nm) ;;
  match p with
  | inl s =>
    tmEval lazy
           (wrap_in_delimiters (concat (nl ++ nl) [m.(lmd_prelude); s; m.(lmd_entry_point)]))
  | inr s => tmFail s
  end.
