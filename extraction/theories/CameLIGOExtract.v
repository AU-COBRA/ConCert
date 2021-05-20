From Coq Require Import PeanoNat ZArith.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Erasure.
From MetaCoq.Erasure Require ErasureFunction.
From MetaCoq.Template Require Import Kernames config.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC.

From MetaCoq.Template Require Pretty.

From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import CertifyingInlining.
From ConCert.Utils Require Import RecordSet RecordUpdate StringExtra.
From ConCert.Execution Require Import Blockchain Serializable.

From ConCert.Extraction Require Import CameLIGOPretty
     Common ExAst Erasure Optimize Extraction TypeAnnotations Annotations Utils SpecializeChainBase.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.
From MetaCoq.PCUIC Require PCUICAst PCUICTyping.

Record CameLIGOMod {Base : ChainBase} (msg ctx setup storage operation : Type) :=
  { lmd_module_name : string ;
    lmd_prelude : string ;
    lmd_init : ctx -> setup -> option storage;
    lmd_init_prelude : string ;
    lmd_receive_prelude : string;
    lmd_receive : Chain -> ctx -> storage -> option msg -> option (list operation * storage);
    lmd_entry_point : string }.

Arguments lmd_module_name {_ _ _ _ _ _}.
Arguments lmd_prelude {_ _ _ _ _ _}.
Arguments lmd_init {_ _ _ _ _ _}.
Arguments lmd_init_prelude {_ _ _ _ _ _}.
Arguments lmd_receive {_ _ _ _ _ _}.
Arguments lmd_receive_prelude {_ _ _ _ _ _}.
Arguments lmd_entry_point {_ _ _ _ _ _}.

Definition cameligo_args :=
       {| optimize_prop_discr := true;
               extract_transforms := [Optimize.dearg_transform
                              (fun _ => None)
                              true
                              false (* cannot have partially applied ctors *)
                              true
                              true
                              true] |}.

Import PCUICAst PCUICTyping.
Definition annot_extract_env_cameligo
           (Σ : PCUICAst.global_env)
           (wfΣ : ∥wf Σ∥)
           (include : KernameSet.t)
           (ignore : list kername) : result (∑ Σ, env_annots box_type Σ) string.
Proof.
  (* set (extract_cameligo_params inline) as params. *)
  set (fun kn => existsb (eq_kername kn) ignore) as to_ignore.
  unshelve epose proof (annot_extract_pcuic_env cameligo_args Σ wfΣ include to_ignore _).
  - subst;cbn;constructor; [|constructor].
    apply annot_dearg_transform.
  - destruct extract_pcuic_env.
    * exact (Ok (t; X)).
    * exact (Err e).
Defined.


Program Definition annot_extract_template_env_specalize
           (e : TemplateEnvironment.global_env)
           (seeds : KernameSet.t)
           (ignore : list kername) : result (∑ e, env_annots box_type e) string :=
  let e := SafeTemplateChecker.fix_global_env_universes e in
  let e := TemplateToPCUIC.trans_global_decls e in
  e <- specialize_ChainBase_env e ;;
  wfe <-check_wf_env_func extract_within_coq e;;
  annot_extract_env_cameligo e wfe seeds ignore.

Definition CameLIGO_ignore_default {Base : ChainBase} :=
  [
      <%% prod %%>
    ; <%% @Chain %%>
    ; <%% @ActionBody %%>
    ; <%% @ChainBase %%>
    ; <%% axiomatized_ChainBase %%>
    ; <%% Amount %%>
    ; <%% @Address %%>
    ; <%% @address_eqdec %%>
    ; <%% @address_countable %%>
    ; <%% @ContractCallContext %%>
    ; <%% @ctx_from %%>
    ; <%% @ctx_amount %%>
    ; <%% @ctx_contract_address %%>
    ; <%% @SerializedValue %%>
    ; <%% @SerializedType %%>
  ].

Definition TT_remap_default : list (kername * string) :=
  [
    (* types *)
    remap <%% Z %%> "tez"
  ; remap <%% N %%> "nat"
  ; remap <%% nat %%> "nat"
  ; remap <%% bool %%> "bool"
  ; remap <%% unit %%> "unit"
  ; remap <%% list %%> "list"
  ; remap <%% @fst %%> "fst"
  ; remap <%% @snd %%> "snd"
  ; remap <%% option %%> "option"
  ; remap <%% gmap.gmap %%> "map"
  ; remap <%% positive %%> "nat"
  ; remap <%% Amount %%> "tez"
  ; remap <%% @Address %%> "address"
  (* ; remap <%% @ContractCallContext %%> "(adress * (address * int))" *)

  (* operations *)
  ; remap <%% List.fold_left %%> "List.fold"
  ; remap <%% Pos.add %%> "addNat"
  ; remap <%% Pos.sub %%> "subNat"
  ; remap <%% Pos.leb %%> "leNat"
  ; remap <%% Pos.eqb %%> "eqNat"
  ; remap <%% Z.add %%> "addTez"
  ; remap <%% Z.sub %%> "subTez"
  ; remap <%% Z.leb %%> "leTez"
  ; remap <%% Z.ltb %%> "ltTez"
  ; remap <%% Z.eqb %%> "eqTez"
  ; remap <%% Z.gtb %%> "gtbTez"
  ; remap <%% N.add %%> "addInt"
  ; remap <%% N.sub %%> "subInt"
  ; remap <%% N.leb %%> "leInt"
  ; remap <%% N.ltb %%> "ltInt"
  ; remap <%% N.eqb %%> "eqInt"
  ; remap <%% andb %%> "andb"
  ; remap <%% negb %%> "not"
  ; remap <%% orb %%> "orb"

  (* Maps *)
  ; remap <%% @stdpp.base.insert %%> "Map.add"
  ; remap <%% @stdpp.base.lookup %%> "Map.find_opt"
  ; remap <%% @stdpp.base.empty %%> "Map.empty"
  ; remap <%% @address_eqdec %%> ""
  ; remap <%% @address_countable %%> ""
  ].

Definition CameLIGO_rename_default :=
  [
      ("to", "to_")
    ; ("amount", "amount_")
    ; ("continue", "continue_")
  ].

(* We assume the structure of the context from the [PreludeExt]:
  current_time , sender_addr, sent_amount, acc_balance *)
Definition CameLIGO_call_ctx :=
  "(Tezos.now,
   (Tezos.sender,
   (Tezos.amount,
    Tezos.balance)))".

Definition wrap_in_delimiters s :=
  String.concat nl [""; s].

Definition is_empty {A} (xs : list A) :=
  match xs with
  | [] => true
  | _ => false
  end.

Definition printCameLIGODefs `{ChainBase} {Base : ChainBase} {msg ctx params storage operation : Type}
           (prefix : string)
           (Σ : TemplateEnvironment.global_env)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (build_call_ctx : string)
           (init : kername)
           (receive : kername)
           (m : CameLIGOMod msg ctx params storage operation)
  : string + string :=
  let prelude := m.(lmd_prelude) in
  let init_prelude := m.(lmd_init_prelude) in
  let entry_point := m.(lmd_entry_point) in
  let seeds := KernameSet.union (KernameSet.singleton init) (KernameSet.singleton receive) in
  let TT_defs := TT_defs ++ TT_remap_default in
  let ignore := (map fst TT_defs ++ CameLIGO_ignore_default)%list in
  let TT :=
      (CameLIGO_rename_default ++ TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
  match annot_extract_template_env_specalize Σ seeds ignore with
  | Ok (eΣ; annots) =>
    (* dependencies should be printed before the dependent definitions *)
    let ldef_list := List.rev (print_global_env prefix TT eΣ annots) in
    (* filtering empty strings corresponding to the ignored definitions *)
    let not_empty_str := (negb ∘ (String.eqb "") ∘ snd) in

    let ldef_ty_list := ldef_list
                          |> filter (fun d => match d with TyDecl _ => true | _ => false end)
                          |> map (fun d => match d with ConstDecl d' => d' | TyDecl d' => d' end)
                          |> filter not_empty_str in
    let ldef_const_list := ldef_list
                            |> filter (fun d => match d with ConstDecl _ => true | _ => false end)
                            |> map (fun d => match d with ConstDecl d' => d' | TyDecl d' => d' end)
                            |> filter not_empty_str in
    (* look for init function *)
    match bigprod_find (fun '(k, _, _) _ => eq_kername k init) annots with
    | Some ((_, ExAst.ConstantDecl init_cst); annots) =>
      match print_init prefix TT build_call_ctx init_prelude eΣ init_cst annots with
      | Some init_code =>
        (* filtering out the definition of [init] and projecting the code *)
        (* and place prelude after type decls and before constant decls *)
        let defs : list string :=
          ldef_const_list |> filter (negb ∘ (eq_kername init) ∘ fst)
                          |> map snd
                          |> List.app [prelude] (* append const decls after receive prelude decls *)
                          |> List.app (map snd ldef_ty_list) (* append the above after ty decls*)
                          in
          (* map snd (filter (negb ∘ (eq_kername init) ∘ fst) ldef_list) in *)
        let res : string :=
            String.concat (nl ++ nl) (defs ++ (cons init_code nil)) in
        (wrap_in_delimiters (String.concat (nl ++ nl) [prelude; res; entry_point])) |> inl
      | None => inr "Error: Empty body for init"
      end
    | Some _ => inr "Error: init must be a constant"
    | None => inr "Error: No init found"
    end
  | Err e => inr e
  end.


Definition unwrap_string_sum (s : string + string) : string :=
  match s with
  | inl v => v
  | inr v => v
  end.

Definition quote_and_preprocess {Base : ChainBase}
           {msg ctx params storage operation : Type}
           (inline : list kername)
           (m : CameLIGOMod msg ctx params storage operation)
  : TemplateMonad (TemplateEnvironment.global_env * kername * kername) :=
   (* we compute with projections before quoting to avoid unnecessary dependencies to be quoted *)
   init <- tmEval cbn m.(lmd_init);;
   receive <-tmEval cbn m.(lmd_receive);;
  '(Σ,_) <- tmQuoteRecTransp (init,receive) false ;;
  init_nm <- extract_def_name m.(lmd_init);;
  receive_nm <- extract_def_name m.(lmd_receive);;
  Σ <-
  (if is_empty inline then ret Σ
   else
     let to_inline kn := existsb (eq_kername kn) inline in
     Σcert <- tmEval lazy (inline_in_env to_inline Σ) ;;
     mpath <- tmCurrentModPath tt;;
     Certifying.gen_defs_and_proofs Σ Σcert mpath "_cert_pass"
                                    (KernameSetProp.of_list [init_nm;receive_nm]);;
     ret Σcert);;
  ret (Σ, init_nm,receive_nm).

(** Runs all the necessary steps in [TemplateMonad] and adds a definition
    [<module_name>_prepared] to the Coq environment.
    The definition consist of a call to erasure and pretty-printing for further
    evaluation outside of [TemplateMonad], using, e.g. [Eval vm_compute in],
    which is much faster than running the computations inside [TemplateMonad]. *)
Definition CameLIGO_prepare_extraction {Base : ChainBase} {msg ctx params storage operation : Type}
           (prefix : string)
           (inline : list kername)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (m : CameLIGOMod msg ctx params storage operation) :=
  '(Σ, init_nm, receive_nm) <- quote_and_preprocess inline m;;
  let TT_defs := TT_defs ++ TT_remap_default in
  let TT :=
      (CameLIGO_rename_default ++ TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
  let res := unwrap_string_sum (printCameLIGODefs prefix
                                                  Σ
                                                  TT_defs TT_ctors
                                                  CameLIGO_call_ctx
                                                  init_nm receive_nm
                                                  m) in
  tmDefinition (m.(lmd_module_name) ^ "_prepared") res.

(** Bundles together quoting, inlining, erasure and pretty-printing.
    Convenient to use, but might be slow, becase performance of [tmEval lazy] is not great. *)
Definition CameLIGO_extract {Base : ChainBase} {msg ctx params storage operation : Type}
           (prefix : string)
           (inline : list kername)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (m : CameLIGOMod msg ctx params storage operation) :=
  '(Σ, init_nm, receive_nm) <- quote_and_preprocess inline m;;
  let TT_defs := TT_defs ++ TT_remap_default in
  let TT :=
      (CameLIGO_rename_default ++ TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
  p <- tmEval lazy
             (printCameLIGODefs prefix
                                Σ
                                TT_defs TT_ctors
                                CameLIGO_call_ctx
                                init_nm receive_nm
                                m) ;;
  match p with
  | inl s =>
    tmEval lazy
           (wrap_in_delimiters (String.concat (nl ++ nl) [m.(lmd_prelude); s; m.(lmd_entry_point)]))
  | inr s => tmFail s
  end.

(** A simplified erasure/prinitng intended moslty for testing purposes *)
Definition simple_def_print prefix TT_defs TT_ctors seeds prelude harness Σ
  : string + string :=
  let TT_defs := TT_defs ++ TT_remap_default in
  let ignore := map fst TT_defs in
  let TT := (CameLIGO_rename_default ++ TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
  match annot_extract_template_env_specalize Σ seeds ignore with
  | Ok annot_env =>
  let '(eΣ; annots) := annot_env in
      (* dependencies should be printed before the dependent definitions *)
  let ldef_list := List.rev (print_global_env prefix TT eΣ annots) in
    (* filtering empty strings corresponding to the ignored definitions *)
    let not_empty_str := (negb ∘ (String.eqb "") ∘ snd) in

    let ldef_ty_list := ldef_list
                          |> filter (fun d => match d with TyDecl _ => true | _ => false end)
                          |> map (fun d => match d with ConstDecl d' => d' | TyDecl d' => d' end)
                          |> filter not_empty_str in
    let ldef_const_list := ldef_list
                            |> filter (fun d => match d with ConstDecl _ => true | _ => false end)
                            |> map (fun d => match d with ConstDecl d' => d' | TyDecl d' => d' end)
                            |> filter not_empty_str in
    let defs : list string :=
        ldef_const_list  |> map snd
                         |> List.app (map snd ldef_ty_list) in
    String.concat (nl ^ nl) (prelude :: defs ++ [harness]) |> inl
  | Err e => inr e
  end.

(** Quoting and inlining for a single definition.
    Intended mostly for testing purposes *)
Definition quote_and_preprocess_one_def {A}
           (inline : list kername)
           (def : A)
  : TemplateMonad (TemplateEnvironment.global_env * kername) :=
  '(Σ,_) <- tmQuoteRecTransp def false ;;
  def_nm <- extract_def_name def;;
  Σ <-(if is_empty inline then ret Σ
      else
        let to_inline kn := existsb (eq_kername kn) inline in
        Σcert <- tmEval lazy (inline_in_env to_inline Σ) ;;
        mpath <- tmCurrentModPath tt;;
        Certifying.gen_defs_and_proofs Σ Σcert mpath "_cert_pass" (KernameSetProp.of_list [def_nm]);;
        ret Σcert);;
  ret (Σ,def_nm).

(** Extraction for testing purposes.
    Simply prints the definitions and allows for appending a prelude and a
    hand-written harness code to run the extracted definition.
    The harness is just a piece of code with definitions
    of [storage], [main], etc.*)
Definition CameLIGO_extract_single {A}
           (prefix : string)
           (inline : list kername)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (prelude : string)
           (harness: string)
           (def : A) : TemplateMonad string :=
  '(Σ,def_nm) <- quote_and_preprocess_one_def inline def ;;
  let seeds := KernameSetProp.of_list [def_nm] in
  tmEval lazy (unwrap_string_sum (simple_def_print prefix TT_defs TT_ctors (KernameSet.singleton def_nm) prelude harness Σ)).

(** Similar to [CameLIGO_prepare_extraction], but for a single definition  *)
Definition CameLIGO_prepare_extraction_single {A}
           (prefix : string)
           (inline : list kername)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (prelude : string)
           (harness: string)
           (def : A) : TemplateMonad string :=
    '(Σ,def_nm) <- quote_and_preprocess_one_def inline def ;;
    let seeds := KernameSetProp.of_list [def_nm] in
    tmDefinition (def_nm.2 ^ "_prepared") (unwrap_string_sum (simple_def_print prefix TT_defs TT_ctors (KernameSet.singleton def_nm) prelude harness Σ)).
