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
                            true
                            false (* cannot have partially applied ctors *)
                            true
                            true
                            true
                           ] |}.

Import PCUICAst PCUICTyping.
Definition annot_extract_env_cameligo
           (Σ : PCUICAst.global_env)
           (wfΣ : ∥wf Σ∥)
           (include : KernameSet.t)
           (ignore : kername -> bool) : option (∑ Σ, env_annots box_type Σ).
Proof.
  unshelve epose proof (annot_extract_pcuic_env cameligo_args Σ wfΣ include ignore _).
  - constructor; [|constructor].
    apply annot_dearg_transform.
  - destruct extract_pcuic_env; [|exact None].
    exact (Some (t; X)).
Defined.


Definition annot_extract_template_env_specalize
           (e : TemplateEnvironment.global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result (∑ e, env_annots box_type e) string :=
  let e := SafeTemplateChecker.fix_global_env_universes e in
  let e := TemplateToPCUIC.trans_global_decls e in
  e <- specialize_ChainBase_env e ;;
  wfe <-check_wf_env_func extract_within_coq e;;
  match annot_extract_env_cameligo e wfe seeds ignore with
  | Some s => Ok s
  | None => Err "failed internally in annot_extract_template_env_specalize"
  end.

Definition printCameLIGODefs (prefix : string) (Σ : TemplateEnvironment.global_env)
           (TT : MyEnv.env string)
           (ignore : list kername)
           (build_call_ctx : string)
           (init_prelude : string)
           (receive_prelude : string)
           (init : kername)
           (receive : kername)
  : string + string :=
  let seeds := KernameSet.union (KernameSet.singleton init) (KernameSet.singleton receive) in
  match annot_extract_template_env_specalize Σ seeds (fun k => List.existsb (eq_kername k) ignore) with
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
        (* and place receive_prelude after type decls and before constant decls *)
        let defs : list string :=
          ldef_const_list |> filter (negb ∘ (eq_kername init) ∘ fst)
                          |> map snd
                          |> List.app [receive_prelude] (* append const decls after receive prelude decls *)
                          |> List.app (map snd ldef_ty_list) (* append the above after ty decls*)
                          in
          (* map snd (filter (negb ∘ (eq_kername init) ∘ fst) ldef_list) in *)
        let res : string :=
            String.concat (nl ++ nl) (defs ++ (cons init_code nil)) in
        inl res
      | None => inr "Error: Empty body for init"
      end
    | Some _ => inr "Error: init must be a constant"
    | None => inr "Error: No init found"
    end
  | Err e => inr e
  end.


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
Definition CameLIGO_extraction {Base : ChainBase} {msg ctx params storage operation : Type}
           (prefix : string)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (m : CameLIGOMod msg ctx params storage operation) :=
  '(Σ,_) <- tmQuoteRecTransp m false ;;
  init_nm <- extract_def_name m.(lmd_init);;
  receive_nm <- extract_def_name m.(lmd_receive);;
  let TT_defs := TT_defs ++ TT_remap_default in
  let ignore := (map fst TT_defs ++ CameLIGO_ignore_default)%list in
  let TT :=
      (CameLIGO_rename_default ++ TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
  p <- tmEval lazy
             (printCameLIGODefs prefix Σ TT ignore
                                 CameLIGO_call_ctx
                                 m.(lmd_init_prelude)
                                 m.(lmd_receive_prelude)
                                 init_nm receive_nm) ;;
  match p with
  | inl s =>
    tmEval lazy
           (wrap_in_delimiters (String.concat (nl ++ nl) [m.(lmd_prelude); s; m.(lmd_entry_point)]))
  | inr s => tmFail s
  end.
