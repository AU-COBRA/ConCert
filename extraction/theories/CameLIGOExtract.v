From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import ZArith_base.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require ResultMonad.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import SpecializeChainBase.
From MetaCoq.Erasure.Typed Require Import CertifyingInlining.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import Optimize.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure.Typed Require Import Utils.
From ConCert.Utils Require Import Env.
From MetaCoq.Utils Require Import monad_utils.
From MetaCoq.Utils Require Import MCSquash.
From MetaCoq.Utils Require Import MCPrelude.
From MetaCoq.Utils Require Import MCProd.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Template Require Import TemplateMonad.

Import MCMonadNotation ListNotations.

Record CameLIGOMod {Base : ChainBase} (msg ctx setup storage operation error : Type) :=
  { lmd_module_name : string ;
    lmd_prelude : string ;
    lmd_init : setup -> ConCert.Execution.ResultMonad.result storage error;
    lmd_init_prelude : string ;
    lmd_receive_prelude : string;
    lmd_receive : Chain -> ctx -> storage -> option msg -> ConCert.Execution.ResultMonad.result (list operation * storage) error;
    lmd_entry_point : string }.

Arguments lmd_module_name {_ _ _ _ _ _ _}.
Arguments lmd_prelude {_ _ _ _ _ _ _}.
Arguments lmd_init {_ _ _ _ _ _ _}.
Arguments lmd_init_prelude {_ _ _ _ _ _ _}.
Arguments lmd_receive {_ _ _ _ _ _ _}.
Arguments lmd_receive_prelude {_ _ _ _ _ _ _}.
Arguments lmd_entry_point {_ _ _ _ _ _ _}.

(* We override masks for *some* constants that have only logical parameters, like
   [@AddressMap.empty]. Our optimization conservatively keeps one parameter
   if all the parameters are logical. This is necessary because such definitions
   might use something like [false_rect] and removing all the arguments will force
   evaluating their bodies, which can lead to an exception or looping depending
   on how the elimination from the empty types is implemented.
   However, for [AddressMap.empty] is completely safe to remove all arguments,
   since it's an abbreviation for a constructor. *)
Definition overridden_masks (kn : kername) : option bitmask :=
  if eq_kername kn <%% @AddressMap.empty %%> then Some [true]
  else None.

Definition cameligo_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [Optimize.dearg_transform
                                   overridden_masks
                                   true
                                   false (* cannot have partially applied ctors *)
                                   true
                                   true
                                   true] |}.

Import PCUICAst PCUICTyping.
Import bytestring.
Definition annot_extract_env_cameligo
           (Σ : PCUICEnvironment.global_env)
           (wfΣ : ∥wf Σ∥)
           (include : KernameSet.t)
           (ignore : list kername) : result (∑ Σ, env_annots box_type Σ) string.
Proof.
  (* set (extract_cameligo_params inline) as params. *)
  set (fun kn => existsb (eq_kername kn) ignore) as to_ignore.
  unshelve epose proof (annot_extract_pcuic_env cameligo_args Σ wfΣ include to_ignore _).
  - subst; cbn; constructor; [|constructor].
    apply annot_dearg_transform.
  - destruct extract_pcuic_env.
    * exact (Ok (t; X)).
    * exact (Err e).
Defined.

Definition blah : Monad (fun A => result A string) := _.

Program Definition annot_extract_template_env_specalize
           (e : Ast.Env.global_env)
           (seeds : KernameSet.t)
           (ignore : list kername) : result_string (∑ e, env_annots box_type e) :=
  let e := TemplateToPCUIC.trans_global_env e in
  e <- specialize_ChainBase_env (PCUICProgram.trans_env_env e) ;;
  wfe <-check_wf_env_func extract_within_coq e;;
  annot_extract_env_cameligo e wfe seeds ignore.



Definition CameLIGO_ignore_default {Base : ChainBase} :=
  [
      <%% prod %%>
    ; <%% @ChainBase %%>
    ; <%% axiomatized_ChainBase %%>
    ; <%% Amount %%>
    ; <%% @Address %%>
    ; <%% @address_eqdec %%>
    ; <%% @address_countable %%>
    ; <%% @ContractCallContext %%>
    ; <%% @SerializedValue %%>
    ; <%% @SerializedType %%>
    ; <%% chain_height %%>
    ; <%% current_slot %%>
    ; <%% finalized_height %%>
  ].

Open Scope string.

Definition TT_remap_default : list (kername * String.string) :=
  [
    (* types *)
    remap <%% Z %%> "tez"
  (* NOTE: subtracting two [nat]s gives [int], so we remap [N] to [int]
    and use truncated subtraction *)
  (* FIXME: this doesn't look right. [N] should be [nat] in CameLIGO and [Z] should be
     [int]. However, [Z] is also used as the type of currency, that could lead to clashes
     in the extracted code. *)
  ; remap <%% N %%> "int"
  ; remap <%% nat %%> "nat"
  ; remap <%% bool %%> "bool"
  ; remap <%% unit %%> "unit"
  ; remap <%% list %%> "list"
  ; remap <%% @fst %%> "fst"
  ; remap <%% @snd %%> "snd"
  ; remap <%% option %%> "option"
  ; remap <%% ConCert.Execution.ResultMonad.result %%> "result"
  ; remap <%% gmap.gmap %%> "map"
  ; remap <%% positive %%> "nat"
  ; remap <%% Amount %%> "tez"
  ; remap <%% @Address %%> "address"
  ; remap <%% @ActionBody %%> "operation"
  ; remap <%% @ContractCallContext %%> CameLIGO_call_ctx_type_name


  (* operations on numbers and currency [tez] *)
  ; remap <%% Nat.add %%> "addN"
  ; remap <%% Nat.leb %%> "lebN"
  ; remap <%% Nat.ltb %%> "ltbN"
  ; remap <%% Nat.mul %%> "multN"

  ; remap <%% Pos.add %%> "addN"
  ; remap <%% Pos.sub %%> "subN"
  ; remap <%% Pos.mul %%> "multN"
  ; remap <%% Pos.leb %%> "leN"
  ; remap <%% Pos.eqb %%> "eqN"
  ; remap <%% Z.add %%> "addTez"
  (* FIXME: subtraction of tez returns option in LIGO now We should
     not use Z.sub directly, but a similar operation that returns
     [option Z] instead. For now, it can be provided and remapped by
     each contract, but ideally it should be in some central place. *)
  (* ; remap <%% Z.sub %%> "subTez" *)
  ; remap <%% Z.mul %%> "multTez"
  ; remap <%% Z.div %%> "divTez"
  ; remap <%% Z.leb %%> "leTez"
  ; remap <%% Z.ltb %%> "ltTez"
  ; remap <%% Z.eqb %%> "eqTez"
  ; remap <%% Z.gtb %%> "gtbTez"
  ; remap <%% Z.even %%> "evenTez"
  ; remap <%% N.add %%> "addInt"
  ; remap <%% N.sub %%> "subIntTruncated"
  ; remap <%% N.leb %%> "leInt"
  ; remap <%% N.ltb %%> "ltInt"
  ; remap <%% N.eqb %%> "eqInt"
  ; remap <%% andb %%> "andb"
  ; remap <%% negb %%> "not"
  ; remap <%% orb %%> "orb"

  (* address *)
  ; remap <%% @address_eqb %%> "eq_addr"

  (* lists *)
  ; remap <%% @List.fold_left %%> "List.fold"
  ; remap <%% @List.map %%> "List.map"
  ; remap <%% @List.find %%> "List.find"
  ; remap <%% @List.length %%> "List.length"
  ; remap <%% @List.app %%> "List.append"

  (* maps *)
  ; remap <%% @stdpp.base.insert %%> "Map.add"
  ; remap <%% @stdpp.base.lookup %%> "Map.find_opt"
  ; remap <%% @stdpp.base.empty %%> "Map.empty"

  (* call context *)
  ; remap <%% @ctx_origin %%> "ctx_origin"
  ; remap <%% @ctx_from %%> "ctx_from"
  ; remap <%% @ctx_contract_address %%> "ctx_contract_address"
  ; remap <%% @ctx_contract_balance %%> "ctx_contract_balance"
  ; remap <%% @ctx_amount %%> "ctx_amount"

  (* blockchain infrastructure *)
  ; remap <%% @ActionBody %%> "operation"
  ; remap <%% @Chain %%> "chain"
  ; remap <%% @chain_height %%> "chain_height"
  ; remap <%% @current_slot %%> "current_slot"
  ; remap <%% @finalized_height %%> "finalized_height"
  ].

Definition TT_rename_ctors_default : list (String.string * String.string) :=
  [ ("nil", "[]")
  ; ("true", "true")
  ; ("false", "false")
  ; ("Some", "Some")
  ; ("None", "None")
  ; ("Ok", "Ok")
  ; ("Err", "Err")
  ; ("tt", "()")].

Definition wrap_in_delimiters s :=
  Strings.String.concat Common.nl [""; s].

Definition is_empty {A} (xs : list A) :=
  match xs with
  | [] => true
  | _ => false
  end.

Section LigoExtract.

  Context `{ChainBase}
          `{CameLIGOPrintConfig}.

  Open Scope list.

  Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
  Local Coercion bytestring.String.to_string : bytestring.String.t >-> String.string.

Definition printCameLIGODefs {msg ctx params storage operation error : Type}
           (Σ : Ast.Env.global_env)
           (TT_defs : list (kername * String.string))
           (TT_ctors : env String.string)
           (extra_ignore : list kername)
           (build_call_ctx : String.string)
           (init : kername)
           (receive : kername)
           (m : CameLIGOMod msg ctx params storage operation error)
           : String.string + String.string :=
  let init_prelude := m.(lmd_init_prelude) in
  let entry_point := m.(lmd_entry_point) in
  let seeds := KernameSet.union (KernameSet.singleton init) (KernameSet.singleton receive) in
  let TT_defs := TT_defs ++ TT_remap_default in
  let ignore := (map fst TT_defs ++ CameLIGO_ignore_default ++ extra_ignore)%list in
  let TT :=
      (TT_ctors ++ map (fun '(kn,d) => (bs_to_s (string_of_kername kn), d)) TT_defs)%list in
  match annot_extract_template_env_specalize Σ seeds ignore with
  | Ok (eΣ; annots) =>
    (* dependencies should be printed before the dependent definitions *)
    let ldef_list := List.rev (print_global_env TT eΣ annots) in
    (* filtering empty strings corresponding to the ignored definitions *)
    let not_empty_str := (negb ∘ (Strings.String.eqb "") ∘ snd) in

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
      match print_init TT build_call_ctx init_prelude eΣ init_cst annots with
      | Some init_code =>
        (* filtering out the definition of [init] and projecting the code *)
        (* and place init prelude after type decls and before constant decls *)
        let defs : list String.string :=
          ldef_const_list |> filter (negb ∘ (eq_kername init) ∘ fst)
                          |> map snd
                          |> List.app (map snd ldef_ty_list) (* append the above after ty decls*)
                          in
        let res : String.string :=
            Strings.String.concat (Common.nl ++ Common.nl) (defs ++ (cons init_code nil)) in
        (wrap_in_delimiters (Strings.String.concat (Common.nl ++ Common.nl) [m.(lmd_prelude); res; entry_point])) |> inl
      | None => inr "Error: Empty body for init"
      end
    | Some _ => inr "Error: init must be a constant"
    | None => inr "Error: No init found"
    end
  | Err e => inr (bs_to_s e)
  end.


Definition unwrap_string_sum (s : String.string + String.string) : String.string :=
  match s with
  | inl v => v
  | inr v => v
  end.

Open Scope bs_scope.

(** A flag that controls whether info about universes is preserved after quoting *)
Definition WITH_UNIVERSES := false.

Definition quote_and_preprocess {Base : ChainBase}
           {msg ctx params storage operation error : Type}
           (inline : list kername)
           (m : CameLIGOMod msg ctx params storage operation error)
           : TemplateMonad (Ast.Env.global_env * kername * kername) :=
   (* we compute with projections before quoting to
      avoid unnecessary dependencies to be quoted *)
   init <- tmEval cbn m.(lmd_init);;
   receive <-tmEval cbn m.(lmd_receive);;
  '(Σ,_) <- tmQuoteRecTransp (init,receive) false ;;
  init_nm <- extract_def_name m.(lmd_init);;
  receive_nm <- extract_def_name m.(lmd_receive);;
  decls <-
  (if is_empty inline then ret (Ast.Env.declarations Σ)
   else
     let decls := Ast.Env.declarations Σ in
     let to_inline kn := existsb (eq_kername kn) inline in
     Σcert <- tmEval lazy (inline_globals to_inline decls) ;;
     mpath <- tmCurrentModPath tt;;
     Certifying.gen_defs_and_proofs decls Σcert mpath "_cert_pass"
                                    (KernameSetProp.of_list [init_nm; receive_nm]);;
     ret Σcert);;
  Σret <- tmEval lazy (if WITH_UNIVERSES then
                         Ast.Env.mk_global_env (Ast.Env.universes Σ) decls (Ast.Env.retroknowledge Σ)
                       else
                         Ast.Env.mk_global_env (ContextSet.empty) decls (Ast.Env.retroknowledge Σ));;
  ret (Σret, init_nm,receive_nm).

(** Runs all the necessary steps in [TemplateMonad] and adds a definition
    [<module_name>_prepared] to the Coq environment.
    The definition consist of a call to erasure and pretty-printing for further
    evaluation outside of [TemplateMonad], using, e.g. [Eval vm_compute in],
    which is much faster than running the computations inside [TemplateMonad]. *)
Definition CameLIGO_prepare_extraction {msg ctx params storage operation error : Type}
           (inline : list kername)
           (TT_defs : list (kername * String.string))
           (TT_ctors : env String.string)
           (extra_ignore : list kername)
           (build_call_ctx : String.string)
           (m : CameLIGOMod msg ctx params storage operation error) :=
  '(Σ, init_nm, receive_nm) <- quote_and_preprocess inline m;;
  let TT_defs := (TT_defs ++ TT_remap_default)%list in
  let TT :=
    (TT_ctors ++ map (fun '(kn,d) => (bs_to_s (string_of_kername kn), d)) TT_defs)%list in
  let res := unwrap_string_sum (printCameLIGODefs Σ TT_defs TT_ctors extra_ignore
                                                  build_call_ctx
                                                  init_nm receive_nm
                                                  m) in
  tmDefinition (bytestring.String.of_string (m.(lmd_module_name) ^ "_prepared")) res.

(** Bundles together quoting, inlining, erasure and pretty-printing.
    Convenient to use, but might be slow, because performance of [tmEval lazy] is not great. *)
Definition CameLIGO_extract {msg ctx params storage operation error : Type}
           (inline : list kername)
           (TT_defs : list (kername * String.string))
           (TT_ctors : env String.string)
           (extra_ignore : list kername)
           (build_call_ctx : String.string)
           (m : CameLIGOMod msg ctx params storage operation error)
           : TemplateMonad String.string :=
  '(Σ, init_nm, receive_nm) <- quote_and_preprocess inline m;;
  let TT_defs := (TT_defs ++ TT_remap_default)%list in
  let TT :=
      (TT_ctors ++ map (fun '(kn,d) => (bs_to_s (string_of_kername kn), d)) TT_defs)%list in
  p <- tmEval lazy
             (printCameLIGODefs Σ TT_defs TT_ctors extra_ignore
                                build_call_ctx
                                init_nm receive_nm
                                m) ;;
  match (p : String.string + String.string) with
  | inl s =>
    tmEval lazy
           (wrap_in_delimiters (Strings.String.concat (Common.nl ++ Common.nl)
                                              [m.(lmd_prelude); s; m.(lmd_entry_point)]))
  | inr s => tmFail (bytestring.String.of_string s)
  end.

(** A simplified erasure/printing intended mostly for testing purposes *)
Definition simple_def_print `{ChainBase} TT_defs TT_ctors seeds (prelude harness : String.string) Σ
  : String.string + String.string :=
  let TT_defs := (TT_defs ++ TT_remap_default)%list in
  let ignore := (map fst TT_defs ++ CameLIGO_ignore_default)%list in
  let TT := (TT_ctors ++ map (fun '(kn,d) => (bs_to_s (string_of_kername kn), d)) TT_defs)%list in
  match annot_extract_template_env_specalize Σ seeds ignore with
  | Ok annot_env =>
  let '(eΣ; annots) := annot_env in
      (* dependencies should be printed before the dependent definitions *)
  let ldef_list := List.rev (print_global_env TT eΣ annots) in
    (* filtering empty strings corresponding to the ignored definitions *)
    let not_empty_str := (negb ∘ (Strings.String.eqb "") ∘ snd) in

    let ldef_ty_list := ldef_list
                          |> filter (fun d => match d with TyDecl _ => true | _ => false end)
                          |> map (fun d => match d with ConstDecl d' => d' | TyDecl d' => d' end)
                          |> filter not_empty_str in
    let ldef_const_list := ldef_list
                            |> filter (fun d => match d with ConstDecl _ => true | _ => false end)
                            |> map (fun d => match d with ConstDecl d' => d' | TyDecl d' => d' end)
                            |> filter not_empty_str in
    let defs : list String.string :=
        ldef_const_list |> map snd
                        |> List.app (map snd ldef_ty_list) in
    Strings.String.concat (Common.nl ++ Common.nl) ((prelude :: defs ++ [harness]))%list |> inl
  | Err e => inr (bs_to_s e)
  end.

(** Quoting and inlining for a single definition.
    Intended mostly for testing purposes *)
Definition quote_and_preprocess_one_def {A}
           (inline : list kername)
           (def : A)
  : TemplateMonad (Ast.Env.global_env * kername) :=
  '(Σ,_) <- tmQuoteRecTransp def false ;;
  def_nm <- extract_def_name def;;
  decls <-(if is_empty inline then ret (Ast.Env.declarations Σ)
      else
        let decls := Ast.Env.declarations Σ in
        let to_inline kn := existsb (eq_kername kn) inline in
        Σcert <- tmEval lazy (inline_globals to_inline decls) ;;
        mpath <- tmCurrentModPath tt;;
        Certifying.gen_defs_and_proofs decls Σcert mpath "_cert_pass"
                                       (KernameSetProp.of_list [def_nm]);;
     ret Σcert);;
  Σret <- tmEval lazy (if WITH_UNIVERSES then
                         Ast.Env.mk_global_env (Ast.Env.universes Σ) decls (Ast.Env.retroknowledge Σ)
                       else
                         Ast.Env.mk_global_env (ContextSet.empty) decls (Ast.Env.retroknowledge Σ));;
  ret (Σret, def_nm).

(** Extraction for testing purposes.
    Simply prints the definitions and allows for appending a prelude and a
    handwritten harness code to run the extracted definition.
    The harness is just a piece of code with definitions
    of [storage], [main], etc.*)
Definition CameLIGO_extract_single `{ChainBase} {A}
           (inline : list kername)
           (TT_defs : list (kername * String.string))
           (TT_ctors : env String.string)
           (prelude : String.string)
           (harness: String.string)
           (def : A) : TemplateMonad String.string :=
  '(Σ,def_nm) <- quote_and_preprocess_one_def inline def ;;
  let seeds := KernameSetProp.of_list [def_nm] in
  tmEval lazy (unwrap_string_sum (simple_def_print TT_defs TT_ctors (KernameSet.singleton def_nm) prelude harness Σ)).

(** Similar to [CameLIGO_prepare_extraction], but for a single definition *)
Definition CameLIGO_prepare_extraction_single `{ChainBase} {A}
           (inline : list kername)
           (TT_defs : list (kername * String.string))
           (TT_ctors : env String.string)
           (prelude : String.string)
           (harness: String.string)
           (def : A) : TemplateMonad String.string :=
    '(Σ,def_nm) <- quote_and_preprocess_one_def inline def ;;
    let seeds := KernameSetProp.of_list [def_nm] in
    tmDefinition (def_nm.2 ++ "_prepared") (unwrap_string_sum (simple_def_print TT_defs TT_ctors (KernameSet.singleton def_nm) prelude harness Σ)).

End LigoExtract.
