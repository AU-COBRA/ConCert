From MetaCoq.Common Require Import Kernames.
From MetaCoq.PCUIC Require Import PCUICAst.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require ResultMonad.
From ConCert.Extraction Require Import LiquidityPretty.
From ConCert.Extraction Require Import Common.
From MetaCoq.Erasure.Typed Require Import Optimize.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import CertifyingInlining.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From ConCert.Extraction Require Import SpecializeChainBase.
From ConCert.Utils Require Import Env.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith_base.
From MetaCoq.Template Require Import All.

Import ListNotations.
Import MCMonadNotation.


Definition to_constant_decl (gd : option global_decl) :=
  match gd with
  | Some (ConstantDecl cst_body) => ret cst_body
  | Some (InductiveDecl cst_body) => tmFail "Error (constant expected, given inductive)"
  | None => tmFail "Error (expected constant with a body)"
  end.

Record LiquidityMod (msg init_ctx params storage operation error : Type) :=
  { lmd_module_name : String.string ;
    lmd_prelude : String.string ;
    lmd_init : init_ctx -> params -> ConCert.Execution.ResultMonad.result storage error;
    lmd_init_prelude : String.string ;
    lmd_receive : msg -> storage -> ConCert.Execution.ResultMonad.result (list operation * storage) error;
    lmd_entry_point : String.string }.

Arguments lmd_module_name {_ _ _ _ _ _}.
Arguments lmd_prelude {_ _ _ _ _ _}.
Arguments lmd_init {_ _ _ _ _ _}.
Arguments lmd_init_prelude {_ _ _ _ _ _}.
Arguments lmd_receive {_ _ _ _ _ _}.
Arguments lmd_entry_point {_ _ _ _ _ _}.

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

Definition result_string_err A := result A string.

(* Machinery for specializing chain base *)
Definition extract_template_env_specialize
           (params : extract_template_env_params)
           (Σ : global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result_string _ :=
  let Σ := TemplateToPCUIC.trans_global_env Σ in
  Σ <- specialize_ChainBase_env (PCUICProgram.trans_env_env Σ) ;;
  wfΣ <- check_wf_env_func extract_within_coq Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

(* Extract an environment with some minimal checks. This assumes the environment
   is well-formed (to make it computable from within Coq) but furthermore checks that the
   erased context is closed, expanded and that the masks are valid before dearging.
   Takes [should_inline] - a map that returns true for the constants that should be inlined.
   Suitable for extraction of programs **from within Coq**. *)
Definition extract_liquidity_within_coq (to_inline : kername -> bool)
           (seeds : KernameSet.t) :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms :=
       [CertifyingInlining.template_inline to_inline];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms :=
            (* TODO: a 'false' second-last arg disables fully
               expanded environments - only for boardroomvoting *)
            [dearg_transform overridden_masks true true true true true ]
       |}
  |}.

Definition extract (to_inline : kername -> bool)
           (seeds : KernameSet.t)
           (extract_ignore : kername -> bool)
           (Σ : global_env) : TemplateMonad ExAst.global_env :=
  extract_template_env_certifying_passes Ok (extract_liquidity_within_coq to_inline seeds) Σ seeds extract_ignore.

Definition extract_specialize (to_inline : kername -> bool)
           (seeds : KernameSet.t)
           (extract_ignore : kername -> bool)
           (Σ : global_env) : TemplateMonad ExAst.global_env :=
  extract_template_env_certifying_passes specialize_ChainBase_env (extract_liquidity_within_coq to_inline seeds) Σ seeds extract_ignore.


Definition printLiquidityDefs_
           (extract_env : (kername -> bool) -> KernameSet.t -> (kername -> bool) -> global_env -> TemplateMonad ExAst.global_env)
           (prefix : String.string) (Σ : global_env)
           (TT : env String.string)
           (inline : list kername)
           (ignore : list kername)
           (build_call_ctx : String.string)
           (init_prelude : String.string)
           (init : kername)
           (receive : kername)
  : TemplateMonad String.string :=
  let seeds := KernameSet.union (KernameSet.singleton init) (KernameSet.singleton receive) in
  let should_inline kn := existsb (eq_kername kn) inline in
  let ignore_extract kn := List.existsb (eq_kername kn) ignore in
  eΣ <- extract_env should_inline seeds ignore_extract Σ ;;
  (* dependencies should be printed before the dependent definitions *)
  let projs := get_projections eΣ in
  let ldef_list := List.rev (print_global_env prefix TT eΣ projs) in
  (* filtering empty strings corresponding to the ignored definitions *)
  let ldef_list := filter (negb ∘ (Strings.String.eqb "") ∘ snd) ldef_list in
  match ExAst.lookup_env eΣ init with
    | Some (ExAst.ConstantDecl init_cst) =>
      match print_init prefix TT projs build_call_ctx init_prelude eΣ init_cst with
      | Some init_code =>
        (* filtering out the definition of [init] and projecting the code *)
        let defs :=
            map snd (filter (negb ∘ (eq_kername init) ∘ fst) ldef_list) in
        let res :=
            concat (Common.nl ++ Common.nl) (defs ++[ init_code ])%list in
        ret res
      | None => tmFail "Error: Empty body for init"
      end
    | Some _ => tmFail "Error: init must be a constant"
    | None => tmFail "Error: No init found"
  end.

(* standard printing of definitions *without* ChainBase specialization *)
Definition printLiquidityDefs := printLiquidityDefs_ extract.
(* printing *with* ChainBase specialization *)
Definition printLiquidityDefs_specialize := printLiquidityDefs_ extract_specialize.

Definition liquidity_ignore_default :=
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


Definition TT_remap_default : list (kername * String.string) :=
  [
    (* types *)
    (* remap <%% Z %%> "tez" *)
    remap <%% N %%> "nat"
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

  (* operations *)
  ; remap <%% List.fold_left %%> "List.fold"
  ; remap <%% Nat.add %%> "addNat"
  ; remap <%% Nat.sub %%> "subNat"
  ; remap <%% Nat.leb %%> "leNat"
  ; remap <%% Nat.eqb %%> "eqNat"
  ; remap <%% Pos.add %%> "addNat"
  ; remap <%% Pos.sub %%> "subNat"
  ; remap <%% Pos.leb %%> "leNat"
  ; remap <%% Pos.eqb %%> "eqNat"
  ; remap <%% Z.add %%> "addTez"
  ; remap <%% Z.sub %%> "subTez"
  ; remap <%% Z.leb %%> "leTez"
  ; remap <%% Z.ltb %%> "ltTez"
  ; remap <%% Z.eqb %%> "eqTez"
  ; remap <%% Z.gtb %%> "gtTez"
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
  (* ; remap <%% @address_eqdec %%> "" *)
  (* ; remap <%% @address_countable %%> "" *)
  ].

(* We assume the structure of the context from the [PreludeExt]:
  current_time, sender_addr, sent_amount, acc_balance *)
Definition liquidity_call_ctx : String.string :=
  "(Current.time (),
   (Current.sender (),
   (Current.amount (),
    Current.balance ())))".

Definition liquidity_extract_args :=
  {| check_wf_env_func := check_wf_env_func extract_within_coq;
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform
                                 (fun _ => None)
                                 true
                                 false (* cannot have partially applied ctors *)
                                 true
                                 true
                                 true] |} |}.

(** Extraction for testing purposes.
    Simply prints the definitions and allows for appending a prelude and a
    handwritten harness code to run the extracted definition.
    The harness is just a piece of code with definitions
    of [storage], [main], etc.*)
Definition liquidity_extract_single
           (TT_defs : list (kername * String.string))
           (TT_ctors : env String.string)
           (extract_deps : bool)
           (prelude : String.string)
           (harness : String.string)
           (p : program) : String.string + String.string :=
  match p.2 with
  | tConst kn _ =>
    let seeds := KernameSet.singleton kn in
    let TT :=
        (TT_ctors ++ map (fun '(kn,d) => (bs_to_s (string_of_kername kn), d)) TT_defs)%list in
    let ignore := if extract_deps then fun kn => existsb (eq_kername kn) (map fst TT_defs) else fun kn' => negb (eq_kername kn' kn) in
    match extract_template_env liquidity_extract_args p.1 seeds ignore with
    | Ok eΣ =>
      (* filtering out empty type declarations *)
      (* TODO: possibly, move to extraction (requires modifications of the correctness proof) *)
      let projs := get_projections eΣ in

      let eΣ := filter (fun '(_,_,d) => negb (is_empty_type_decl d)) eΣ in
      (* dependencies should be printed before the dependent definitions *)
      let ldef_list := List.rev (print_global_env "" TT eΣ projs) in
      (* filtering empty strings corresponding to the ignored definitions *)
      let ldef_list := filter (negb ∘ (Strings.String.eqb "") ∘ snd) ldef_list in
      let defs := map snd ldef_list in
      inl (concat (Common.nl ^ Common.nl) (prelude :: defs ++ [harness]))
    | Err e => inr (bs_to_s e)
    end
  | _ => inr (bs_to_s "Constant expected")
  end.

Definition wrap_in_delimiters (s : String.string) : String.string :=
  Strings.String.concat Common.nl [bs_to_s ""; bs_to_s "(*START*)"; s; bs_to_s"(*END*)"].

(** A flag that controls whether info about universes is preserved after quoting *)
Definition WITH_UNIVERSES := false.


Definition liquidity_extraction_ {msg ctx params storage operation error : Type}
           (printLiquidityDefs_ : String.string ->
                                 global_env ->
                                 env String.string ->
                                 list kername ->
                                 list kername ->
                                 String.string -> String.string -> kername -> kername -> TemplateMonad String.string)
           (prefix : String.string)
           (TT_defs : list (kername * String.string))
           (TT_ctors : env String.string)
           (inline : list kername)
           (m : LiquidityMod msg ctx params storage operation error) : TemplateMonad String.string :=
  '(Σ,_) <- tmQuoteRecTransp m false ;;
  init_nm <- extract_def_name m.(lmd_init);;
  receive_nm <- extract_def_name m.(lmd_receive);;
  let TT_defs := (TT_defs ++ TT_remap_default)%list in
  let ignore := (map fst TT_defs ++ liquidity_ignore_default)%list in
  let TT :=
    (TT_ctors ++ map (fun '(kn,d) => (bs_to_s (string_of_kername kn), d)) TT_defs)%list in
  Σ <- tmEval lazy (if WITH_UNIVERSES then
                     Ast.Env.mk_global_env (Ast.Env.universes Σ) (Ast.Env.declarations Σ) (Ast.Env.retroknowledge Σ)
                   else
                     Ast.Env.mk_global_env (ContextSet.empty) (Ast.Env.declarations Σ)(Ast.Env.retroknowledge Σ));;
  s <- printLiquidityDefs_ prefix Σ TT inline ignore
                         liquidity_call_ctx
                         m.(lmd_init_prelude)
                             init_nm receive_nm ;;
    tmEval lazy
           (wrap_in_delimiters (concat (Common.nl ^ Common.nl) [m.(lmd_prelude); s; m.(lmd_entry_point)])).

Definition unwrap_string_sum (s : string + string) : string :=
  match s with
  | inl v => v
  | inr v => v
  end.
Definition is_empty {A} (xs : list A) :=
  match xs with
  | [] => true
  | _ => false
  end.

Definition quote_and_preprocess {Base : ChainBase}
           {msg ctx params storage operation error : Type}
           (inline : list kername)
           (m : LiquidityMod msg ctx params storage operation error)
          : TemplateMonad (global_env * kername * kername) :=
   (* we compute with projections before quoting to avoid unnecessary dependencies to be quoted *)
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
Definition liquidity_prepare_extraction {Base : ChainBase} {msg ctx params storage operation error : Type}
           (prefix : String.string)
           (TT_defs : list (kername * String.string))
           (TT_ctors : env String.string)
           (inline : list kername)
           (m : LiquidityMod msg ctx params storage operation error) :=
  '(Σ, init_nm, receive_nm) <- quote_and_preprocess inline m;;
  let TT_defs := (TT_defs ++ TT_remap_default)%list in
  let ignore := (map fst TT_defs ++ liquidity_ignore_default)%list in
  let TT :=
      (TT_ctors ++ map (fun '(kn,d) => (bs_to_s (string_of_kername kn), d)) TT_defs)%list in
  s <- printLiquidityDefs_specialize prefix Σ TT inline ignore
                         liquidity_call_ctx
                         m.(lmd_init_prelude)
                             init_nm receive_nm ;;
  let res := wrap_in_delimiters (concat (Common.nl ++ Common.nl)
                                    [m.(lmd_prelude); s; m.(lmd_entry_point)]) in
  tmDefinition (bytestring.String.of_string (m.(lmd_module_name) ++ "_prepared")) res.

(* Liquidity extraction *without* ChainBase specialization *)
Definition liquidity_extraction {msg ctx params storage operation error : Type} :=
  @liquidity_extraction_ msg ctx params storage operation error printLiquidityDefs.

(* Liquidity extraction *with* ChainBase specialization *)
Definition liquidity_extraction_specialize {msg ctx params storage operation error : Type} :=
  @liquidity_extraction_ msg ctx params storage operation error printLiquidityDefs_specialize.
