From Coq Require Import PeanoNat ZArith.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require ErasureFunction.
From MetaCoq.Template Require Import Kernames config.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC.

From MetaCoq.Template Require Pretty.

From ConCert.Execution Require Import Blockchain Serializable Common.

From ConCert.Embedding Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.

From ConCert.Extraction Require Import LPretty
     Common ExAst Erasure Optimize Extraction CertifyingInlining CertifyingBeta Certifying SpecializeChainBase.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
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

(* We override masks for *some* constants that have only logical parameters, like
   [@AddressMap.empty]. Our optimisation conservatively keeps one parameter
   if all the parameters are logical. This is necessary because such definitions
   might use something like [false_rect] and removing all the arguments will force evaluating their bodies, which can lead to an exception or looping depending
   on how the elimination from the empty types is implemented.
   However, for [AddressMap.empty] is completely safe to remove all arguments, since it's an abbreviation for a constructor.*)
Definition overridden_masks (kn : kername) : option bitmask :=
  if eq_kername kn <%% @AddressMap.empty %%> then Some [true]
  else None.

(* Machinery for specializing chain base *)
Definition extract_template_env_specialize
           (params : extract_template_env_params)
           (Σ : global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := SafeTemplateChecker.fix_global_env_universes Σ in
  let Σ := TemplateToPCUIC.trans_global_decls Σ in
  Σ <- specialize_ChainBase_env Σ ;;
  wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

(* Machinery for specializing chain base *)
Definition extract_template_env_specialize
           (params : extract_template_env_params)
           (Σ : global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := SafeTemplateChecker.fix_global_env_universes Σ in
  let Σ := TemplateToPCUIC.trans_global_decls Σ in
  Σ <- specialize_ChainBase_env Σ ;;
  wfΣ <- check_wf_env_func params Σ;;
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
            [dearg_transform overridden_masks true true true true true ]
       |}
  |}.

Definition extract (to_inline :  kername -> bool)
           (seeds : KernameSet.t)
           (extract_ignore : kername -> bool)
           (Σ : global_env) : TemplateMonad ExAst.global_env
  := extract_template_env_certifying_passes ret (extract_liquidity_within_coq to_inline seeds) Σ seeds extract_ignore.

Definition extract_specialize (to_inline :  kername -> bool)
           (seeds : KernameSet.t)
           (extract_ignore : kername -> bool)
           (Σ : global_env) : TemplateMonad ExAst.global_env
  := extract_template_env_certifying_passes specialize_ChainBase_env (extract_liquidity_within_coq to_inline seeds) Σ seeds extract_ignore.


Definition printLiquidityDefs_
           (extract_env : (kername -> bool) -> KernameSet.t -> (kername -> bool) -> global_env -> TemplateMonad ExAst.global_env)
           (prefix : string) (Σ : global_env)
           (TT : MyEnv.env string)
           (inline : list kername)
           (ignore : list kername)
           (build_call_ctx : string)
           (init_prelude : string)
           (init : kername)
           (receive : kername)

  : TemplateMonad string :=
  let seeds := KernameSet.union (KernameSet.singleton init) (KernameSet.singleton receive) in
  let should_inline kn := existsb (eq_kername kn) inline in
  let ignore_extract kn := List.existsb (eq_kername kn) ignore in
  eΣ <- extract_env should_inline seeds ignore_extract Σ ;;
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
        ret res
      | None => tmFail "Error: Empty body for init"
      end
    | Some _ => tmFail "Error: init must be a constant"
    | None => tmFail "Error: No init found"
  end.

(* standard printing of definitions *without* chainbase specialization *)
Definition printLiquidityDefs := printLiquidityDefs_ extract.
(* printing *with* chainbase specialization *)
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

(* We assume the structure of the context from the [PreludeExt]:
  current_time , sender_addr, sent_amount, acc_balance *)
Definition liquidity_call_ctx :=
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
    hand-written harness code to run the extracted definition.
    The harness is just a piece of code with definitions
    of [storage], [main], etc.*)
Definition liquidity_extract_single
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (extract_deps : bool)
           (prelude : string)
           (harness : string)
           (p : program) : string + string :=
  match p.2 with
  | tConst kn _ =>
    let seeds := KernameSet.singleton kn in
    let TT :=
        (TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
    let ignore := if extract_deps then fun kn => existsb (eq_kername kn) (map fst TT_defs) else fun kn' => negb (eq_kername kn' kn)  in
    match extract_template_env liquidity_extract_args p.1 seeds ignore with
    | Ok eΣ =>
      (* filtering out empty type declarations *)
      (* TODO: possibly, move to extraction (requires modifications of the correctness proof) *)
      let eΣ := filter (fun '(_,_,d) => negb (is_empty_type_decl d)) eΣ in
      (* dependencies should be printed before the dependent definitions *)
      let ldef_list := List.rev (print_global_env "" TT eΣ) in
      (* filtering empty strings corresponding to the ignored definitions *)
      let ldef_list := filter (negb ∘ (String.eqb "") ∘ snd) ldef_list in
      let defs := map snd ldef_list in
      inl (concat (nl ^ nl) (prelude :: defs ++ [harness]))
    | Err e => inr e
    end
  | _ => inr "Constant expected"
  end.

Definition wrap_in_delimiters s :=
  String.concat nl ["";"(*START*)"; s; "(*END*)"].

Definition liquidity_extraction_ {msg ctx params storage operation : Type}
           (printLiquidityDefs_ : string ->
                                 global_env ->
                                 env string ->
                                 list kername ->
                                 list kername ->
                                 string -> string -> kername -> kername -> TemplateMonad string)
           (prefix : string)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (inline : list kername)
           (m : LiquidityMod msg ctx params storage operation) : TemplateMonad string :=
  '(Σ,_) <- tmQuoteRecTransp m false ;;
  init_nm <- extract_def_name m.(lmd_init);;
  receive_nm <- extract_def_name m.(lmd_receive);;
  let TT_defs := (TT_defs ++ TT_remap_default)%list in
  let ignore := (map fst TT_defs ++ liquidity_ignore_default)%list in
  let TT :=
      (TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
  s <- printLiquidityDefs_ prefix Σ TT inline ignore
                         liquidity_call_ctx
                         m.(lmd_init_prelude)
                             init_nm receive_nm ;;
    tmEval lazy
           (wrap_in_delimiters (concat (nl ++ nl) [m.(lmd_prelude); s; m.(lmd_entry_point)])).

(* Liquidity extraction *without* chainbase specialization *)
Definition liquidity_extraction {msg ctx params storage operation : Type} := @liquidity_extraction_ msg ctx params storage operation printLiquidityDefs.
(* Liquidity extraction *with* chainbase specialization *)
Definition liquidity_extraction_specialize {msg ctx params storage operation : Type} := @liquidity_extraction_ msg ctx params storage operation printLiquidityDefs_specialize.
