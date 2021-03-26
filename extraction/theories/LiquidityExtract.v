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
     Common ExAst Erasure Optimize Extraction SpecializeChainBase Inlining.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
(* Import AcornBlockchain. *)
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

(* Extract an environment with some minimal checks. This assumes the environment
   is well-formed (to make it computable from within Coq) but furthermore checks that the
   erased context is closed, expanded and that the masks are valid before dearging.
   Takes [should_inline] - a map that returns true for the constants that should be inlined.
   Suitable for extraction of programs **from within Coq**. *)
   Definition extract_liquidity_within_coq (should_inline : kername -> bool) :=
    {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
       pcuic_args :=
         {| optimize_prop_discr := true;
            transforms := [dearg_transform true true true true true;
                           Inlining.transform should_inline ] |} |}.
  
  Definition extract (should_inline : kername -> bool)
    := extract_template_env (extract_liquidity_within_coq should_inline).

(* Machinery for specializing chain base *)
Definition extract_template_env_specialize
           (should_inline : kername -> bool)
           (params : extract_template_env_params)
           (Σ : global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := SafeTemplateChecker.fix_global_env_universes Σ in
  let Σ := TemplateToPCUIC.trans_global_decls Σ in
  Σ <- specialize_ChainBase_env Σ ;;
  wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

Definition extract_template_env_within_coq_specialize inline := extract_template_env_specialize inline (extract_liquidity_within_coq inline).

Definition printLiquidityDefs_ 
           (extract_template_env : (kername -> bool) -> global_env -> KernameSet.t -> (kername -> bool) -> result ExAst.global_env string)
           (prefix : string) (Σ : global_env)
           (TT : MyEnv.env string)
           (ignore : list kername)
           (inline : list kername)
           (build_call_ctx : string)
           (init_prelude : string)
           (init : kername)
           (receive : kername)
  : string + string :=
  let seeds := KernameSet.union (KernameSet.singleton init) (KernameSet.singleton receive) in
  match extract_template_env (fun k => List.existsb (eq_kername k) inline) Σ seeds (fun k => List.existsb (eq_kername k) ignore) with
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

(* standard printing of definitions *without* chainbase specialization *)
Definition printLiquidityDefs := printLiquidityDefs_ extract.
(* printing *with* chainbase specialization *)
Definition printLiquidityDefs_specialize := printLiquidityDefs_ extract_template_env_within_coq_specialize.


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
  ; remap <%% N.add %%> "addNat"
  ; remap <%% N.sub %%> "subNat"
  ; remap <%% N.leb %%> "leNat"
  ; remap <%% N.ltb %%> "ltNat"
  ; remap <%% N.eqb %%> "eqNat"
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

Definition liquidity_extraction_ {msg ctx params storage operation : Type}
           (printLiquidityDefs_ : string ->
                                 global_env ->
                                 env string ->
                                 list kername ->
                                 list kername ->
                                 string -> string -> kername -> kername -> string + string)
           (prefix : string)
           (TT_defs : list (kername *  string))
           (TT_ctors : MyEnv.env string)
           (inline : list kername)
           (m : LiquidityMod msg ctx params storage operation) : TemplateMonad string :=
  '(Σ,_) <- tmQuoteRecTransp m false ;;
  init_nm <- extract_def_name m.(lmd_init);;
  receive_nm <- extract_def_name m.(lmd_receive);;
  let ignore := (map fst TT_defs ++ liquidity_ignore_default)%list in
  let TT :=
      (TT_ctors ++ map (fun '(kn,d) => (string_of_kername kn, d)) TT_defs)%list in
  p <- tmEval lazy
             (printLiquidityDefs_ prefix Σ TT ignore inline
                                 liquidity_call_ctx
                                 m.(lmd_init_prelude)
                                 init_nm receive_nm) ;;
  match p with
  | inl s =>
    tmEval lazy
           (wrap_in_delimiters (concat (nl ++ nl) [m.(lmd_prelude); s; m.(lmd_entry_point)]))
  | inr s => tmFail s
  end.

(* Liquidity extraction *without* chainbase specialization *)
Definition liquidity_extraction {msg ctx params storage operation : Type} := @liquidity_extraction_ msg ctx params storage operation printLiquidityDefs.
(* Liquidity extraction *with* chainbase specialization *)
Definition liquidity_extraction_specialize {msg ctx params storage operation : Type} := @liquidity_extraction_ msg ctx params storage operation printLiquidityDefs_specialize.
