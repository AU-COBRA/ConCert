From Coq Require Import PeanoNat ZArith.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import SafeTemplateErasure.
From MetaCoq.Erasure Require ErasureFunction.
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.Template Require Import config.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC.

From MetaCoq.Template Require Pretty.

From ConCert Require Import MyEnv Common.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.

From ConCert.Extraction Require Import LPretty ExAst Erasure Optimize.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import AcornBlockchain.
Import MonadNotation.

Definition print_EnvCheck {A}
           (f : E.global_context -> A -> string)
           (checked_t : EnvCheck (E.global_context * A))
  : string + string :=
  match checked_t return string + string with
  | CorrectDecl (Σ', t) =>
    inl (f Σ' t)
  | EnvError Σ' (AlreadyDeclared id) =>
    inr ("Already declared: " ++ id)
  | EnvError Σ' (IllFormedDecl id e) =>
    inr ("Type error: " ++ PCUICSafeChecker.string_of_type_error Σ' e ++ ", while checking " ++ id)
  end.

Import ResultMonad.

Definition print_result {A}
           (f : ExAst.global_env -> A -> string)
           (res : result (ExAst.global_env * A) string)
  : string + string :=
  match res return string + string with
  | Ok (Σ,a) =>
    inl (f Σ a)
  | Err s => inr s
  end.

Definition is_fully_applied_ctor (Σ : P.global_env)
           (ind : inductive)
           (ctor : nat) (n_app : nat) :=
  match PCUICChecker.lookup_constructor_decl Σ ind.(inductive_mind) ind.(inductive_ind) ctor with
  | PCUICChecker.Checked (_,_,ty) =>
    let (dom, _) :=
        PCUICAstUtils.decompose_prod ty in
    Nat.eqb n_app (List.length dom.2)
  | _ => false
  end.

Definition find_indices {A : Type}
           (f : A -> bool) : list A -> list nat :=
  let worker := fix go (i : nat) l :=
              match l with
              | [] => []
              | x :: tl =>
                if f x then i :: go (1+i)%nat tl
                else go (1+i)%nat tl
              end in
  worker 0.

Fixpoint last_option {A} (l : list A) : option A :=
  match l with
  | [] => None
  | [a] => Some a
  | a :: (_ :: _) as l0 => last_option l0
  end.

Definition is_TBox (t : box_type) : bool :=
  match t with
  | TBox => true
  | _ => false
  end.

Definition last_box_index l := last_option (find_indices is_TBox l).

Fixpoint lookup_env (Σ : P.global_env) (id : kername) : option P.global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if eq_kername id hd.1 then Some hd.2
    else lookup_env tl id
  end.

Definition lookup_ind_decl (Σ : P.global_env) ind i :=
  match lookup_env Σ ind with
  | Some (P.InductiveDecl {| P.ind_bodies := l; P.ind_universes := uctx |}) =>
    match nth_error l i with
    | Some body => Some body
    | None => None
    end
  | _ => None
  end.

Definition lookup_const (Σ : P.global_env) const :=
  match lookup_env Σ const with
  | Some (P.ConstantDecl b) => Some b
  | _ => None
  end.

Definition erase_type_to_typing_result {A} (e : erase_type_error) : typing_result A:=
  match e with
  | NotPrenex => TypeError (Msg "Not Prenex")
  | TypingError te => TypeError te
  | GeneralError msg => TypeError (Msg msg)
  end.

Program Definition is_logargs_applied_const (Σ : P.global_env_ext)
           (HΣ : ∥ PCUICTyping.wf_ext Σ ∥)
           (const : kername) (n_app : nat) : typing_result bool :=
  match lookup_const Σ const with
  | Some b =>
    match erase_type Σ HΣ [] Vector.nil b.(P.cst_type) _ [] with
      | ResultMonad.Ok ety => let (dom, _) := decompose_arr ety.2 in
                 match last_box_index dom with
                 | Some i => ret (Nat.leb (i+1) n_app)
                 | None => ret true
                 end
      | ResultMonad.Err e => erase_type_to_typing_result e
    end
  | _ => TypeError (Msg ("Constant not found: " ++ string_of_kername const))
  end.
Next Obligation.
  intros. sq. destruct Σ; destruct HΣ as [p1 p2];simpl in *.
  subst filtered_var.
  right.
  todo "everything coming from well-formed environment is well typed + validity".
Qed.
Next Obligation. easy. Qed.

Program Definition test_applied_to_logargs  (p : Ast.program) (const : kername) (n_app : nat)
  : EnvCheck bool :=
  let p := fix_program_universes p in
  let Σ := (trans_global (Ast.empty_ext p.1)).1 in
  G <- check_wf_env_only_univs Σ ;;
  t <- wrap_error (P.empty_ext Σ) "during cheking applied constant" (is_logargs_applied_const (P.empty_ext Σ) _ const n_app) ;;
  ret (Monad:=envcheck_monad) t.
Next Obligation.
  intros.
  unfold PCUICTyping.wf_ext, empty_ext.
  unfold PCUICTyping.on_global_env_ext.
  destruct G as (?&H&H0). sq.
  split; auto. simpl.
  sq.
  repeat split;eauto;try easy. simpl.
  now apply wf_consistent.
Qed.

MetaCoq Quote Recursively Definition ex_combine := combine.

Compute (test_applied_to_logargs ex_combine (to_kername_dummy <% @combine %>) 2).

Definition test_fully_applied_constructor (p : Ast.program) (ind_nm : kername) (ind_i : nat) (ctor : nat) (n_app : nat) :=
  let p := fix_program_universes p in
  let Σ := (trans_global (Ast.empty_ext p.1)).1 in
  (is_fully_applied_ctor Σ (mkInd ind_nm ind_i) ctor n_app).

MetaCoq Quote Recursively Definition q_prod
  := (fun (x y : nat) => (x,y)).

Compute ((test_fully_applied_constructor q_prod (to_kername_dummy <% prod %>) 0 0 4)).


Definition forallb_defs {A : Set} (f : A -> bool) (ds : list (E.def A)) :=
  (* this way of defining is fixpoint-firendly, i.e. is we [map] first and then apply [forallb] it fails to work with the definition below *)
  forallb (fun x => f x.(E.dbody)) ds.

Open Scope bool.

Definition check_ctors_applied (Σ : P.global_env) :=
  fix go (apps : list E.term) (t : E.term) :=
    match t with
    | E.tRel i => true
    | E.tEvar ev args => forallb (go []) args
    | E.tLambda na M => go [] M
    | E.tApp u v => (go (v :: apps) u) && (go [] v)
    | E.tLetIn na b b' => (go [] b) && (go [] b')
    | E.tCase ind c brs =>
      let brs' := forallb (fun x => go [] (snd x)) brs in
      (go [] c) && brs'
    | E.tProj p c => go [] c
    | E.tFix mfix idx =>
      forallb_defs (go []) mfix
    | E.tCoFix mfix idx =>
      forallb_defs (go []) mfix
    | E.tBox => true
    | E.tVar _ => true
    | E.tConst _ => true
    | E.tConstruct ind i =>
      is_fully_applied_ctor Σ ind i (List.length apps)
    end.

Definition check_consts_applied
  (Σ : P.global_env_ext) (HΣ : ∥ PCUICTyping.wf_ext Σ ∥) :=
  fix go (apps : list E.term) (t : E.term) : typing_result bool:=
    match t with
    | E.tRel i => ret true
    | E.tEvar ev args =>
      res <- monad_map (go []) args ;;
      ret (forallb id res)
    | E.tLambda na M => go [] M
    | E.tApp u v =>
      b1 <- go (v :: apps) u ;;
      b2 <- go [] v ;;
      ret (b1 && b2)
    | E.tLetIn na b b' =>
      b1 <- go [] b;;
      b2 <- go [] b';;
      ret (b1 && b2)
    | E.tCase ind c brs =>
      b1 <- go [] c ;;
      res <- monad_map (fun x => go [] (snd x)) brs ;;
      ret (b1 && forallb id res)
    | E.tProj p c => go [] c
    | E.tFix mfix idx =>
      res <- monad_map (fun x => go [] (E.dbody x)) mfix ;;
      ret (forallb id res)
    | E.tCoFix mfix idx =>
      res <- monad_map (fun x => go [] (E.dbody x)) mfix ;;
      ret (forallb id res)
    | E.tBox => ret true
    | E.tVar _ => ret true
    | E.tConst nm => is_logargs_applied_const Σ HΣ nm (List.length apps)
    | E.tConstruct ind i => ret true
    end.

Program Definition check_applied
        (Σ : P.global_env)
        (wf : ∥PCUICTyping.wf Σ∥)
        (et : E.term) : EnvCheck bool :=
  is_const_applied <- wrap_error (P.empty_ext Σ) "during checking applied constant"
                                 (check_consts_applied (P.empty_ext Σ) _ [] et) ;;
  let is_constr_applied := check_ctors_applied Σ [] et in
  ret (Monad:=envcheck_monad) (andb is_const_applied is_constr_applied).
Next Obligation.
  intros.
  destruct wf as [wf].
  constructor.
  split; [assumption| ].
  simpl.
  repeat split;eauto;try easy.
  now apply wf_consistent.
Qed.

Definition erase_and_check_applied (p : Ast.program) : EnvCheck bool :=
  let p := fix_program_universes p in
  let Σ := (trans_global (Ast.empty_ext p.1)).1 in
  G <- check_wf_env_only_univs Σ ;;
  et <- erase_template_program p ;;
  check_applied Σ (proj2 (projT2 G)) et.2.

Definition print_sum (s : string + string) :=
  match s with
  | inl s' => s'
  | inr s' => s'
  end.


Definition liftM {M : Type -> Type} `{Monad M} {A B : Type}
           (f : A -> B) : M A -> M B :=
  fun ma => ma >>= ret ∘ f.

Definition eta_expand_cst
           (ctors : list ((inductive × nat) × nat))
           (constants : list (kername × nat))
           (cst : ExAst.constant_body) : ExAst.constant_body :=
    {| ExAst.cst_type := ExAst.cst_type cst;
       ExAst.cst_body := option_map (eta_expand ctors constants) (ExAst.cst_body cst) |}.

Definition debox_cst (Σ : ExAst.global_env) (kn : kername) (cst : ExAst.constant_body) :=
  let dearg_set := get_dearg_set_for_unused_args Σ in
  let consts_eta_count := map (on_snd S_last_1) (const_masks dearg_set) in
  let get_ctors_eta_count kn mib_masks :=
      map (fun '(i, c, mask) =>
             ({| inductive_mind := kn; inductive_ind := i |}, c,
              List.length (param_mask mib_masks) + S_last_1 mask))%nat
          (ctor_masks mib_masks) in
  let ctors_eta_count :=
      List.concat
        (map (fun '(kn, mib_masks) => get_ctors_eta_count kn mib_masks)
             (ind_masks dearg_set)) in
  let cst_eta := eta_expand_cst ctors_eta_count consts_eta_count cst in
  let cst_deboxed := dearg_cst (ind_masks dearg_set)
                               (const_masks dearg_set) kn cst_eta in
  {| ExAst.cst_type := on_snd debox_box_type cst_deboxed.(ExAst.cst_type );
     ExAst.cst_body := cst_deboxed.(ExAst.cst_body) |}.

Import ResultMonad.

(** Deboxes erases a constant and deboxes both constant's type and body. Also removes redundant top-level lambdas. *)
Program Definition erase_debox_all_applied
           (Σ : T.global_env)
           (kn : kername)
           (cst : T.constant_body)
  : result (ExAst.global_env * ExAst.constant_body) string :=
  let Σ := fix_global_env_universes Σ in
  let Σ := trans_global (empty_ext Σ) in
  G <- result_of_EnvCheck (check_wf_env_only_univs Σ.1) ;;
  Σ' <- map_error
         string_of_erase_global_decl_error
         (erase_global_decls [] Σ.1 _) ;;
  e <- map_error
    (string_of_erase_constant_decl_error Σ)
    (erase_constant_decl Σ _ (trans_constant_body cst) _);;
  ret (Σ', debox_cst Σ' kn e).
Next Obligation.
  intros. destruct G as (?&?&wfΣ).
  now sq; inversion wfΣ.
Qed.
Next Obligation.
  intros. destruct G as (?&?&wfΣ).
  sq. subst Σ. split.
  * now sq; inversion wfΣ.
  * simpl.
    repeat split;eauto;try easy.
    now apply wf_consistent.
Qed.
Next Obligation.
  intros.
  todo "assuming well-typedness".
Qed.

(* Definition erase_debox_all_applied (TT : MyEnv.env string) *)
(*            (Σ : T.global_env) (seeds : list string) : *)
(*   ResultMonad.result ExAst.global_env string := *)
(*   let Σ := fix_global_env_universes Σ in *)
(*   specialize_erase_debox_template_env Σ [] []. *)

(* Definition print_decl (TT : env string) (tys : list Ast.term) *)
(*            (Σ : E.global_context) (decl_body : list E.aname * E.term) : string := *)
(*   let (args,body) := decl_body in *)
(*   (* FIXME: this will produce wrong type annotations if the logical argument *)
(*      appears between the normal arguments! We need to switch to erased types and filter  out the boxes in types *) *)
(*   let targs := combine args tys in *)
(*   let printed_targs := *)
(*       map (fun '(x,ty) => parens false (string_of_name x.(E.binder_name) ++ " : " ++ print_liq_type TT ty)) targs in *)
(*   let decl := decl_name ++ " " ++ concat " " printed_targs in *)
(*   let ctx := map (fun x => E.Build_context_decl x.(E.binder_name) None) (rev args) in *)
  (* "let " ++ decl ++ " = " ++  LPretty.print_term Σ [] TT ctx true false body. *)


Definition erase_print_deboxed_all_applied (prefix : string)
           (TT : MyEnv.env string) (* tranlation table *)
           (Σ : T.global_env)
           (kn : kername)
           (cst : T.constant_body) : string :=
  let deboxed := erase_debox_all_applied Σ kn cst  in
  let res := print_result (fun ge c => print_cst prefix TT ge kn c) deboxed in
  print_sum res.


Program Definition erase_check_debox_all (prefix : string)
           (TT : MyEnv.env string) (* tranlation table *)
           (Σ : T.global_env)
           (kn : kername)
           (cst : T.constant_body) : result (ExAst.global_env * ExAst.constant_body) string :=
  let Σ := fix_global_env_universes Σ in
  let Σ' := trans_global (empty_ext Σ) in
  G <- result_of_EnvCheck (check_wf_env_only_univs Σ'.1) ;;
  is_ok <- match cst.(cst_body) with
          | Some b => result_of_EnvCheck (erase_and_check_applied (Σ,b))
          | None => ret true (* NOTE: for constants without a body we just return true*)
          end ;;
  if is_ok : bool then
    erase_debox_all_applied Σ kn cst
  else
    Err "Not all constructors or constants are appropriately applied".

Program Definition erase_check_debox_all_print (prefix : string)
        (TT : MyEnv.env string) (* tranlation table *)
        (Σ : T.global_env)
        (kn : kername)
        (cst : T.constant_body)
  : string :=
  let deboxed := erase_check_debox_all prefix TT Σ kn cst in
  let res := print_result (fun ge c => print_cst prefix TT ge kn c) deboxed in
  print_sum res.

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).

(** Returns a pair of a fully qualified name and a short name to use in the extracted code.
 Used in the case if we need to refer to a previously extracted constant in the same file *)
Definition local (prefix : string) (t : Ast.term) : string * string :=
  let nm := to_string_name t in
  (nm, prefix ++ unqual_name nm).

(** Returns a pair of a fully qualified name (if [t] is a constant) and a new name.
 Used in a similar way as [Extract Inlined Constant] of the standard extraction *)
Definition remap (t : Ast.term) (new_name : string) :  string * string :=
  let nm := to_string_name t in
  (nm, new_name).

Record LiqDef :=
  mkLiqDef {ld_name : kername; ld_cst : T.constant_body}.

Definition liq_def nm ty body ud :=
  {|ld_name := nm ; ld_cst := {| T.cst_type := ty;
                                 T.cst_body := body;
                                 T.cst_universes := ud |} |}.

Definition opt_to_template {A} (o : option A) : TemplateMonad A:=
  match o with
  | Some v => ret v
  | None => tmFail "None"
  end.

Definition to_constant_decl (gd : option T.global_decl) :=
  match gd with
  | Some (ConstantDecl cst_body) => ret cst_body
  | Some (InductiveDecl cst_body) => tmFail "Error (constant expected, given inductive)"
  | None => tmFail "Error (expected constant with a body)"
  end.

Definition toDefWithEnv {A} (p : A)  :=
  t <- tmQuoteRec p  ;;
  nm <- opt_to_template (to_kername t.2) ;;
  cbody_o <- tmQuoteConstant nm false ;;
  cbody <- opt_to_template cbody_o.(cst_body) ;;
  ret (mkLiqDef nm cbody_o, t.1).

Definition toDef {A} (p : A)  :=
  t <- tmQuote p  ;;
  nm <- opt_to_template (to_kername t) ;;
  cbody_o <- tmQuoteConstant nm false ;;
  cbody <- opt_to_template cbody_o.(cst_body) ;;
  ret (mkLiqDef nm cbody_o).

(* Definition toLiquidityWithBoxes {A} (prefix : string) *)
(*            (FT : list string) (* list of fixpoint names *) *)
(*            (TT : MyEnv.env string) (* tranlation table *) *)
(*            (p : A) := *)
(*   d_e <- toDefWithEnv p ;; *)
(*   let '(liq_def, env) := d_e in *)
(*   let decl_name := unqual_name liq_def.(ld_name) in *)
(*   match liq_def.(ld_body) with *)
(*   | Some b => *)
(*     liq_prog <- tmEval lazy (erase_print prefix FT TT (env,b)) ;; *)
(*     let liq_def_string := "let " ++ decl_name ++ " = " ++ liq_prog in ret liq_def_string *)
(*   | None => *)
(*     liq_type <- tmEval lazy (print_liq_type prefix TT liq_def.(ld_type)) ;; *)
(*     let liq_def_string := "type " ++ decl_name ++ " = " ++ liq_type in ret liq_def_string *)
(*   end. *)

Definition toLiquidity {A} (prefix : string) (TT : MyEnv.env string) (p : A) :=
  d_e <- toDefWithEnv p ;;
  let '(liq_def, Σ) := d_e in
  let nm := liq_def.(ld_name) in
  let cst := liq_def.(ld_cst) in
  tmEval lazy (erase_check_debox_all_print prefix TT Σ nm cst).

Definition toLiquidityEnv {A} (prefix : string) (TT : MyEnv.env string) (Σ : T.global_env)(p : A) :=
  liq_def <- toDef p ;;
  let nm := liq_def.(ld_name) in
  let cst := liq_def.(ld_cst) in
  tmEval lazy (erase_check_debox_all_print prefix TT Σ nm cst).

Definition print_one_ind_body (prefix : string) (TT : MyEnv.env string) (oibs : list one_inductive_body) :=
  match oibs with
  | [oib] => ret (print_inductive prefix TT oib)
  | _ => tmFail "Only non-mutual inductives are supported"
  end.

Definition is_sort_simple (t : T.term) :=
  match t with
  | T.tSort _ => true
  | _ => false
  end.

Definition toDefIdent (nm : kername) : TemplateMonad LiqDef :=
  cbody_o <- tmQuoteConstant nm false ;;
  cbody <- opt_to_template cbody_o.(cst_body) ;;
  if is_sort_simple cbody_o.(cst_type) then
    ret (mkLiqDef nm {| cst_type := cbody;
                        cst_body:= None;
                        cst_universes := cbody_o.(cst_universes) |})
  else ret (mkLiqDef nm cbody_o).

Definition toLiquidityDefs (prefix : string) (TT : MyEnv.env string) (Σ : TemplateEnvironment.global_env)(ids : list kername) :=
  ds <- monad_map toDefIdent ids ;;
  let liquidify d :=
      let nm := d.(ld_name) in
      let cst := d.(ld_cst) in
      tmEval lazy (erase_check_debox_all_print prefix TT Σ nm cst) in
  ldefs <- monad_map liquidify ds ;;
  tmEval lazy (concat (nl++nl) ldefs).

Definition toLiquidityADTs (prefix : string) (TT : MyEnv.env string) (Σ : TemplateEnvironment.global_env)(ids : list kername) :=
  let liquidify ind :=
      ind_def <- tmQuoteInductive ind ;;
      print_one_ind_body prefix TT ind_def.(ind_bodies) in
  ldefs <- monad_map liquidify ids ;;
  tmEval lazy (concat (nl++nl) ldefs).

Record LiquidityModule :=
  { lm_module_name : string ;
    lm_prelude : string ;
    lm_adts : list kername ;
    lm_defs : list kername;
    lm_entry_point : string ;
    lm_init : string}.

Definition printLiquidityModule (prefix : string) (Σ : global_env) (TT : MyEnv.env string)
           (m : LiquidityModule) :=
  adts <- toLiquidityADTs prefix TT Σ m.(lm_adts) ;;
  defs <- toLiquidityDefs prefix TT Σ m.(lm_defs);;
  res <- tmEval lazy
               (m.(lm_prelude)
                 ++ nl ++ nl
                 ++ adts
                 ++ nl ++ nl
                 ++ defs
                 ++ nl ++ nl
                 ++ m.(lm_entry_point)) ;;
  tmDefinition m.(lm_module_name) res ;;
  msg <- tmEval lazy ("The module extracted successfully. The definition " ++ "[" ++ m.(lm_module_name) ++ "]" ++ " containing the Liquidity code has been added to the Coq environment. Use [Print] command to print the Liquidity code") ;;
  tmPrint msg.
