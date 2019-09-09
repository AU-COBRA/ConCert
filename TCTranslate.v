Require Import Bool.
Require Import MetaCoq.Template.All.
(* Require Import MetaCoq.Template.Typing.*)
Require Import String List.

Require Import MyEnv Ast.

Import ListNotations.

Fixpoint type_to_term (ty : type) : term :=
  match ty with
  | tyInd i => tInd (mkInd i 0) []
  | tyArr t1 t2 => tProd nAnon (type_to_term t1) (type_to_term t2)
  end.


Fixpoint pat_to_lam (tys : list (name * type)) (body : term) : term :=
  match tys with
    [] => body
  | (n,ty) :: tys' => tLambda (nNamed n) (type_to_term ty) (pat_to_lam tys' body)
  end.

Fixpoint pat_to_elam (tys : list (name * type)) (body : expr) : expr :=
  match tys with
    [] => body
  | (n,ty) :: tys' => eLambda n ty (pat_to_elam tys' body)
  end.


(* Resolves a pattern by looking up in the global environment
   and returns an index of the consrutor in the list of contrutors for the given iductive and
   a list of pairs mapping pattern variable names to the types of the constructor arguments *)
Definition resolve_pat_arity (Σ : global_env) (ind_name : name) (p : pat) : nat * list (name * type) :=
  (* NOTE: in lookup failed we return a dummy value [(0,("",[]))]
     to make the function total *)
  let o_ci := resolve_constr Σ ind_name p.(pName) in
  let (i, nm_tys) := from_option o_ci (0,[]) in
  (i, combine p.(pVars) nm_tys).

Definition trans_branch (bs : list (pat * term))
           (c : name * list type) :=
  let dummy := (0, tVar "error") in
  let (nm, tys) := c in
  let o_pt_e := find (fun x =>(fst x).(pName) =? nm) bs in
  match o_pt_e with
    | Some pt_e => if (Nat.eqb (#|(fst pt_e).(pVars)|) (#|tys|)) then
                    let vars_tys := combine (fst pt_e).(pVars) tys in
                    (length (fst pt_e).(pVars), pat_to_lam vars_tys (snd pt_e))
                  else dummy
    | None => dummy
  end.

Definition fun_prod {A B C D} (f : A -> C) (g : B -> D) : A * B -> C * D :=
  fun x => (f (fst x), g (snd x)).

Definition expr_to_term (Σ : global_env) : expr -> Ast.term :=
  fix expr_to_term e :=
  match e with
  | eRel i => tRel i
  | eVar nm => tVar nm
  | eLambda nm ty b => tLambda (nNamed nm) (type_to_term ty) (expr_to_term b)
  | eLetIn nm e1 ty e2 => tLetIn (nNamed nm) (expr_to_term e1) (type_to_term ty) (expr_to_term e2)
  | eApp e1 e2 => mkApps (expr_to_term e1) [expr_to_term e2]
  | eConstr t i => match (resolve_constr Σ t i) with
                  | Some c => tConstruct (mkInd t 0) (fst c) []
                  (* FIXME: a hack to make the function total *)
                  | None => tConstruct (mkInd (t ++ ": no declaration found.") 0) 0 []
                     end
  | eConst nm => tConst nm []
  | eCase nm_i ty e bs =>
    let (nm,i) := nm_i in
    let typeInfo := tLambda nAnon (tInd (mkInd nm 0) []) (type_to_term ty) in
    let cs := from_option (resolve_inductive Σ nm) [] in
    let tbs := map (fun_prod id expr_to_term) bs in
    let branches := map (trans_branch tbs) cs in
    (* TODO: no translation for polymorphic types, the number of parameters is zero *)
    tCase (mkInd nm 0, 0) typeInfo (expr_to_term e) branches
  | eFix nm nv ty1 ty2 b =>
    let tty1 := type_to_term ty1 in
    let tty2 := type_to_term ty2 in
    let ty := tProd nAnon tty1 tty2 in
    let body := tLambda (nNamed nv) tty1 (expr_to_term b) in
    tFix [(mkdef _ (nNamed nm) ty body 0)] 0
  end.

Section Examples.
  Import BaseTypes.
  Import StdLib.


  Definition x := "x".
  Definition y := "y".
  Definition z := "z".

  Check [| ^0 |].

  Check [| \x : Nat -> y |].

  Definition id_f_syn :=  [| (\x : Nat -> ^0) 1 |].

  Make Definition id_f_one := (expr_to_term Σ id_f_syn).
  Example id_f_eq : id_f_one = 1. Proof. reflexivity. Qed.

  (* The same as [id_f_syn], but with named vars *)
  Definition id_f_with_vars := [| (\x : Nat -> x) 1 |].

  Make Definition id_f_one' := (expr_to_term Σ (indexify [] id_f_with_vars)).
  Example id_f_eq' : id_f_one' = 1. Proof. reflexivity. Qed.

  Definition simple_let_syn :=
    [|
     \x : Nat ->
       let y : Nat := 1 in ^0
     |].

  Make Definition simple_let := (expr_to_term Σ simple_let_syn).
  Example simple_let_eq : simple_let 1 = 1. Proof. reflexivity. Qed.

  Definition simple_let_with_vars_syn :=
    [|
     \x : Nat ->
       let y : Nat := 1 in y
     |].

  Make Definition simple_let' := (expr_to_term Σ (indexify [] simple_let_with_vars_syn)).
  Example simple_let_eq' : simple_let' 0 = 1. Proof. reflexivity. Qed.


  Definition negb_syn :=
    [|
     \x : Bool ->
            case x : Bool return Bool of
            | true -> false
            | false -> true
    |].

  Make Definition negb' := (expr_to_term Σ (indexify [] negb_syn)).

  Example negb'_correct : forall b, negb' b = negb b.
  Proof.
    destruct b;easy.
  Qed.

  Definition myplus_syn :=
    [| \x : Nat -> \y : Nat -> x + y |].

  Make Definition myplus := (expr_to_term Σ (indexify [] myplus_syn)).

End Examples.


Module Psubst.
  Definition psubst {A} := nat -> A.

  Definition id_subst : psubst := fun i => eRel i.
  Definition subst_cons {A} (e : A) (σ : psubst) : psubst :=
    fun i => if Nat.eqb i 0 then e else σ (i-1).

  Notation ids := id_subst.
  Notation "↑" := plus.
  Notation "e ⋅ σ" := (subst_cons e σ) (at level 50).

  Import Basics.
  Open Scope program_scope.

  Fixpoint erename (r : nat -> nat) (e : expr) : expr :=
    match e with
    | eRel i => eRel (r i)
    | eVar nm  => eVar nm
    | eLambda nm ty b => eLambda nm ty (erename (↑1 ∘ r) b)
    | eLetIn nm e1 ty e2 => eLetIn nm (erename r e1) ty (erename r e2)
    | eApp e1 e2 => eApp (erename r e1) (erename r e2)
    | eConstr t i as e' => e'
    | eConst nm => eConst nm
    | eCase nm_i ty e bs =>
      eCase nm_i ty (erename r e)
            (map (fun x =>
                    let k := length (fst x).(pVars) in
                    (fst x, erename (↑k ∘ r) (snd x))) bs)
    | eFix nm v ty1 ty2 b => eFix nm v ty1 ty2 (erename (↑2 ∘ r) b)
    end.

  Definition up (σ : psubst) := ids 0 ⋅ (erename (↑1) ∘ σ).

  Fixpoint up_k (k : nat) (σ : psubst) :=
    match k with
    | O => σ
    | S k' => up (up_k k' σ)
    end.

  Import FunctionalExtensionality.
  Import Lia.

  Lemma up_k_eq_id k σ :
    forall i,
    i < k ->
    up_k k σ i = ids i.
  Proof.
    induction k;intros i H.
    + inversion H.
    + simpl.
      destruct i. reflexivity.
      unfold up,subst_cons,compose. simpl.
      replace (i-0) with i by lia.
      rewrite IHk by lia. reflexivity.
  Qed.

  Reserved Notation "e .[ σ ]" (at level 0).

  Fixpoint apply_subst (σ : psubst) (e : expr) : expr :=
    match e with
    | eRel i => σ i
    | eVar nm  => eVar nm
    | eLambda nm ty b => eLambda nm ty (b .[up σ])
    | eLetIn nm e1 ty e2 => eLetIn nm (e1 .[σ]) ty (e2 .[up σ])
    | eApp e1 e2 => eApp (e1 .[σ]) (e2 .[σ])
    | eConstr t i as e' => e'
    | eConst nm => eConst nm
    | eCase nm_i ty e bs =>
      eCase nm_i ty (e .[σ])
            (map (fun x => (fst x, (snd x) .[up_k (length (fst x).(pVars)) σ])) bs)
    | eFix nm v ty1 ty2 b => eFix nm v ty1 ty2 (b .[up_k 2 σ])
  end
  where "e .[ σ ]" := (apply_subst σ e).

  Fixpoint lsubst (l : list expr) : psubst :=
    match l with
    | [] => ids
    | e :: l' => e ⋅ (lsubst l')
    end.

End Psubst.