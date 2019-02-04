(* Proof of correctness of the translation from core language expression to the Template Coq terms *)
Require Import Ast EvalE Facts CustomTactics String.
Require Template.WcbvEval.
Require Import Template.All.

Require Import List.

Import ListNotations.

Notation "Σ ;;; Γ |- t1 ⇓ t2 " := (WcbvEval.eval Σ Γ t1 t2) (at level 50).
Notation "T⟦ e ⟧ Σ " := (expr_to_term Σ e) (at level 40).

Import InterpreterEnvList.

Theorem expr_to_term_sound n ρ Σ1 Σ2 (Γ:=[]) (e : expr) (t : term) (v : val) :
  Σ2 ;;; Γ |- T⟦e⟧Σ1 ⇓ t ->
  expr_eval_i n Σ1 ρ e = Ok v ->
  t = T⟦from_val_i v⟧Σ1.
Proof.
  revert dependent v.
  revert dependent t.
  revert dependent ρ.
  revert dependent n.
  induction e using expr_ind_case;intros n1 ρ t1 v.
  + (* eRel*)
    (*This case is trivial because we assume that we deal with closed terms by putting Γ = [] *)
    intros HT He. simpl in *. destruct n1; tryfalse. autounfold with facts in *.
    simpl in *.
    destruct (lookup_i ρ n) eqn:Hlookup;tryfalse. simpl in He;inversion He;subst.
    inversion HT;subst;simpl in *. inversion isdecl. inversion isdecl.
  + (* eVar *)
    (* This case is trivial because we only consider terms with de Bruijn indices *)
    intros HT He. destruct n1; tryfalse.
  + (* eLambda *)
    intros HT He. destruct n1; tryfalse.
    autounfold with facts in *. simpl in HT. simpl in He.
    inversion He. simpl. inversion HT. subst.
    destruct ρ.
    * simpl. repeat f_equal. apply subst_env_i_empty.
    * simpl.
      destruct (n0 =? n).
      ** f_equal.

Admitted.