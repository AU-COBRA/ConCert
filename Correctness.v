(* Proof of correctness of the translation from core language expression to the Template Coq terms *)
Require Import Ast EvalE Facts CustomTactics String.
Require Template.WcbvEval.
Require Import Template.All.

Require Import List.

Import ListNotations.

Notation "Σ ;;; Γ |- t1 ⇓ t2 " := (WcbvEval.eval Σ Γ t1 t2) (at level 50).
Notation "T⟦ e ⟧ Σ " := (expr_to_term Σ e) (at level 40).

Import InterpreterEnvList.

Theorem expr_to_term_sound n ns ρ Σ1 Σ2 (Γ := []) (e : expr) (t : term) (v : val) :
  Σ2 ;;; Γ |- T⟦indexify ns e⟧Σ1 ⇓ t ->
  expr_eval n Σ1 ρ e = Ok v ->
  t = T⟦from_val v⟧Σ1.
Proof.
  induction e using expr_ind_case.
  + (* eRel - since we expect only named variables, this case is trivial*)
    intros HT He. simpl in *. destruct n; tryfalse.
  + (* eVar *)
    intros HT He. destruct n; tryfalse. simpl in *.
    (* we need to relate [ρ] and [ns] *)
    admit.
  + (* eLambda *)
    intros HT He. destruct n; tryfalse. simpl in HT. simpl in He.
    inversion He. simpl. inversion HT. subst.
Admitted.