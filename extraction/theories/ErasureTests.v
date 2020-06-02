From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import StringExtra.
From Coq Require Import Ascii.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Erasure Require Import SafeTemplateErasure.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.SafeChecker Require Import SafeTemplateChecker.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import config.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.

Local Open Scope string_scope.
Import ListNotations.
Import MonadNotation.
Set Equations Transparent.

Module E := MetaCoq.Erasure.EAst.

Module flag_of_type_tests.
Record type_flag_squashed := {
  is_logical : bool;
  is_sort : bool;
  is_arity : bool }.

Program Definition flag_of_type_program (p : Ast.program)
  : result type_flag_squashed string :=
  let Σ := List.rev (trans_global (Ast.empty_ext p.1)).1 in
  G <- match check_wf_env_only_univs Σ with
       | CorrectDecl a => ret a
       | _ => Err "Could not check_wf_env_only_univs"
       end;;
  f <- match flag_of_type (empty_ext Σ) _ [] (trans p.2) _ with
       | Checked a => ret a
       | TypeError te => Err "Could not get flag"
       end;;
  ret {| is_logical := Erasure.is_logical f;
         is_sort := if Erasure.is_sort f then true else false;
         is_arity := if Erasure.is_arity f then true else false |}.
Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. destruct H0. constructor.
  split; auto. simpl. todo "on_udecl on empty universe context".
Qed.
Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. destruct H0. todo "assuming well-typedness".
Qed.

Quote Recursively Definition ex1 := Type.
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex1) in exact x) =
                Ok {| is_logical := false; is_sort := true; is_arity := true |}.

Quote Recursively Definition ex2 := nat.
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex2) in exact x) =
                Ok {| is_logical := false; is_sort := false; is_arity := false |}.

Quote Recursively Definition ex3 := (nat -> nat).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex3) in exact x) =
                Ok {| is_logical := false; is_sort := false; is_arity := false |}.

Quote Recursively Definition ex4 := (forall A, A).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex4) in exact x) =
                Ok {| is_logical := false; is_sort := false; is_arity := false |}.

Quote Recursively Definition ex5 := (Prop).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex5) in exact x) =
                Ok {| is_logical := true; is_sort := true; is_arity := true |}.

Quote Recursively Definition ex6 := (Prop -> Type).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex6) in exact x) =
                Ok {| is_logical := false; is_sort := false; is_arity := true |}.

Quote Recursively Definition ex7 := (Type -> Prop).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex7) in exact x) =
                Ok {| is_logical := true; is_sort := false; is_arity := true |}.

Quote Recursively Definition ex8 := (False).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex8) in exact x) =
                Ok {| is_logical := true; is_sort := false; is_arity := false |}.

Quote Recursively Definition ex9 := (Fin.t 0 -> False).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex9) in exact x) =
                Ok {| is_logical := true; is_sort := false; is_arity := false |}.
End flag_of_type_tests.

Module erase_type_tests.
Program Definition erase_type_program (p : Ast.program)
  : result (EAst.global_context * (list name * box_type)) erase_type_error :=
  let Σ := List.rev (trans_global (Ast.empty_ext p.1)).1 in
  G <- match check_wf_env_only_univs Σ with
       | CorrectDecl a => ret a
       | _ => Err (GeneralError "Could not check_wf_env_only_univs")
       end;;
  Σ' <- wrap_typing_result (SafeErasureFunction.erase_global Σ _) TypingError;;
  t <- erase_type (empty_ext Σ) _ [] (Vector.nil _) (trans p.2) _ [];;
  ret (Σ', t).
Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. destruct H0. constructor.
  split; auto. simpl. todo "on_udecl on empty universe context".
Qed.
Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. destruct H0. todo "assuming well-typedness".
Qed.

Definition is_arr (t : box_type) : bool :=
  match t with
  | TArr _ _ => true
  | _ => false
  end.

Definition kername_unqual (name : kername) : string :=
  match last_index_of "." name with
  | Some n => substring_from (S n) name
  | None => ""
  end.

Definition parenthesize_arg (a : box_type) : bool :=
  match a with
  | TBox
  | TAny
  | TVar _
  | TInd _
  | TConst _ => true
  | _ => false
  end.

Fixpoint print_box_type (Σ : E.global_context) (bt : box_type) :=
  match bt with
  | TBox => "□"
  | TAny => "𝕋"
  | TArr dom codom => parens (negb (is_arr dom)) (print_box_type Σ dom) ++ " → " ++ print_box_type Σ codom
  | TApp t1 t2 => print_box_type Σ t1 ++ " " ++ parens (parenthesize_arg t2) (print_box_type Σ t2)
  | TVar i => "'a" ++ string_of_nat i
  | TInd s =>
    match EPretty.lookup_ind_decl Σ s.(inductive_mind) s.(inductive_ind) with
    | Some oib => oib.(E.ind_name)
    | None => "UndeclaredIductive(" ++ s.(inductive_mind)
                                    ++ ","
                                    ++ s.(inductive_mind)
                                    ++ ")"
    end
  | TConst s => kername_unqual s
  end.

Definition print_type_vars (l : list name) :=
  String.concat " " (map (fun na => match na with
                                    | nAnon => "_"
                                    | nNamed i => i
                                    end) l).

Definition erase_and_print_type
           {cf : checker_flags}
           (after_erasure : box_type -> box_type)
           (p : Ast.program)
  : result (string × string) erase_type_error :=
  let p := fix_program_universes p in
  '(Σ, (tvars, bt)) <- erase_type_program p;;
  ret (print_type_vars tvars, print_box_type Σ bt).

Quote Recursively Definition ex1 := (forall (A B : Type) (a : A * B) (C : Type), A * B * C).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex1) in exact x) =
                Ok ("A B C", "□ → □ → prod 'a0 'a1 → □ → prod (prod 'a0 'a1) 'a2").

Quote Recursively Definition ex2 := (forall (A : Type) (P : A -> Prop), @sig A P).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex2) in exact x) =
                Ok ("A", "□ → □ → sig 'a0 □").

Quote Recursively Definition ex3 := (forall (A : Type) (P : A -> Prop), { a : A | P a }).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex3) in exact x) =
                Ok ("A", "□ → □ → sig 'a0 □").

Quote Recursively Definition ex4 := (forall (A B : Type) (f : A -> B) (n : nat),
                                        Vector.t A n -> Vector.t B n).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex4) in exact x) =
                Ok ("A B", "□ → □ → ('a0 → 'a1) → nat → t 'a0 𝕋 → t 'a1 𝕋").

Quote Recursively Definition ex5 :=
  (forall (A : Type),  list A -> list A -> 0 = 0 -> forall (B : Type), B -> A -> A).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex5) in exact x) =
                Ok ("A B", "□ → list 'a0 → list 'a0 → □ → □ → 'a1 → 'a0 → 'a0").

(* Prenex form that we fail on *)
Quote Recursively Definition ex6 :=
  (forall (A : Type), (forall A : Type, A -> A) -> A -> forall B : Type, B -> nat).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex6) in exact x) =
                Err NotPrenex.

(** Erasing and deboxing *)
Quote Recursively Definition ex7 :=
  (forall (A : Type), A -> forall (B : Type) (C : Type), B -> C).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex7) in exact x) =
                Ok ("A B C", "□ → 'a0 → □ → □ → 'a1 → 'a2").

(** Tesing mutual inductives *)
Inductive tree (A : Set) : Set :=
  node : A -> forest A -> tree A
with forest (A : Set) : Set :=
    leaf : A -> forest A
  | cons : tree A -> forest A -> forest A.

Quote Recursively Definition ex8 := (forall (A: Set), forest A -> tree A -> A).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex8) in exact x) =
                Ok ("A", "□ → forest 'a0 → tree 'a0 → 'a0").

(* We cannot currently handle the following even though we may want to be able to.
   To handle this we would need to do deboxing simultaneously with erasure. *)
Quote Recursively Definition ex9 := (forall (A : 0 = 0 -> Type) (B : Type), option (A eq_refl) -> B).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex9) in exact x) =
                Err NotPrenex.

Quote Recursively Definition ex10 :=
  (forall (A : Type), (forall (B : Type), B -> B) -> A).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex10) in exact x) =
                Err NotPrenex.

Definition non_neg := {n : nat | 0 < n}.

Quote Recursively Definition ex11 := (forall (A : Type), {n : nat | 0 < n} -> A).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex11) in exact x) =
                Ok ("A", "□ → sig nat □ → 'a0").

Quote Recursively Definition ex12 := (forall (A : Type) (P : A -> Prop), unit).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex12) in exact x) =
                Ok ("A", "□ → □ → unit").

Quote Recursively Definition ex13 := (let p := (nat, unit) in fst p × snd p).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex13) in exact x) =
                Ok ("", "prod (fst □ □ 𝕋) (snd □ □ 𝕋)").

Quote Recursively Definition ex14 := (let t := nat in t).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex14) in exact x) =
                Ok ("", "nat").

Quote Recursively Definition ex15 := ((fix f n := match n with
                                                  | 0 => nat
                                                  | S n => nat -> f n
                                                  end) 5).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex15) in exact x) =
                Ok ("", "nat → nat → nat → nat → nat → nat").

Quote Recursively Definition ex16 := (Type -> Type).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex16) in exact x) =
                Ok ("_", "□ → □").

Quote Recursively Definition ex17 := (Type -> Prop).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex17) in exact x) =
                Ok ("", "□").

Quote Recursively Definition ex18 := (False).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex18) in exact x) =
                Ok ("", "□").

Quote Recursively Definition ex19 := (Fin.t 0 -> False).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex19) in exact x) =
                Ok ("", "□").

End erase_type_tests.

Module erase_ind_arity_tests.
Program Definition erase_arity_program (p : Ast.program)
  : result (list oib_type_var) string :=
  let Σ := List.rev (trans_global_decls p.1) in
  G <- match check_wf_env_only_univs Σ with
       | CorrectDecl a => ret a
       | _ => Err "Could not check_wf_env_only_univs"
       end;;
  wrap_typing_result (erase_ind_arity (empty_ext Σ) _ [] (trans p.2) _)
                     (string_of_type_error (empty_ext Σ)).
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.

Quote Recursively Definition ex1 := (forall (A : Type), A -> A -> Prop).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_arity_program ex1) in exact x) =
                Ok
                  [{| tvar_name := nNamed "A";
                      tvar_is_logical := false;
                      tvar_is_arity := true;
                      tvar_is_sort := true |};
                  {|
                    tvar_name := nAnon;
                    tvar_is_logical := false;
                    tvar_is_arity := false;
                    tvar_is_sort := false |};
                  {|
                    tvar_name := nAnon;
                    tvar_is_logical := false;
                    tvar_is_arity := false;
                    tvar_is_sort := false |}].
End erase_ind_arity_tests.

Module erase_global_decls_tests.
Program Definition erase_decls_program (p : Ast.program)
  : result (list (kername × EAst.global_decl)) string :=
  let Σ := List.rev (trans_global_decls p.1) in
  G <- match check_wf_env_only_univs Σ with
       | CorrectDecl a => ret a
       | _ => Err "Could not check_wf_env_only_univs"
       end;;
  map_error string_of_erase_global_decl_error
            (erase_global_decls [] Σ _).

Quote Recursively Definition ex1 := nat.
Compute erase_decls_program ex1.

Quote Recursively Definition ex2 := { n : nat | n = 5 }.
Compute erase_decls_program ex2.

Quote Recursively Definition ex3 := (list nat).
Compute erase_decls_program ex3.

Quote Recursively Definition ex4 := (Vector.t nat 5).
Compute erase_decls_program ex4.
