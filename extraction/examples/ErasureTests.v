From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import ExAst.
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

Module flag_of_type_tests.
Record type_flag_squashed := {
  is_logical : bool;
  is_sort : bool;
  is_arity : bool }.

Program Definition flag_of_type_program (p : Ast.program)
  : result type_flag_squashed string :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
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

MetaCoq Quote Recursively Definition ex1 := Type.
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex1) in exact x) =
                Ok {| is_logical := false; is_sort := true; is_arity := true |}.

MetaCoq Quote Recursively Definition ex2 := nat.
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex2) in exact x) =
                Ok {| is_logical := false; is_sort := false; is_arity := false |}.

MetaCoq Quote Recursively Definition ex3 := (nat -> nat).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex3) in exact x) =
                Ok {| is_logical := false; is_sort := false; is_arity := false |}.

MetaCoq Quote Recursively Definition ex4 := (forall A, A).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex4) in exact x) =
                Ok {| is_logical := false; is_sort := false; is_arity := false |}.

MetaCoq Quote Recursively Definition ex5 := (Prop).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex5) in exact x) =
                Ok {| is_logical := true; is_sort := true; is_arity := true |}.

MetaCoq Quote Recursively Definition ex5' := (forall n m: nat, Prop).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex5') in exact x) =
                Ok {| is_logical := true; is_sort := false; is_arity := true |}.

MetaCoq Quote Recursively Definition ex6 := (Prop -> Type).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex6) in exact x) =
                Ok {| is_logical := false; is_sort := false; is_arity := true |}.

MetaCoq Quote Recursively Definition ex7 := (Type -> Prop).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex7) in exact x) =
                Ok {| is_logical := true; is_sort := false; is_arity := true |}.

MetaCoq Quote Recursively Definition ex8 := (False).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex8) in exact x) =
                Ok {| is_logical := true; is_sort := false; is_arity := false |}.

MetaCoq Quote Recursively Definition ex9 := (Fin.t 0 -> False).
Check eq_refl : ltac:(let x := eval vm_compute in (flag_of_type_program ex9) in exact x) =
                Ok {| is_logical := true; is_sort := false; is_arity := false |}.
End flag_of_type_tests.

Module erase_type_tests.
Definition string_of_env_error Σ e :=
  match e with
  | IllFormedDecl s e =>
    "IllFormedDecl " ++ s ++ "\nType error: " ++ string_of_type_error Σ e
  | AlreadyDeclared s => "Alreadydeclared " ++ s
  end%string.

Program Definition erase_type_program (p : Ast.program)
  : result (P.global_env * (list name * box_type)) erase_type_error :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
  G <- match check_wf_env_only_univs Σ with
       | CorrectDecl a => ret a
       | EnvError Σ err => Err (GeneralError
                                  ("Could not check_wf_env_only_univs: "
                                     ++ string_of_env_error Σ err))
       end;;
  t <- erase_type (empty_ext Σ) _ [] (Vector.nil _) (trans p.2) _ [];;
  ret (Σ, t).
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

Definition parenthesize_arg (a : box_type) : bool :=
  match a with
  | TBox
  | TAny
  | TVar _
  | TInd _
  | TConst _ => true
  | _ => false
  end.

Definition print_name (na : name) : string :=
  match na with
  | nNamed s => s
  | nAnon => "_"
  end.

Definition print_box_type (Σ : P.global_env) (tvars : list name) :=
  fix f (bt : box_type) :=
  match bt with
  | TBox => "□"
  | TAny => "𝕋"
  | TArr dom codom => parens (negb (is_arr dom)) (f dom) ++ " → " ++ f codom
  | TApp t1 t2 => f t1 ++ " " ++ parens (parenthesize_arg t2) (f t2)
  | TVar i => match nth_error tvars i with
              | Some na => print_name na
              | None => "'a" ++ string_of_nat i
              end
  | TInd s =>
    match @lookup_ind_decl (empty_ext Σ) s with
    | Checked (decl; oib; _) => oib.(P.ind_name)
    | TypeError te => "UndeclaredInductive("
                        ++ string_of_kername s.(inductive_mind)
                        ++ "," ++ string_of_nat s.(inductive_ind) ++ ")"
    end
  | TConst s => s.2
  end.

Definition print_type_vars (l : list name) :=
  String.concat " " (map print_name l).

Definition erase_and_print_type
           {cf : checker_flags}
           (after_erasure : box_type -> box_type)
           (p : Ast.program)
  : result (string × string) erase_type_error :=
  '(Σ, (tvars, bt)) <- erase_type_program p;;
  ret (print_type_vars tvars, print_box_type Σ tvars bt).

MetaCoq Quote Recursively Definition ex1 := (forall (A B : Type) (a : A * B) (C : Type), A * B * C).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex1) in exact x) =
                Ok ("A B C", "□ → □ → prod A B → □ → prod (prod A B) C").

MetaCoq Quote Recursively Definition ex2 := (forall (A : Type) (P : A -> Prop), @sig A P).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex2) in exact x) =
                Ok ("A", "□ → □ → sig A □").

MetaCoq Quote Recursively Definition ex3 := (forall (A : Type) (P : A -> Prop), { a : A | P a }).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex3) in exact x) =
                Ok ("A", "□ → □ → sig A □").

MetaCoq Quote Recursively Definition ex4 := (forall (A B : Type) (f : A -> B) (n : nat),
                                        Vector.t A n -> Vector.t B n).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex4) in exact x) =
                Ok ("A B", "□ → □ → (A → B) → nat → t A 𝕋 → t B 𝕋").

MetaCoq Quote Recursively Definition ex5 :=
  (forall (A : Type),  list A -> list A -> 0 = 0 -> forall (B : Type), B -> A -> A).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex5) in exact x) =
                Ok ("A B", "□ → list A → list A → □ → □ → B → A → A").

(* Prenex form that we fail on *)
MetaCoq Quote Recursively Definition ex6 :=
  (forall (A : Type), (forall A : Type, A -> A) -> A -> forall B : Type, B -> nat).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex6) in exact x) =
                Err NotPrenex.

(** Erasing and deboxing *)
MetaCoq Quote Recursively Definition ex7 :=
  (forall (A : Type), A -> forall (B : Type) (C : Type), B -> C).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex7) in exact x) =
                Ok ("A B C", "□ → A → □ → □ → B → C").

(** Tesing mutual inductives *)
Inductive tree (A : Set) : Set :=
  node : A -> forest A -> tree A
with forest (A : Set) : Set :=
    leaf : A -> forest A
  | cons : tree A -> forest A -> forest A.

MetaCoq Quote Recursively Definition ex8 := (forall (A: Set), forest A -> tree A -> A).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex8) in exact x) =
                Ok ("A", "□ → forest A → tree A → A").

(* We cannot currently handle the following even though we may want to be able to.
   To handle this we would need to do deboxing simultaneously with erasure. *)
MetaCoq Quote Recursively Definition ex9 := (forall (A : 0 = 0 -> Type) (B : Type), option (A eq_refl) -> B).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex9) in exact x) =
                Err NotPrenex.

MetaCoq Quote Recursively Definition ex10 :=
  (forall (A : Type), (forall (B : Type), B -> B) -> A).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex10) in exact x) =
                Err NotPrenex.

MetaCoq Quote Recursively Definition ex11 := (forall (A : Type), {n : nat | 0 < n} -> A).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex11) in exact x) =
                Ok ("A", "□ → sig nat □ → A").

MetaCoq Quote Recursively Definition ex12 := (forall (A : Type) (P : A -> Prop), unit).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex12) in exact x) =
                Ok ("A", "□ → □ → unit").

MetaCoq Quote Recursively Definition ex13 := (let p := (nat, unit) in fst p × snd p).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex13) in exact x) =
                Ok ("", "prod (fst □ □ 𝕋) (snd □ □ 𝕋)").

MetaCoq Quote Recursively Definition ex14 := (let t := nat in t).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex14) in exact x) =
                Ok ("", "nat").

MetaCoq Quote Recursively Definition ex15 := ((fix f n := match n with
                                                  | 0 => nat
                                                  | S n => nat -> f n
                                                  end) 5).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex15) in exact x) =
                Ok ("", "nat → nat → nat → nat → nat → nat").

MetaCoq Quote Recursively Definition ex16 := (Type -> Type).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex16) in exact x) =
                Ok ("_", "□ → □").

MetaCoq Quote Recursively Definition ex17 := (Type -> Prop).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex17) in exact x) =
                Ok ("", "□").

MetaCoq Quote Recursively Definition ex18 := (False).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex18) in exact x) =
                Ok ("", "□").

MetaCoq Quote Recursively Definition ex19 := (Fin.t 0 -> False).
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_type id ex19) in exact x) =
                Ok ("", "□").

End erase_type_tests.

Module erase_ind_arity_tests.
Program Definition erase_arity_program (p : Ast.program)
  : result (list oib_type_var) string :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
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

MetaCoq Quote Recursively Definition ex1 := (forall (A : Type), A -> A -> Prop).
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

Module erase_ind_tests.
Definition print_box_type := erase_type_tests.print_box_type.
Definition print_name := erase_type_tests.print_name.

Definition parenthesize_ctor_type (bt : box_type) : bool :=
  match bt with
  | TBox
  | TAny
  | TVar _
  | TInd _
  | TConst _ => false
  | _ => true
  end.

Definition print_one_inductive_body
         (Σ : global_env)
         (oib : ExAst.one_inductive_body) : string :=
  let print_ctor_type bt :=
      " " ++ parens
          (negb (parenthesize_ctor_type bt))
          (print_box_type Σ (map tvar_name (ExAst.ind_ctor_type_vars oib)) bt) in

  let print_ctor '(ctor_name, ctor_types) :=
      nl ++ "| " ++ ctor_name ++
         concat "" (map print_ctor_type ctor_types) in

  "data "
    ++ ExAst.ind_name oib ++ concat "" (map (fun tvar => " " ++ print_name (tvar_name tvar))
                                            (ind_type_vars oib))
    ++ concat "" (map print_ctor (ExAst.ind_ctors oib)).

Definition print_inductive (Σ : global_env) (mib : ExAst.mutual_inductive_body) : string :=
  concat nl (map (print_one_inductive_body Σ) (ExAst.ind_bodies mib)).

Axiom assume_wellformed : forall {X}, X.
Axiom cannot_happen : forall {X}, X.
Definition erase_and_print_ind_prog (p : Ast.program)
           : result string erase_ind_error :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
  match trans p.2 with
  | P.tInd ind _ =>
    match List.find (fun '(kn, _) => eq_kername kn (inductive_mind ind)) Σ with
    | Some (kn, P.InductiveDecl mib) =>
      inder <- erase_ind
                 (Σ, ind_universes mib) assume_wellformed
                 (inductive_mind ind) mib assume_wellformed;;
      ret (print_inductive Σ inder)
    | _ => cannot_happen
    end
  | _ => cannot_happen
  end.

MetaCoq Quote Recursively Definition ex1 := nat.
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_ind_prog ex1) in exact x) =
                Ok ("data nat" ++ nl ++
                    "| O" ++ nl ++
                    "| S nat").

MetaCoq Quote Recursively Definition ex2 := sig.
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_ind_prog ex2) in exact x) =
                Ok ("data sig A P" ++ nl ++
                    "| exist □ □ A □").

MetaCoq Quote Recursively Definition ex3 := list.
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_ind_prog ex3) in exact x) =
                Ok ("data list A" ++ nl ++
                    "| nil □" ++ nl ++
                    "| cons □ A (list A)").

MetaCoq Quote Recursively Definition ex4 := option.
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_ind_prog ex4) in exact x) =
                Ok ("data option A" ++ nl ++
                    "| Some □ A" ++ nl ++
                    "| None □").

MetaCoq Quote Recursively Definition ex5 := Vector.t.
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_ind_prog ex5) in exact x) =
                Ok ("data t A _" ++ nl ++
                    "| nil □" ++ nl ++
                    "| cons □ A nat (t A 𝕋)").

Inductive tree (A : Set) : Set :=
  node : A -> forest A -> tree A
with forest (A : Set) : Set :=
    leaf : A -> forest A
  | cons : tree A -> forest A -> forest A.
MetaCoq Quote Recursively Definition ex6 := tree.
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_ind_prog ex6) in exact x) =
                Ok ("data tree A" ++ nl ++
                    "| node □ A (forest A)" ++ nl ++
                    "data forest A" ++ nl ++
                    "| leaf □ A" ++ nl ++
                    "| cons □ (tree A) (forest A)").

Inductive Env :=
     | EnvCtr : MEnv -> MTEnv -> Env
with MEnv :=
     | MEnvCtr : False -> list Mod -> MEnv
with MTEnv :=
     | MTEnvCtr : list MTy -> MTEnv
with Mod :=
     | NonParamMod : Env -> Mod
     | Ftor : Env -> MTy -> Mod
with MTy :=
     | MSigma : Mod -> MTy.
MetaCoq Quote Recursively Definition ex7 := Env.
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_ind_prog ex7) in exact x) =
                Ok ("data Env" ++ nl ++
                    "| EnvCtr MEnv MTEnv" ++ nl ++
                    "data MEnv" ++ nl ++
                    "| MEnvCtr □ (list Mod)" ++ nl ++
                    "data MTEnv" ++ nl ++
                    "| MTEnvCtr (list MTy)" ++ nl ++
                    "data Mod" ++ nl ++
                    "| NonParamMod Env" ++ nl ++
                    "| Ftor Env MTy" ++ nl ++
                    "data MTy" ++ nl ++
                    "| MSigma Mod").

Inductive Weird (A : Type) : Type :=
| Nil
| Cons (a : A) (w : Weird (A * A)).

MetaCoq Quote Recursively Definition ex8 := Weird.
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_ind_prog ex8) in exact x) =
                Ok ("data Weird A" ++ nl ++
                    "| Nil □" ++ nl ++
                    "| Cons □ A (Weird (prod A A))").

Inductive IndexedList : Type -> Type :=
| inil : forall T, IndexedList T
| icons : forall T, T -> IndexedList T -> IndexedList T.

MetaCoq Quote Recursively Definition ex9 := IndexedList.
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_ind_prog ex9) in exact x) =
                Err (EraseIndBodyError "IndexedList" (CtorUnmappedTypeVariables "inil")).

MetaCoq Quote Recursively Definition ex10 := Monad.
Check eq_refl : ltac:(let x := eval vm_compute in (erase_and_print_ind_prog ex10) in exact x) =
                Err (EraseIndBodyError "Monad" (EraseCtorError "Build_Monad" NotPrenex)).

Inductive ManyParamsInd (A : Type) (P : Prop) (Q : Prop) (B : Type) :=
  MPIConstr : P -> A -> B -> ManyParamsInd A P Q B.

MetaCoq Quote Recursively Definition ex11 := ManyParamsInd.

Example ManyParamsInd_test :
  erase_and_print_ind_prog ex11 =
  Ok <$ "data ManyParamsInd A P Q B";
        "| MPIConstr □ □ □ □ □ A B" $>.
Proof. reflexivity. Qed.

(* [Q] is non-arity parameter *)
Inductive ManyParamsIndNonArity (A : Type) (P : Prop) (Q : True) (B : Type) :=
  MPINAConstr1 : P -> A -> B -> ManyParamsIndNonArity A P Q B
| MPINAConstr2 : P -> list P -> A*B -> ManyParamsIndNonArity A P Q B.

MetaCoq Quote Recursively Definition ex12 := ManyParamsIndNonArity.

Example ManyParamsIndNonArity_test:
  erase_and_print_ind_prog ex12 =
  Ok <$ "data ManyParamsIndNonArity A P Q B";
        "| MPINAConstr1 □ □ □ □ □ A B";
        "| MPINAConstr2 □ □ □ □ □ (list □) (prod A B)" $>.
Proof. vm_compute. reflexivity. Qed.

Inductive PropTypeVarInCtor :=
  ex13_ctor : Prop -> PropTypeVarInCtor.
MetaCoq Quote Recursively Definition ex13 := PropTypeVarInCtor.

Example PropTypeVarInCtor_test :
  erase_and_print_ind_prog ex13 =
  Ok <$ "data PropTypeVarInCtor";
        "| ex13_ctor □" $>.
Proof. vm_compute. reflexivity. Qed.

Inductive IndWithIndex : nat -> Type :=
| ex14_ctor (T : Type) : IndWithIndex 0.
MetaCoq Quote Recursively Definition ex14 := IndWithIndex.

Example IndWithIndex_test :
  erase_and_print_ind_prog ex14 =
  Err (EraseIndBodyError "IndWithIndex" (CtorUnmappedTypeVariables "ex14_ctor")).
Proof. vm_compute. reflexivity. Qed.

End erase_ind_tests.
