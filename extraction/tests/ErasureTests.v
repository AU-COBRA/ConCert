From ConCert.Extraction Require Import Erasure TypeAnnotations.
From ConCert.Extraction Require Import ExAst.
From ConCert.Utils Require Import StringExtra.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import SafeTemplateChecker.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import config.

Local Open Scope string_scope.
Import String.
Import PCUICErrors.
Set Equations Transparent.

Local Existing Instance extraction_checker_flags.

Module flag_of_type_tests.
Record type_flag_squashed :=
  { is_logical : bool;
    is_sort : bool;
    is_arity : bool }.

Program Definition flag_of_type_program (p : Ast.program) : type_flag_squashed :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
  let f := flag_of_type (empty_ext Σ) _ [] (trans p.2) _ in
  {| is_logical := Erasure.is_logical f;
     is_sort := if Erasure.is_sort (conv_ar f) then true else false;
     is_arity := if Erasure.is_arity (conv_ar f) then true else false |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

MetaCoq Quote Recursively Definition ex1 := Type.
Example ex1_test :
  flag_of_type_program ex1 =
  {| is_logical := false; is_sort := true; is_arity := true |}.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex2 := nat.
Example ex2_test :
  flag_of_type_program ex2 =
  {| is_logical := false; is_sort := false; is_arity := false |}.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex3 := (nat -> nat).
Example ex3_test :
  flag_of_type_program ex3 =
  {| is_logical := false; is_sort := false; is_arity := false |}.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex4 := (forall A, A).
Example ex4_test :
  flag_of_type_program ex4 =
  {| is_logical := false; is_sort := false; is_arity := false |}.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex5 := (Prop).
Example ex5_test :
  flag_of_type_program ex5 =
  {| is_logical := true; is_sort := true; is_arity := true |}.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex5' := (forall n m: nat, Prop).
Example ex5'_test :
  flag_of_type_program ex5' =
  {| is_logical := true; is_sort := false; is_arity := true |}.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex6 := (Prop -> Type).
Example ex6_test :
  flag_of_type_program ex6 =
  {| is_logical := false; is_sort := false; is_arity := true |}.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex7 := (Type -> Prop).
Example ex7_test :
  flag_of_type_program ex7 =
  {| is_logical := true; is_sort := false; is_arity := true |}.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex8 := (False).
Example ex8_test :
  flag_of_type_program ex8 =
  {| is_logical := true; is_sort := false; is_arity := false |}.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex9 := (Fin.t 0 -> False).
Example ex9_test :
  flag_of_type_program ex9 =
  {| is_logical := true; is_sort := false; is_arity := false |}.
Proof. vm_compute. reflexivity. Qed.
End flag_of_type_tests.

Module erase_type_tests.
Definition string_of_env_error Σ e :=
  match e with
  | IllFormedDecl s e =>
    "IllFormedDecl " ++ s ++ "\nType error: " ++ string_of_type_error Σ e
  | AlreadyDeclared s => "Alreadydeclared " ++ s
  end%string.

Program Definition erase_type_program (p : Ast.program) : P.global_env * (list name * box_type) :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
  (Σ, erase_type (empty_ext Σ) _ (trans p.2) _).
Next Obligation.  Admitted.
Next Obligation.  Admitted.

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
      match @PCUICSafeRetyping.lookup_ind_decl (empty_ext Σ) s with
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
           (p : Ast.program) : string × string :=
  let '(Σ, (tvars, bt)) := erase_type_program p in
  (print_type_vars tvars, print_box_type Σ tvars bt).

MetaCoq Quote Recursively Definition ex1 := (forall (A B : Type) (a : A * B) (C : Type), A * B * C).
Example ex1_test :
  erase_and_print_type id ex1 =
  ("A B C", "□ → □ → prod A B → □ → prod (prod A B) C").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex2 := (forall (A : Type) (P : A -> Prop), @sig A P).
Example ex2_test :
  erase_and_print_type id ex2 =
  ("A", "□ → □ → sig A □").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex3 := (forall (A : Type) (P : A -> Prop), { a : A | P a }).
Example ex3_test :
  erase_and_print_type id ex3 =
  ("A", "□ → □ → sig A □").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex4 := (forall (A B : Type) (f : A -> B) (n : nat),
                                                Vector.t A n -> Vector.t B n).
Example ex4_test :
  erase_and_print_type id ex4 =
  ("A B", "□ → □ → (A → B) → nat → t A 𝕋 → t B 𝕋").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex5 :=
  (forall (A : Type),  list A -> list A -> 0 = 0 -> forall (B : Type), B -> A -> A).
Example ex5_test :
  erase_and_print_type id ex5 =
  ("A B", "□ → list A → list A → □ → □ → B → A → A").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex6 :=
  (forall (A : Type), (forall A : Type, A -> A) -> A -> forall B : Type, B -> nat).
Example ex6_test :
  erase_and_print_type id ex6 =
  ("A B", "□ → (□ → 𝕋 → 𝕋) → A → □ → B → nat").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex7 :=
  (forall (A : Type), A -> forall (B : Type) (C : Type), B -> C).
Example ex7_test :
  erase_and_print_type id ex7 =
  ("A B C", "□ → A → □ → □ → B → C").
Proof. vm_compute. reflexivity. Qed.

(** Tesing mutual inductives *)
Inductive tree (A : Set) : Set :=
  node : A -> forest A -> tree A
with forest (A : Set) : Set :=
  leaf : A -> forest A
| cons : tree A -> forest A -> forest A.

MetaCoq Quote Recursively Definition ex8 := (forall (A: Set), forest A -> tree A -> A).
Example ex8_test :
  erase_and_print_type id ex8 =
  ("A", "□ → forest A → tree A → A").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex9 :=
  (forall (A : 0 = 0 -> Type) (B : Type), option (A eq_refl) -> B).
Example ex9_test :
  erase_and_print_type id ex9 =
  ("A B", "□ → □ → option A → B").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex10 :=
  (forall (A : Type), (forall (B : Type), B -> B) -> A).
Example ex10_test :
  erase_and_print_type id ex10 =
  ("A", "□ → (□ → 𝕋 → 𝕋) → A").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex11 := (forall (A : Type), {n : nat | 0 < n} -> A).
Example ex11_test :
  erase_and_print_type id ex11 =
  ("A", "□ → sig nat □ → A").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex12 := (forall (A : Type) (P : A -> Prop), unit).
Example ex12_test :
  erase_and_print_type id ex12 =
  ("A", "□ → □ → unit").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex13 := (let p := (nat, unit) in fst p × snd p).
Example ex13_test :
  erase_and_print_type id ex13 =
  ("", "prod (fst □ □ 𝕋) (snd □ □ 𝕋)").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex14 := (let t := nat in t).
Example ex14_test :
  erase_and_print_type id ex14 =
  ("", "nat").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex15 := ((fix f n := match n with
                                                          | 0 => nat
                                                          | S n => nat -> f n
                                                          end) 5).
Example ex15_test :
  erase_and_print_type id ex15 =
  ("", "nat → nat → nat → nat → nat → nat").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex16 := (Type -> Type).
Example ex16_test :
  erase_and_print_type id ex16 =
  ("_", "□ → □").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex17 := (Type -> Prop).
Example ex17_test :
  erase_and_print_type id ex17 =
  ("", "□").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex18 := (False).
Example ex18_test :
  erase_and_print_type id ex18 =
  ("", "□").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex19 := (Fin.t 0 -> False).
Example ex19_test :
  erase_and_print_type id ex19 =
  ("", "□").
Proof. vm_compute. reflexivity. Qed.

Axiom match_head : nat.
MetaCoq Quote Recursively Definition ex20 := (match match_head with | 0 => nat | S n => bool end).
Example ex20_test :
  erase_and_print_type id ex20 =
  ("", "𝕋").
Proof. vm_compute. reflexivity. Qed.

Definition zero := 0.
MetaCoq Quote Recursively Definition ex21 := match zero with 0 => nat | S n => bool end.
Example ex21_test :
  erase_and_print_type id ex21 =
  ("", "𝕋").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex22 := match 0 with 0 => nat | S n => bool end.
Example ex22_test :
  erase_and_print_type id ex22 =
  ("", "nat").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex23 :=
  ((fix f (n : nat) :=
     match n with
     | 0 => nat
     | S n => nat -> f n
     end) zero).
Example ex23_test :
  erase_and_print_type id ex23 =
  ("", "𝕋").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex24 :=
  ((fix f (n : nat) :=
     match n with
     | 0 => nat
     | S n => nat -> f n
     end) 2).
Example ex24_test :
  erase_and_print_type id ex24 =
  ("", "nat → nat → nat").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex25 := (forall P : Type -> Type, P nat -> nat).
Example ex25_test :
  erase_and_print_type id ex25 =
  ("P", "□ → P → nat").
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex26 := ((Type -> nat) -> nat).
Example ex26_test :
  erase_and_print_type id ex26 =
  ("", "(□ → nat) → nat").
Proof. vm_compute. reflexivity. Qed.

Definition idT (T : Type) := T.
MetaCoq Quote Recursively Definition ex27 := (idT nat -> idT nat).
Example ex27_test :
  erase_and_print_type id ex27 = ("", "idT nat → idT nat").
Proof. vm_compute. reflexivity. Qed.

(* the type of [proj1_sig] *)
MetaCoq Quote Recursively Definition ex28 := (forall (A : Type) (P : A -> Prop), {x : A | P x} -> A).
Example ex28_test :
  erase_and_print_type id ex28 =
    ("A", "□ → □ → sig A □ → A").
Proof. vm_compute. reflexivity. Qed.


End erase_type_tests.


Import PCUICSafeRetyping.

Program Definition type_of_program (p : Ast.program) : term :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
  type_of (empty_ext Σ) _ _ [] (trans p.2) _.
Next Obligation.  Admitted.
Next Obligation.  Admitted.
Next Obligation.  Admitted.


Program Definition erase_type_of_program (p : Ast.program) : P.global_env * box_type :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
  (Σ, erase_type_of (empty_ext Σ) _ [] (Vector.nil _) (trans p.2) _).
Next Obligation.  Admitted.
Next Obligation.  Admitted.

Definition erase_and_print_type_of
           {cf : checker_flags}
           (after_erasure : box_type -> box_type)
           (p : Ast.program) : string :=
  let '(Σ, bt) :=  erase_type_of_program p in
  (erase_type_tests.print_box_type Σ [] bt).

Program Definition erase_type_program' (p : Ast.global_env * P.term) : P.global_env * ((list name) * box_type) :=
  let Σ := trans_global_decls p.1 in
  (Σ, erase_type_aux (empty_ext Σ) _ [] (Vector.nil _) p.2 _ (Some 0)).
Next Obligation.  Admitted.
Next Obligation.  Admitted.


Fixpoint foldLAlt {A B : Type} (f : A -> B -> A) (l : list B) (a0 : A) : A :=
      match l with
      | [] => a0
      | b :: t => foldLAlt f t (f a0 b)
      end.

MetaCoq Quote Recursively Definition ex28 := @foldLAlt.

Compute type_of_program ex28.
Compute match erase_type_program' (ex28.1, type_of_program ex28) with
        | (Σ, bt) => erase_type_tests.print_box_type Σ bt.1 bt.2
        end.

Definition poly_func {A B : Set} (a : A) (b : B) : A :=
    let inner {B : Set} (b : B) : A := a in
    inner b.

MetaCoq Quote Recursively Definition blah := @poly_func.

Compute type_of_program blah.
Compute erase_type_of_program blah.
Compute erase_and_print_type_of id blah.


Module erase_ind_arity_tests.
Program Definition erase_arity_program (p : Ast.program) : list type_var_info :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
  erase_ind_arity (empty_ext Σ) _ [] (trans p.2) _.
Next Obligation. Admitted.
Next Obligation. Admitted.

MetaCoq Quote Recursively Definition ex1 := (forall (A : Type), A -> A -> Prop).
Example ex1_test :
  erase_arity_program ex1 =
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
Proof. vm_compute. reflexivity. Qed.
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
          (print_box_type Σ (map tvar_name (ExAst.ind_type_vars oib)) bt) in

  let print_ctor '(ctor_name, ctor_types) :=
      nl ++ "| " ++ ctor_name ++
         concat "" (map (print_ctor_type ∘ snd) ctor_types) in

  "data "
    ++ ExAst.ind_name oib ++ concat "" (map (fun tvar => " " ++ print_name (tvar_name tvar))
                                            (ind_type_vars oib))
    ++ concat "" (map print_ctor (ExAst.ind_ctors oib)).

Definition print_inductive (Σ : global_env) (mib : ExAst.mutual_inductive_body) : string :=
  concat nl (map (print_one_inductive_body Σ) (ExAst.ind_bodies mib)).

Axiom assume_wellformed : forall {X}, X.
Axiom cannot_happen : forall {X}, X.
Definition erase_and_print_ind_prog (p : Ast.program) : string :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
  match trans p.2 with
  | P.tInd ind _ =>
    match List.find (fun '(kn, _) => eq_kername kn (inductive_mind ind)) Σ with
    | Some (kn, P.InductiveDecl mib) =>
      let inder := erase_ind
                     (Σ, ind_universes mib) assume_wellformed
                     (inductive_mind ind) mib assume_wellformed in
      print_inductive Σ inder
    | _ => cannot_happen
    end
  | _ => cannot_happen
  end.

MetaCoq Quote Recursively Definition ex1 := nat.
Example ex1_test :
  erase_and_print_ind_prog ex1 = <$
"data nat";
"| O";
"| S nat" $>.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex2 := sig.
Example ex2_test :
  erase_and_print_ind_prog ex2 = <$
"data sig A P";
"| exist □ □ A □" $>.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex3 := list.
Example ex3_test :
  erase_and_print_ind_prog ex3 = <$
"data list A";
"| nil □";
"| cons □ A (list A)" $>.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex4 := option.
Example ex4_test :
  erase_and_print_ind_prog ex4 = <$
"data option A";
"| Some □ A";
"| None □" $>.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex5 := Vector.t.
Example ex5_test :
  erase_and_print_ind_prog ex5 = <$
"data t A _";
"| nil □";
"| cons □ A nat (t A 𝕋)" $>.
Proof. vm_compute. reflexivity. Qed.

Inductive tree (A : Set) : Set :=
  node : A -> forest A -> tree A
with forest (A : Set) : Set :=
  leaf : A -> forest A
| cons : tree A -> forest A -> forest A.
MetaCoq Quote Recursively Definition ex6 := tree.
Example ex6_test :
  erase_and_print_ind_prog ex6 = <$
"data tree A";
"| node □ A (forest A)";
"data forest A";
"| leaf □ A";
"| cons □ (tree A) (forest A)" $>.
Proof. vm_compute. reflexivity. Qed.

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
Example ex7_test :
  erase_and_print_ind_prog ex7 = <$
"data Env";
"| EnvCtr MEnv MTEnv";
"data MEnv";
"| MEnvCtr □ (list Mod)";
"data MTEnv";
"| MTEnvCtr (list MTy)";
"data Mod" ++ nl ++
"| NonParamMod Env";
"| Ftor Env MTy";
"data MTy";
"| MSigma Mod" $>.
Proof. vm_compute. reflexivity. Qed.

Inductive Weird (A : Type) : Type :=
| Nil
| Cons (a : A) (w : Weird (A * A)).

MetaCoq Quote Recursively Definition ex8 := Weird.
Example ex8_test :
  erase_and_print_ind_prog ex8 = <$
"data Weird A";
"| Nil □";
"| Cons □ A (Weird (prod A A))" $>.
Proof. vm_compute. reflexivity. Qed.

Inductive IndexedList : Type -> Type :=
| inil : forall T, IndexedList T
| icons : forall T, T -> IndexedList T -> IndexedList T.

MetaCoq Quote Recursively Definition ex9 := IndexedList.
Example ex9_test :
  erase_and_print_ind_prog ex9 = <$
"data IndexedList _";
"| inil □";
"| icons □ 𝕋 (IndexedList 𝕋)" $>.
Proof. vm_compute. reflexivity. Qed.

MetaCoq Quote Recursively Definition ex10 := Monad.
Example ex10_test :
  erase_and_print_ind_prog ex10 = <$
"data Monad m";
"| Build_Monad (□ → □) (□ → 𝕋 → m) (□ → □ → m → (𝕋 → m) → m)" $>.
Proof. vm_compute. reflexivity. Qed.

Inductive ManyParamsInd (A : Type) (P : Prop) (Q : Prop) (B : Type) :=
  MPIConstr : P -> A -> B -> ManyParamsInd A P Q B.

MetaCoq Quote Recursively Definition ex11 := ManyParamsInd.

Example ManyParamsInd_test :
  erase_and_print_ind_prog ex11 = <$
"data ManyParamsInd A P Q B";
"| MPIConstr □ □ □ □ □ A B" $>.
Proof. vm_compute. reflexivity. Qed.

(* [Q] is non-arity parameter *)
Inductive ManyParamsIndNonArity (A : Type) (P : Prop) (Q : True) (B : Type) :=
  MPINAConstr1 : P -> A -> B -> ManyParamsIndNonArity A P Q B
| MPINAConstr2 : P -> list P -> A*B -> ManyParamsIndNonArity A P Q B.

MetaCoq Quote Recursively Definition ex12 := ManyParamsIndNonArity.

Example ManyParamsIndNonArity_test:
  erase_and_print_ind_prog ex12 = <$
"data ManyParamsIndNonArity A P Q B";
"| MPINAConstr1 □ □ □ □ □ A B";
"| MPINAConstr2 □ □ □ □ □ (list □) (prod A B)" $>.
Proof. vm_compute. reflexivity. Qed.

Inductive PropTypeVarInCtor :=
  ex13_ctor : Prop -> PropTypeVarInCtor.
MetaCoq Quote Recursively Definition ex13 := PropTypeVarInCtor.

Example PropTypeVarInCtor_test :
  erase_and_print_ind_prog ex13 = <$
"data PropTypeVarInCtor";
"| ex13_ctor □" $>.
Proof. vm_compute. reflexivity. Qed.

Inductive IndWithIndex : nat -> Type :=
| ex14_ctor (T : Type) : IndWithIndex 0.
MetaCoq Quote Recursively Definition ex14 := IndWithIndex.

Example IndWithIndex_test :
  erase_and_print_ind_prog ex14 = <$
"data IndWithIndex _";
"| ex14_ctor □" $>.
Proof. vm_compute. reflexivity. Qed.
End erase_ind_tests.

Module erase_type_scheme_tests.
Axiom assume_wellformed : forall {X}, X.
Axiom does_not_happen : forall {X}, X.
Definition erase_and_print_type_scheme (p : Ast.program) : string * string :=
  let p := fix_program_universes p in
  let Σ := trans_global_decls p.1 in
  match trans p.2 with
  | P.tConst kn _ =>
    match lookup_env Σ kn with
    | Some (P.ConstantDecl cst) =>
      let r := erase_constant_decl
                 (Σ, cst_universes cst) assume_wellformed
                 cst assume_wellformed in
      match r with
      | inr (Some (tvars, bt)) =>
        let tvars := map tvar_name tvars in
        (erase_type_tests.print_type_vars tvars,
         erase_type_tests.print_box_type Σ tvars bt)
      | _ => does_not_happen
      end
    | _ => does_not_happen
    end
  | _ => does_not_happen
  end.

Definition nat_alias := nat.
MetaCoq Quote Recursively Definition ex1 := nat_alias.
Example ex1_test :
  erase_and_print_type_scheme ex1 = ("", "nat").
Proof. vm_compute. reflexivity. Qed.

Definition list_nat := list nat.
MetaCoq Quote Recursively Definition ex2 := list_nat.
Example ex2_test :
  erase_and_print_type_scheme ex2 = ("", "list nat").
Proof. vm_compute. reflexivity. Qed.

Definition list_alias T := list T.
MetaCoq Quote Recursively Definition ex3 := list_alias.
Example ex3_test :
  erase_and_print_type_scheme ex3 = ("T", "list T").
Proof. vm_compute. reflexivity. Qed.

Definition list_alias_eta := list.
MetaCoq Quote Recursively Definition ex4 := list_alias_eta.
Example ex4_test :
  (* Names are taken from arity when eta expanding *)
  erase_and_print_type_scheme ex4 = ("A", "list A").
Proof. vm_compute. reflexivity. Qed.

Inductive anon_list : Type -> Type :=
| anil : forall T, anon_list T
| acons : forall T, T -> anon_list T -> anon_list T.

Definition anon_list_alias_eta := anon_list.
MetaCoq Quote Recursively Definition ex5 := anon_list_alias_eta.
Example ex5_test :
  erase_and_print_type_scheme ex5 = ("_", "anon_list _").
Proof. vm_compute. reflexivity. Qed.

Definition option_wrap T := option T.
MetaCoq Quote Recursively Definition ex6 := option_wrap.
Example ex6_test :
  erase_and_print_type_scheme ex6 = ("T", "option T").
Proof. vm_compute. reflexivity. Qed.

Definition vector_wrap T n := Vector.t (option T) n.
MetaCoq Quote Recursively Definition ex7 := vector_wrap.
Example ex7_test :
  erase_and_print_type_scheme ex7 = ("T n", "t (option T) 𝕋").
Proof. vm_compute. reflexivity. Qed.

Definition vector_wrap_eta T := Vector.t (option T).
MetaCoq Quote Recursively Definition ex8 := vector_wrap_eta.
Example ex8_test :
  erase_and_print_type_scheme ex8 = ("T _", "t (option T) 𝕋").
Proof. vm_compute. reflexivity. Qed.

Fixpoint vector_wrap_fix T n := Vector.t (option T) n.
MetaCoq Quote Recursively Definition ex9 := vector_wrap_fix.
Example ex9_test :
  erase_and_print_type_scheme ex9 = ("T n", "𝕋").
Proof. vm_compute. reflexivity. Qed.

End erase_type_scheme_tests.
