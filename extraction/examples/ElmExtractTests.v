(** * Tests for extraction to Elm *)
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import ElmExtract.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Utils Require Import StringExtra.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq Require Import utils.

Local Open Scope string.

Instance StandardBoxes : ElmPrintConfig :=
  {| term_box_symbol := "□";
     type_box_symbol := "□";
     any_type_symbol := "𝕋";
     false_elim_def := "false_rec ()";
     print_full_names := false |}.

Definition no_check_args :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform (fun _ => None) true true false false false] |} |}.

Definition general_extract (p : program) (ignore: list kername) (TT : list (kername * string)) : result string string :=
  entry <- match p.2 with
           | tConst kn _ => ret kn
           | tInd ind _ => ret (inductive_mind ind)
           | _ => Err "Expected program to be a tConst or tInd"
           end;;
  Σ <- extract_template_env
         no_check_args
         p.1
         (KernameSet.singleton entry)
         (fun k => existsb (eq_kername k) ignore);;
  let TT_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') TT) in
  '(_, s) <- finish_print (print_env Σ TT_fun);;
  ret s.

Definition extract (p : program) : result string string :=
  general_extract p [] [].

Module ex1.
  Definition foo : { n : nat | n = 0 } := exist 0 eq_refl.
  Definition bar := proj1_sig foo.
  MetaCoq Quote Recursively Definition ex1 := bar.

  Example ex1_test :
    extract ex1 = Ok <$
"type Sig a";
"  = Exist a";
"";
"proj1_sig : Sig a -> a";
"proj1_sig e =";
"  case e of";
"    Exist a ->";
"      a";
"";
"type Nat";
"  = O";
"  | S Nat";
"";
"foo : Sig Nat";
"foo =";
"  Exist O";
"";
"bar : Nat";
"bar =";
"  proj1_sig foo" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex1.

Module ex2.
  Definition only_in_type := 5.
  Definition foo : { n : nat | only_in_type = 5 } := exist 0 eq_refl.
  Definition bar := proj1_sig foo.
  MetaCoq Quote Recursively Definition ex2 := bar.
  Example ex2_test :
    extract ex2 = Ok <$
"type Sig a";
"  = Exist a";
"";
"proj1_sig : Sig a -> a";
"proj1_sig e =";
"  case e of";
"    Exist a ->";
"      a";
"";
"type Nat";
"  = O";
"  | S Nat";
"";
"foo : Sig Nat";
"foo =";
"  Exist O";
"";
"bar : Nat";
"bar =";
"  proj1_sig foo" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex2.

Module ex3.
  Definition foo (f : 5 = 5 -> nat -> nat) := f eq_refl 0.
  Definition bar (p : 5 = 5) (n : nat) := n.
  (* bar must be eta expanded in the following *)
  Definition baz := foo bar.
  MetaCoq Quote Recursively Definition ex3 := baz.

  Example ex3_test :
    extract ex3 = Ok <$
"type Nat";
"  = O";
"  | S Nat";
"";
"foo : (□ -> Nat -> Nat) -> Nat";
"foo f =";
"  f □ O";
"";
"bar : Nat -> Nat";
"bar n =";
"  n";
"";
"baz : Nat";
"baz =";
"  foo (\x -> bar)" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex3.

Module ex4.
  Definition foo : {0 = 0} + {0 <> 0} := left eq_refl.
  MetaCoq Quote Recursively Definition ex4 := foo.

  Example ex4_test :
    extract ex4 = Ok <$
"type Sumbool";
"  = Left";
"  | Right";
"";
"foo : Sumbool";
"foo =";
"  Left" $>.
  Proof. now vm_compute. Qed.
End ex4.

Module ex5.
  (* Using normal sum means it cannot be deboxed away *)
  Definition foo : (0 = 0) + (0 <> 0) := inl eq_refl.
  MetaCoq Quote Recursively Definition ex5 := foo.

  Example ex5_test :
    extract ex5 = Ok <$
"type Sum a b";
"  = Inl a";
"  | Inr b";
"";
"foo : Sum □ □";
"foo =";
"  Inl □" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex5.

Module ex6.
  Definition foo (f : 5 = 5 -> 5 = 5 -> nat -> nat) := f eq_refl eq_refl 0.
  Definition bar (m : nat) (p q : 5 = 5) (n : nat) := m + n.
  (* bar must be eta expanded twice and m and n need to be lifted *)
  Definition baz := (fun m n => foo (bar (m + n))) 0.
  MetaCoq Quote Recursively Definition ex6 := baz.

  Example ex6_test :
    extract ex6 = Ok <$
"type Nat";
"  = O";
"  | S Nat";
"";
"foo : (□ -> □ -> Nat -> Nat) -> Nat";
"foo f =";
"  f □ □ O";
"";
"add : Nat -> Nat -> Nat";
"add n m =";
"  case n of";
"    O ->";
"      m";
"    S p ->";
"      S (add p m)";
"";
"bar : Nat -> Nat -> Nat";
"bar m n =";
"  add m n";
"";
"baz : Nat -> Nat";
"baz =";
"  (\m n -> foo (\x x2 -> bar (add m n))) O" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex6.

Module ex7.
  (* Dearg through lets *)
  Definition foo (n : nat) (x := 0) (p : x = 0) (m : nat) := match n with 0 => m | _ => n end.
  Definition bar := foo 1 eq_refl 0.
  MetaCoq Quote Recursively Definition ex7 := bar.

  Example ex7_test :
    extract ex7 = Ok <$
"type Nat";
"  = O";
"  | S Nat";
"";
"foo : Nat -> Nat -> Nat";
"foo n =";
"  let";
"    x =";
"      O";
"  in";
"  \m -> case n of";
"          O ->";
"            m";
"          S n0 ->";
"            n";
"";
"bar : Nat";
"bar =";
"  foo (S O) O" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex7.

Module ex8.
  (* Remove P, Q, and proofs from inductive *)
  Inductive ManyParamsInd (A : Type) (P : Prop) (Q : Prop) (B : Type) :=
    MPIConstr : P -> A -> B -> ManyParamsInd A P Q B.

  MetaCoq Quote Recursively Definition ex8 := ManyParamsInd.

  Example ex8_test :
    extract ex8 = Ok <$
"type ManyParamsInd a b";
"  = MPIConstr a b" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex8.

Module ex9.
  (* [Q] is non-arity parameter *)
  Inductive ManyParamsIndNonArity (A : Type) (P : Prop) (Q : True) (B : Type) :=
    MPINAConstr1 : P -> A -> B -> ManyParamsIndNonArity A P Q B
  | MPINAConstr2 : P -> list P -> A*B -> ManyParamsIndNonArity A P Q B.

  MetaCoq Quote Recursively Definition ex9 := ManyParamsIndNonArity.

  Example ManyParamsIndNonArity_test:
    extract ex9 = Ok <$
"type List a";
"  = Nil";
"  | Cons a (List a)";
"";
"type Prod a b";
"  = Pair a b";
"";
"type ManyParamsIndNonArity a b";
"  = MPINAConstr1 a b";
"  | MPINAConstr2 (List □) (Prod a b)" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex9.

Module ex10.
  (* Debox axiom *)
  Definition foo (x : { n : nat | n > 0 }) := proj1_sig x.
  MetaCoq Quote Recursively Definition ex10 := foo.

  Example ex10_test :
    general_extract ex10 [<%% @proj1_sig %%>] [] = Ok <$
"type Sig a";
"  = Exist a";
"";
"type Nat";
"  = O";
"  | S Nat";
"";
"foo : Sig Nat -> Nat";
"foo x =";
"  proj1_sig x" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex10.

Module ex11.
  MetaCoq Quote Recursively Definition ex11 := Monad.
  Example Monad_test :
    extract ex11 = Ok <$
"type Monad m";
"  = Build_Monad (□ -> 𝕋 -> m) (□ -> □ -> m -> (𝕋 -> m) -> m)" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex11.

Module ex12.
  Definition idT (T : Type) := T.
  Definition weird_id {T} (i : idT T) := i.
  MetaCoq Quote Recursively Definition ex := @weird_id.
  Example test :
    extract ex = Ok <$
"type alias IdT t = t";
"";
"weird_id : IdT t -> IdT t";
"weird_id i =";
"  i" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex12.

Module ex13.
  Definition opt := option.
  Definition unwrap (o : opt nat) : nat := match o with
                                           | Some x => x
                                           | None => 0
                                           end.
  MetaCoq Quote Recursively Definition ex := unwrap.
  Example test :
    extract ex = Ok <$
"type Option a";
"  = Some a";
"  | None";
"";
"type alias Opt a = Option a";
"";
"type Nat";
"  = O";
"  | S Nat";
"";
"unwrap : Opt Nat -> Nat";
"unwrap o =";
"  case o of";
"    Some x ->";
"      x";
"    None ->";
"      O" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex13.

Module ex_infix1.

  Definition TT : list (kername * string) :=
    [ remap <%% list %%> "List"
    ; ((<%% list %%>.1, "nil"), "[]")
    ; ((<%% list %%>.1, "cons"), "(::)")
    ].

  MetaCoq Quote Recursively Definition ex := map.

  Example test :
    general_extract ex (map fst TT) TT = Ok <$
"";
"";
"map : (a -> b) -> List a -> List b";
"map f =";
"  let";
"    map2 l =";
"      case l of";
"        [] ->";
"          []";
"        a :: t ->";
"          (::) (f a) (map2 t)";
"  in";
"  map2" $>. reflexivity. Qed.
End ex_infix1.

Module recursor_ex.

  Program Definition test {A B : Type} (f : A -> B) (xs : list A) : list B :=
    list_rect (fun x => list B) [] (fun x _ rec => f x :: rec) xs.

  Lemma test_is_map : @test = @map.
  Proof. reflexivity. Qed.

  Print test.

  MetaCoq Quote Recursively Definition ex := @test.

  Compute general_extract ex [] [].
End recursor_ex.

Module type_scheme_ex.

  Definition general_extract_tc (p : program) (ignore: list kername) (TT : list (kername * string)) : TemplateMonad string :=
  entry <- match p.2 with
           | tConst kn _ => ret kn
           | tInd ind _ => ret (inductive_mind ind)
           | _ => tmFail "Expected program to be a tConst or tInd"
           end;;
  res <- tmEval lazy (extract_template_env
                       no_check_args
                       p.1
                       (KernameSet.singleton entry)
                       (fun k => existsb (eq_kername k) ignore));;
  match res with
  | Ok Σ =>
    tmPrint Σ;;
    let TT_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') TT) in
    s <- tmEval lazy (finish_print (print_env Σ TT_fun));;
    match s with
    | Ok (_,s) => ret s
    | Err s => tmFail s
    end
  | Err s => tmFail s
  end.


  (* A simple type abbreviation *)

  Definition Arrow (A B : Type) := A -> B.

  MetaCoq Quote Recursively Definition Arrow_syn := Arrow.

  Example Arrow_test :
    general_extract Arrow_syn [] [] = Ok "type alias Arrow a b = a -> b".
  Proof. vm_compute. reflexivity. Qed.

  Definition Triple (A B C : Type) := A * B * C.

  MetaCoq Quote Recursively Definition Triple_syn := Triple.

  MetaCoq Run (general_extract_tc Triple_syn [] []).

  Example Triple_test :
    general_extract Triple_syn [] [] = Ok <$
"type Prod a b";
"  = Pair a b";
"";
"type alias Triple a b c = Prod (Prod a b) c" $>.
  Proof. vm_compute. reflexivity. Qed.

  Module LetouzeyExample.
  (* An example from Letouzey's thesis, Section 3.3.4 *)

  Definition P (b : bool) : Set := if b then nat else bool.
  Definition Sch3 : (bool -> Set) -> Set := fun X => X true -> X false.
  Definition Sch3_applied := (fun X => X true -> X false) (fun b => if b then nat else bool).

  MetaCoq Quote Recursively Definition Sch3_syn := Sch3.

  Example Sch3_test :
    general_extract Sch3_syn [] [] = Ok "type alias Sch3 x = x -> x".
  Proof. vm_compute. reflexivity. Qed.

  MetaCoq Quote Recursively Definition Sch3_applied_syn := Sch3_applied.

  (* In this case, the application reduces to a type with no type parameters *)
  Example Sch3_applied_test :
    general_extract Sch3_applied_syn [] [] = Ok <$
"type Bool";
"  = True";
"  | False";
"";
"type Nat";
"  = O";
"  | S Nat";
"";
"type alias Sch3_applied = Nat -> Bool" $>.
  Proof. vm_compute. reflexivity. Qed.

  End LetouzeyExample.


  (* [Vec] is a common example of using a type scheme to abbreviate a type *)

  Definition vec (A : Type) (n : nat) := {xs : list A | length xs = n}.

  Program Definition singleton_vec (n : nat) : vec nat 1 := [n].

  MetaCoq Quote Recursively Definition singleton_vec_syn := singleton_vec.

  MetaCoq Run (general_extract_tc singleton_vec_syn [] []).

  Example singleton_vec_test:
    general_extract singleton_vec_syn [] [] = Ok <$
"type Nat";
"  = O";
"  | S Nat";
"";
"type Sig a";
"  = Exist a";
"";
"type List a";
"  = Nil";
"  | Cons a (List a)";
"";
"type alias Vec a = Sig (List a)";
"";
"singleton_vec : Nat -> Vec Nat";
"singleton_vec n =";
"  Exist (Cons n Nil)" $>.
  Proof. vm_compute. reflexivity. Qed.

End type_scheme_ex.
