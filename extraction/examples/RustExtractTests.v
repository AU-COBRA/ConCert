(** * Tests for extraction to Rust *)
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import RustExtract.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import StringExtra.
From ConCert.Extraction Require Import TopLevelFixes.
From Coq Require Import Arith.
From Coq Require Import String.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import Loader.
From MetaCoq Require Import monad_utils.
From MetaCoq Require Import utils.

Import PrettyPrinterMonad.
Import MonadNotation.
Local Open Scope string.

Instance RustConfig : RustPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     print_full_names := false |}.

Definition general_extract (p : T.program) (ignore: list kername) (TT : list (kername * string)) : result string string :=
  entry <- match p.2 with
           | T.tConst kn _ => ret kn
           | T.tInd ind _ => ret (inductive_mind ind)
           | _ => Err "Expected program to be a tConst or tInd"
           end;;
  Σ <- extract_template_env
         extract_within_coq
         p.1
         (KernameSet.singleton entry)
         (fun k => existsb (eq_kername k) ignore);;
  let Σ := opt_top_level_fixes Σ in
  let TT_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') TT) in
  let is_const '(kn, decl) :=
      match decl with
      | Ex.ConstantDecl _ => true
      | _ => false
      end in
  let p :=
      print_decls Σ TT_fun (filter (negb ∘ is_const) (List.rev Σ));;
      append_nl;;
      append_nl_and_indent;;
      print_decls Σ TT_fun (filter is_const (List.rev Σ));;
      ret tt in
  '(_, s) <- finish_print p;;
  ret s.

Definition extract (p : T.program) : result string string :=
  general_extract p [] [].

Module ex1.
  Definition foo : { n : nat | n = 0 } := exist _ 0 eq_refl.
  Definition bar := proj1_sig foo.
  MetaCoq Quote Recursively Definition ex1 := bar.

  Example ex1_test :
    extract ex1 = Ok <$
"#[derive(Debug, Copy, Clone)]";
"pub enum Sig<'a, A> {";
"  Exist(PhantomData<&'a A>, A)";
"}";
"";
"#[derive(Debug, Copy, Clone)]";
"pub enum Nat<'a> {";
"  O(PhantomData<&'a ()>),";
"  S(PhantomData<&'a ()>, &'a Nat<'a>)";
"}";
"";
"fn proj1_sig<A: Copy>(&'a self, e: &'a Sig<'a, A>) -> A {";
"  match e {";
"    &Sig::Exist(_, a) => {";
"      a";
"    },";
"  }";
"}";
"fn proj1_sig__closure<A: Copy>(&'a self) -> &'a dyn Fn(&'a Sig<'a, A>) -> A {";
"  self.closure(move |e| {";
"    self.proj1_sig(e)";
"  })";
"}";
"";
"fn foo(&'a self) -> &'a Sig<'a, &'a Nat<'a>> {";
"  self.alloc(Sig::Exist(PhantomData, self.alloc(Nat::O(PhantomData))))";
"}";
"";
"fn bar(&'a self) -> &'a Nat<'a> {";
"  self.proj1_sig(self.foo())";
"}" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex1.

Module ex2.
  Definition only_in_type := 5.
  Definition foo : { n : nat | only_in_type = 5 } := exist _ 0 eq_refl.
  Definition bar := proj1_sig foo.
  MetaCoq Quote Recursively Definition ex2 := bar.
  Example ex2_test :
    extract ex2 = Ok <$
"#[derive(Debug, Copy, Clone)]";
"pub enum Sig<'a, A> {";
"  Exist(PhantomData<&'a A>, A)";
"}";
"";
"#[derive(Debug, Copy, Clone)]";
"pub enum Nat<'a> {";
"  O(PhantomData<&'a ()>),";
"  S(PhantomData<&'a ()>, &'a Nat<'a>)";
"}";
"";
"fn proj1_sig<A: Copy>(&'a self, e: &'a Sig<'a, A>) -> A {";
"  match e {";
"    &Sig::Exist(_, a) => {";
"      a";
"    },";
"  }";
"}";
"fn proj1_sig__closure<A: Copy>(&'a self) -> &'a dyn Fn(&'a Sig<'a, A>) -> A {";
"  self.closure(move |e| {";
"    self.proj1_sig(e)";
"  })";
"}";
"";
"fn foo(&'a self) -> &'a Sig<'a, &'a Nat<'a>> {";
"  self.alloc(Sig::Exist(PhantomData, self.alloc(Nat::O(PhantomData))))";
"}";
"";
"fn bar(&'a self) -> &'a Nat<'a> {";
"  self.proj1_sig(self.foo())";
"}" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex2.

Module ex3.
  MetaCoq Quote Recursively Definition quoted := plus.

  Example test :
    extract quoted = Ok <$
"#[derive(Debug, Copy, Clone)]";
"pub enum Nat<'a> {";
"  O(PhantomData<&'a ()>),";
"  S(PhantomData<&'a ()>, &'a Nat<'a>)";
"}";
"";
"fn add(&'a self, n: &'a Nat<'a>, m: &'a Nat<'a>) -> &'a Nat<'a> {";
"  match n {";
"    &Nat::O(_) => {";
"      m";
"    },";
"    &Nat::S(_, p) => {";
"      self.alloc(Nat::S(PhantomData, self.add(p, m)))";
"    },";
"  }";
"}";
"fn add__closure(&'a self) -> &'a dyn Fn(&'a Nat<'a>) -> &'a dyn Fn(&'a Nat<'a>) -> &'a Nat<'a> {";
"  self.closure(move |n| {";
"    self.closure(move |m| {";
"      self.add(n, m)";
"    })";
"  })";
"}" $>.
  Proof. vm_compute. reflexivity. Qed.

End ex3.

Module ex4.
  Fixpoint ack (n m : nat) : nat :=
    match n with
    | O => S m
    | S p => let fix ackn (m : nat) :=
                 match m with
                 | O => ack p 1
                 | S q => ack p (ackn q)
                 end
             in ackn m
    end.
  MetaCoq Quote Recursively Definition quoted := ack.

  Example test :
    extract quoted = Ok <$
"#[derive(Debug, Copy, Clone)]";
"pub enum Nat<'a> {";
"  O(PhantomData<&'a ()>),";
"  S(PhantomData<&'a ()>, &'a Nat<'a>)";
"}";
"";
"fn ack(&'a self, n: &'a Nat<'a>, m: &'a Nat<'a>) -> &'a Nat<'a> {";
"  match n {";
"    &Nat::O(_) => {";
"      self.alloc(Nat::S(PhantomData, m))";
"    },";
"    &Nat::S(_, p) => {";
"      let ackn = {";
"        let ackn = self.alloc(std::cell::Cell::new(None));";
"        ackn.set(Some(";
"          self.closure(move |m2| {";
"            match m2 {";
"              &Nat::O(_) => {";
"                self.ack(p, self.alloc(Nat::S(PhantomData, self.alloc(Nat::O(PhantomData)))))";
"              },";
"              &Nat::S(_, q) => {";
"                self.ack(p, hint_app(ackn.get().unwrap())(q))";
"              },";
"            }";
"          })));";
"        ackn.get().unwrap()";
"      };";
"      hint_app(ackn)(m)";
"    },";
"  }";
"}";
"fn ack__closure(&'a self) -> &'a dyn Fn(&'a Nat<'a>) -> &'a dyn Fn(&'a Nat<'a>) -> &'a Nat<'a> {";
"  self.closure(move |n| {";
"    self.closure(move |m| {";
"      self.ack(n, m)";
"    })";
"  })";
"}" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex4.

Module ex5.
  Definition code (n m : nat) (f : Fin.t (n + m)) : Fin.t (m + n) :=
    match Nat.add_comm n m with
    | eq_refl => f
    end.

  MetaCoq Quote Recursively Definition quoted := code.

  Example test :
    extract quoted = Ok <$
"#[derive(Debug, Copy, Clone)]";
"pub enum Nat<'a> {";
"  O(PhantomData<&'a ()>),";
"  S(PhantomData<&'a ()>, &'a Nat<'a>)";
"}";
"";
"#[derive(Debug, Copy, Clone)]";
"pub enum T<'a> {";
"  F1(PhantomData<&'a ()>, &'a Nat<'a>),";
"  FS(PhantomData<&'a ()>, &'a Nat<'a>, &'a T<'a>)";
"}";
"";
"#[derive(Debug, Copy, Clone)]";
"pub enum Eq<'a, A> {";
"  Eq_refl(PhantomData<&'a A>)";
"}";
"";
"fn code(&'a self, f: &'a T<'a>) -> &'a T<'a> {";
"  f";
"}";
"fn code__closure(&'a self) -> &'a dyn Fn(&'a T<'a>) -> &'a T<'a> {";
"  self.closure(move |f| {";
"    self.code(f)";
"  })";
"}" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex5.
