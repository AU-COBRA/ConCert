(** * Tests for extraction to Rust *)
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import RustExtract.
From ConCert.Extraction Require Import Printing.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Utils Require Import StringExtra.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Kernames.
From MetaCoq Require Import utils.

Import PrettyPrinterMonad.
Local Open Scope string.

Instance RustConfig : RustPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     print_full_names := false |}.

Definition default_attrs : ind_attr_map := fun _ => "#[derive(Debug, Clone)]".

Definition extract (p : T.program) : result string string :=
  entry <- match p.2 with
           | T.tConst kn _ => ret kn
           | T.tInd ind _ => ret (inductive_mind ind)
           | _ => Err "Expected program to be a tConst or tInd"
           end;;
  Σ <- extract_template_env
         (extract_rust_within_coq (fun _ => None) (fun _ => false))
         p.1
         (KernameSet.singleton entry)
         (fun k => false);;
  let is_const '(kn, decl) :=
      match decl with
      | Ex.ConstantDecl _ => true
      | _ => false
      end in
  (* Filtering out empty type declarations *)
  (* TODO: possibly, move to extraction (requires modifications of the correctness proof) *)
  let Σ := filter (fun '(kn,d) => negb (is_empty_type_decl d)) Σ in

  let p :=
      print_decls Σ no_remaps default_attrs (filter (negb ∘ is_const) (List.rev Σ));;
      append_nl;;
      append_nl;;
      print_decls Σ no_remaps default_attrs (filter is_const (List.rev Σ));;
      ret tt in
  '(_, s) <- finish_print p;;
  ret s.

Module ex1.
  Definition foo : { n : nat | n = 0 } := exist 0 eq_refl.
  Definition bar := proj1_sig foo.
  MetaCoq Quote Recursively Definition ex1 := bar.

  Example ex1_test :
    extract ex1 = Ok <$
"#[derive(Debug, Clone)]";
"pub enum Sig<'a, A> {";
"  exist(PhantomData<&'a A>, A)";
"}";
"";
"#[derive(Debug, Clone)]";
"pub enum Nat<'a> {";
"  O(PhantomData<&'a ()>),";
"  S(PhantomData<&'a ()>, &'a Nat<'a>)";
"}";
"";
"fn proj1_sig<A: Copy>(&'a self, e: &'a Sig<'a, A>) -> A {";
"  match e {";
"    &Sig::exist(_, a) => {";
"      a";
"    },";
"  }";
"}";
"fn proj1_sig__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a Sig<'a, A>) -> A {";
"  self.closure(move |e| {";
"    self.proj1_sig(";
"      e)";
"  })";
"}";
"";
"fn foo(&'a self) -> &'a Sig<'a, &'a Nat<'a>> {";
"  self.alloc(";
"    Sig::exist(";
"      PhantomData,";
"      self.alloc(";
"        Nat::O(";
"          PhantomData))))";
"}";
"";
"fn bar(&'a self) -> &'a Nat<'a> {";
"  self.proj1_sig(";
"    self.foo())";
"}" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex1.

Module ex2.
  Definition only_in_type := 5.
  Definition foo : { n : nat | only_in_type = 5 } := exist 0 eq_refl.
  Definition bar := proj1_sig foo.
  MetaCoq Quote Recursively Definition ex2 := bar.
  Example ex2_test :
    extract ex2 = Ok <$
"#[derive(Debug, Clone)]";
"pub enum Sig<'a, A> {";
"  exist(PhantomData<&'a A>, A)";
"}";
"";
"#[derive(Debug, Clone)]";
"pub enum Nat<'a> {";
"  O(PhantomData<&'a ()>),";
"  S(PhantomData<&'a ()>, &'a Nat<'a>)";
"}";
"";
"fn proj1_sig<A: Copy>(&'a self, e: &'a Sig<'a, A>) -> A {";
"  match e {";
"    &Sig::exist(_, a) => {";
"      a";
"    },";
"  }";
"}";
"fn proj1_sig__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a Sig<'a, A>) -> A {";
"  self.closure(move |e| {";
"    self.proj1_sig(";
"      e)";
"  })";
"}";
"";
"fn foo(&'a self) -> &'a Sig<'a, &'a Nat<'a>> {";
"  self.alloc(";
"    Sig::exist(";
"      PhantomData,";
"      self.alloc(";
"        Nat::O(";
"          PhantomData))))";
"}";
"";
"fn bar(&'a self) -> &'a Nat<'a> {";
"  self.proj1_sig(";
"    self.foo())";
"}" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex2.

Module ex3.
  MetaCoq Quote Recursively Definition quoted := plus.

  Example test :
    extract quoted = Ok <$
"#[derive(Debug, Clone)]";
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
"      self.alloc(";
"        Nat::S(";
"          PhantomData,";
"          self.add(";
"            p,";
"            m)))";
"    },";
"  }";
"}";
"fn add__curried(&'a self) -> &'a dyn Fn(&'a Nat<'a>) -> &'a dyn Fn(&'a Nat<'a>) -> &'a Nat<'a> {";
"  self.closure(move |n| {";
"    self.closure(move |m| {";
"      self.add(";
"        n,";
"        m)";
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
"#[derive(Debug, Clone)]";
"pub enum Nat<'a> {";
"  O(PhantomData<&'a ()>),";
"  S(PhantomData<&'a ()>, &'a Nat<'a>)";
"}";
"";
"fn ack(&'a self, n: &'a Nat<'a>, m: &'a Nat<'a>) -> &'a Nat<'a> {";
"  match n {";
"    &Nat::O(_) => {";
"      self.alloc(";
"        Nat::S(";
"          PhantomData,";
"          m))";
"    },";
"    &Nat::S(_, p) => {";
"      let ackn = {";
"        let ackn = self.alloc(std::cell::Cell::new(None));";
"        ackn.set(Some(";
"          self.closure(move |m2| {";
"            match m2 {";
"              &Nat::O(_) => {";
"                self.ack(";
"                  p,";
"                  self.alloc(";
"                    Nat::S(";
"                      PhantomData,";
"                      self.alloc(";
"                        Nat::O(";
"                          PhantomData)))))";
"              },";
"              &Nat::S(_, q) => {";
"                self.ack(";
"                  p,";
"                  hint_app(ackn.get().unwrap())(q))";
"              },";
"            }";
"          })));";
"        ackn.get().unwrap()";
"      };";
"      hint_app(ackn)(m)";
"    },";
"  }";
"}";
"fn ack__curried(&'a self) -> &'a dyn Fn(&'a Nat<'a>) -> &'a dyn Fn(&'a Nat<'a>) -> &'a Nat<'a> {";
"  self.closure(move |n| {";
"    self.closure(move |m| {";
"      self.ack(";
"        n,";
"        m)";
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
"#[derive(Debug, Clone)]";
"pub enum Nat<'a> {";
"  O(PhantomData<&'a ()>),";
"  S(PhantomData<&'a ()>, &'a Nat<'a>)";
"}";
"";
"#[derive(Debug, Clone)]";
"pub enum T<'a> {";
"  F1(PhantomData<&'a ()>, &'a Nat<'a>),";
"  FS(PhantomData<&'a ()>, &'a Nat<'a>, &'a T<'a>)";
"}";
"";
"#[derive(Debug, Clone)]";
"pub enum Eq<'a, A> {";
"  eq_refl(PhantomData<&'a A>)";
"}";
"";
"fn code(&'a self, f: &'a T<'a>) -> &'a T<'a> {";
"  f";
"}";
"fn code__curried(&'a self) -> &'a dyn Fn(&'a T<'a>) -> &'a T<'a> {";
"  self.closure(move |f| {";
"    self.code(";
"      f)";
"  })";
"}" $>.
  Proof. vm_compute. reflexivity. Qed.
End ex5.

Module SafeHead.

  Program Definition safe_head {A} (non_empty_list : {l : list A | length l > 0}) : A :=
    match non_empty_list as l' return l' = non_empty_list -> A  with
    | [] =>
      (* NOTE: we use [False_rect] to make the extracted code a bit nicer.
         It's totally possible to leave the whole branch as an obligation,
         the extraction will handle it.
         However, if the whole branch is an abligation, the proof it should
         be left transparent (using [Defined]), so the extraction could
         produce reasonable code for it. If left opaque, it the body of
         the obligation will be ignored by extraction producing no
         corresponding definiton*)
      fun _ => False_rect _ _
    | hd :: tl => fun _ => hd
    end eq_refl.
  Next Obligation.
    cbn in *;subst.
    match goal with
    | H : 0 > 0 |- _ => inversion H
    end.
  Qed.

  Program Definition head_of_repeat_plus_one {A} (n : nat) (a : A) : A
    := safe_head (repeat a (S n)).
  Next Obligation.
    intros. cbn. lia.
  Qed.

  MetaCoq Run (p <- Core.tmQuoteRecTransp (@head_of_repeat_plus_one) false;;
               Core.tmDefinition "Prog" p).

  Compute extract Prog.

  Example test : extract Prog = Ok <$
"#[derive(Debug, Clone)]";
"pub enum Nat<'a> {";
"  O(PhantomData<&'a ()>),";
"  S(PhantomData<&'a ()>, &'a Nat<'a>)";
"}";
"";
"#[derive(Debug, Clone)]";
"pub enum Sig<'a, A> {";
"  exist(PhantomData<&'a A>, A)";
"}";
"";
"#[derive(Debug, Clone)]";
"pub enum List<'a, A> {";
"  nil(PhantomData<&'a A>),";
"  cons(PhantomData<&'a A>, A, &'a List<'a, A>)";
"}";
"";
"fn proj1_sig<A: Copy>(&'a self, e: &'a Sig<'a, A>) -> A {";
"  match e {";
"    &Sig::exist(_, a) => {";
"      a";
"    },";
"  }";
"}";
"fn proj1_sig__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a Sig<'a, A>) -> A {";
"  self.closure(move |e| {";
"    self.proj1_sig(";
"      e)";
"  })";
"}";
"";
"fn False_rect<P: Copy>(&'a self, P: ()) -> P {";
"  panic!(""Absurd case!"")";
"}";
"fn False_rect__curried<P: Copy>(&'a self) -> &'a dyn Fn(()) -> P {";
"  self.closure(move |P| {";
"    self.False_rect(";
"      P)";
"  })";
"}";
"";
"fn safe_head<A: Copy>(&'a self, non_empty_list: &'a Sig<'a, &'a List<'a, A>>) -> A {";
"  hint_app(match self.proj1_sig(";
"                   non_empty_list) {";
"             &List::nil(_) => {";
"               self.closure(move |x| {";
"                 self.False_rect(";
"                   ())";
"               })";
"             },";
"             &List::cons(_, hd, tl) => {";
"               self.closure(move |x| {";
"                 hd";
"               })";
"             },";
"           })(())";
"}";
"fn safe_head__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a Sig<'a, &'a List<'a, A>>) -> A {";
"  self.closure(move |non_empty_list| {";
"    self.safe_head(";
"      non_empty_list)";
"  })";
"}";
"";
"fn repeat<A: Copy>(&'a self, x: A, n: &'a Nat<'a>) -> &'a List<'a, A> {";
"  match n {";
"    &Nat::O(_) => {";
"      self.alloc(";
"        List::nil(";
"          PhantomData))";
"    },";
"    &Nat::S(_, k) => {";
"      self.alloc(";
"        List::cons(";
"          PhantomData,";
"          x,";
"          self.repeat(";
"            x,";
"            k)))";
"    },";
"  }";
"}";
"fn repeat__curried<A: Copy>(&'a self) -> &'a dyn Fn(A) -> &'a dyn Fn(&'a Nat<'a>) -> &'a List<'a, A> {";
"  self.closure(move |x| {";
"    self.closure(move |n| {";
"      self.repeat(";
"        x,";
"        n)";
"    })";
"  })";
"}";
"";
"fn head_of_repeat_plus_one<A: Copy>(&'a self, n: &'a Nat<'a>, a: A) -> A {";
"  self.safe_head(";
"    self.alloc(";
"      Sig::exist(";
"        PhantomData,";
"        self.repeat(";
"          a,";
"          self.alloc(";
"            Nat::S(";
"              PhantomData,";
"              n))))))";
"}";
"fn head_of_repeat_plus_one__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a Nat<'a>) -> &'a dyn Fn(A) -> A {";
"  self.closure(move |n| {";
"    self.closure(move |a| {";
"      self.head_of_repeat_plus_one(";
"        n,";
"        a)";
"    })";
"  })";
"}" $>.
  Proof. vm_compute. reflexivity. Qed.

End SafeHead.
