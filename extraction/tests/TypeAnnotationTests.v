From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import Annotations.
From ConCert.Extraction Require Import ErasureTests.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import TypeAnnotations.
From MetaCoq.Template Require Import Kernames.

Module P := PCUICAst.
Module T := Ast.

Section printing.
  Context (Σ : P.global_env).
  Definition print_box_type := erase_type_tests.print_box_type Σ [].

  Definition print_name (na : name) : string :=
    match na with
    | nAnon => "_"
    | nNamed id => id
    end.

  Definition print_ind_ctor (ind : inductive) (c : nat) : string :=
    match P.lookup_env Σ (inductive_mind ind) with
    | Some (P.InductiveDecl mib) =>
      match nth_error (P.ind_bodies mib) (inductive_ind ind) with
      | Some oib =>
        match nth_error (P.ind_ctors oib) c with
        | Some ((id, _), _) => id
        | None => "<ctor not found>"
        end
      | None => "<OIB not found>"
      end
    | _ => "<MIB not found>"
    end.

  Fixpoint print_term_annotated
           (Γ : list name)
           (t : term) : annots box_type t -> string :=
    match t with
    | tBox => fun bt => "□ : " ^ print_box_type bt
    | tRel i => fun bt => print_name (nth i Γ nAnon) ^ " : " ^ print_box_type bt
    | tLambda na body =>
      fun '(bt, a) =>
        "(" ^ print_name na ^ " -> (" ^ print_term_annotated (na :: Γ) body a ^ ")) : "
        ^ print_box_type bt
    | tLetIn na val body =>
      fun '(bt, (vala, bodya)) =>
        "(let " ^ print_name na ^ " := (" ^ print_term_annotated Γ val vala ^ ") in" ^ nl
        ^ print_term_annotated (na :: Γ) body bodya ^ ") : " ^ print_box_type bt
    | tApp hd arg =>
      fun '(bt, (hda, arga)) =>
        "(" ^ print_term_annotated Γ hd hda ^ ") "
        ^ "(" ^ print_term_annotated Γ arg arga ^ ") : " ^ print_box_type bt
    | tConst s => fun bt => s.2 ^ " : "  ^ print_box_type bt
    | tConstruct ind c =>
      fun bt =>
        print_ind_ctor ind c ^ " : " ^ print_box_type bt
    | _ => fun _ => "error: cannot print"
    end.
End printing.

Definition opt_args :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform (fun _ => None) true true false false false] |} |}.

Definition no_opt_args :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := false;
          extract_transforms := [] |} |}.

Axiom does_not_happen : forall {A}, A.

Definition general_extract_typed (p : T.program) (opt : bool) (ignore : list kername) (TT : list (kername * string)) : string.
Proof.
  refine (let entry := match p.2 with
           | T.tConst kn _ => kn
           | T.tInd ind _ => (inductive_mind ind)
           | _ => does_not_happen
           end in _).
  set (args := if opt then opt_args else no_opt_args).
  unshelve epose proof (annot_extract_template_env args p.1 (KernameSet.singleton entry)
                                                   (fun k => existsb (eq_kername k) ignore) _).
  { destruct opt; cbn.
    - constructor; [|constructor].
      apply annot_dearg_transform.
    - constructor. }
  destruct extract_template_env as [|e]; [|exact does_not_happen].
  destruct (bigprod_find (fun '(kn, _, _) _ => eq_kername entry kn) X); [|exact does_not_happen].
  destruct s as ((? & decl) & annot).
  destruct decl; [|exact does_not_happen|exact does_not_happen].
  cbn in *.
  unfold constant_body_annots in *.
  destruct Ex.cst_body; [|exact does_not_happen].
  exact (print_term_annotated (TemplateToPCUIC.trans_global_decls p.1) [] t0 annot).
Defined.

Definition extract_opt p := general_extract_typed p true [] [].
Definition extract_no_opt p := general_extract_typed p false [] [].

Module ex1.
  Definition foo := 1.
  MetaCoq Quote Recursively Definition ex := foo.
  Example test :
    extract_opt ex = "(S : nat → nat) (O : nat) : nat".
  Proof. vm_compute. reflexivity. Qed.
End ex1.

Module ex2.
  Definition foo : { n : nat | n = 0 } := exist 0 eq_refl.
  Definition bar := proj1_sig foo.
  MetaCoq Quote Recursively Definition ex := bar.

  Example test_no_opt :
    extract_no_opt ex =
    "(((proj1_sig : □ → □ → sig 𝕋 □ → 𝕋) (□ : □) : □ → sig nat □ → nat) (□ : □) : sig nat □ → nat) (foo : sig nat □) : nat".
  Proof. vm_compute. reflexivity. Qed.

  Example test_opt :
    extract_opt ex = "(proj1_sig : sig nat → nat) (foo : sig nat) : nat".
  Proof. vm_compute. reflexivity. Qed.
End ex2.

Module ex3.
  Definition foo (f : 5 = 5 -> nat -> nat) := f eq_refl 0.
  Definition bar (p : 5 = 5) (n : nat) := n.
  (* bar must be eta expanded in the following *)
  Definition baz := foo bar.
  MetaCoq Quote Recursively Definition ex := baz.

  Example test_no_opt :
    extract_no_opt ex = "(foo : (□ → nat → nat) → nat) (bar : □ → nat → nat) : nat".
  Proof. vm_compute. reflexivity. Qed.

  Example test_opt :
    extract_opt ex =
    "(foo : (□ → nat → nat) → nat) ((_ -> (bar : nat → nat)) : □ → nat → nat) : nat".
  Proof. vm_compute. reflexivity. Qed.
End ex3.

Module ex4.
  Definition foo : option nat := None.
  MetaCoq Quote Recursively Definition ex := foo.

  Example test_no_opt :
    extract_no_opt ex = "(None : □ → option 𝕋) (□ : □) : option nat".
  Proof. vm_compute. reflexivity. Qed.

  Example test_opt :
    extract_opt ex = "None : option nat".
  Proof. vm_compute. reflexivity. Qed.
End ex4.

Module ex5.
  Definition foo : list nat := [0].
  MetaCoq Quote Recursively Definition ex := foo.

  Example test_no_opt :
    extract_no_opt ex = "(((cons : □ → 𝕋 → list 𝕋 → list 𝕋) (□ : □) : nat → list nat → list nat) (O : nat) : list nat → list nat) ((nil : □ → list 𝕋) (□ : □) : list nat) : list nat".
  Proof. vm_compute. reflexivity. Qed.

  Example test_opt :
    extract_opt ex = "((cons : nat → list nat → list nat) (O : nat) : list nat → list nat) (nil : list nat) : list nat".
  Proof. vm_compute. reflexivity. Qed.
End ex5.
