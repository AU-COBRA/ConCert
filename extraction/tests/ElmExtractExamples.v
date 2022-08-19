(** * Examples for extraction to Elm *)

(** The examples are writen into files that are later processed and passed to the Elm compiler as part of the building process. *)

(** Warning: this file does not work in the interactive mode due to the problems with paths for [Redirect].
    We have to stick to the path, relative to the project root and in the interactive mode current directory is different. *)
From ConCert.Utils Require Import StringExtra.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import ElmExtract.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import CertifyingEta.
From ConCert.Extraction.Tests Require Import ElmExtractTests.
From ConCert.Extraction.Tests Require Import Ack.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq Require Import utils.
From Coq Require Import String.

Import MCMonadNotation.
Local Open Scope string.

Instance ElmBoxes : ElmPrintConfig :=
  {| term_box_symbol := "()"; (* the inhabitant of the unit type *)
     type_box_symbol := "()"; (* unit type *)
     any_type_symbol := "()"; (* unit type *)
     false_elim_def := "false_rec ()"; (* predefined function *)
     print_full_names := false (* short names for readability *)|}.

Definition result_err_bytestring A := result A bytestring.String.t.

Definition general_wrapped (p : program) (pre post : string)
  (ignore: list kername) (TT : list (kername * string)) : result_err_bytestring _ :=
  entry <- match p.2 with
           | tConst kn _ => ret kn
           | _ => Err (s_to_bs "Expected program to be a tConst")
           end;;
  Σ <- extract_template_env_within_coq
         p.1
         (KernameSet.singleton entry)
         (fun k => existsb (eq_kername k) ignore);;
  let TT_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') TT) in
  '(_, s) <- map_error (fun x => s_to_bs x) (finish_print (print_env Σ TT_fun));;
  ret (pre ++ Common.nl ++ s ++ Common.nl ++ post).

Definition wrapped (p : program) (pre post : string) : result _ _ :=
  general_wrapped p pre post [] [].

Module ElmExamples.

  Import Lia.

  Definition Preambule mod_name :=
    concat Common.nl
           ["module " ++ mod_name ++ " exposing (..)";
            "import Test";
            "import Html";
            "import Expect exposing (Expectation)"].

  Definition main_and_test (test : string) :=
    ("main = Html.text "++ Common.parens false ("Debug.toString " ++ Common.parens false test) ++ Common.nl ++
    "suite = Test.test (Debug.toString 1)" ++ Common.parens false ("\ _ -> " ++ test))%string.

  (* [safe_pred] example is inspired by Letozey's A New Extraction for Coq *)
  Definition safe_pred (n:nat) (not_zero : O<>n) : {p :nat | n=(S p)} :=
    match n as n0 return (n0 = n -> _ -> _ )with
    | O => fun heq h => False_rect _ (ltac:(cbn;intros;easy))
    | S m => fun heq h => exist m eq_refl
    end eq_refl not_zero.

  Program Definition safe_pred_full := safe_pred 1 (ltac:(easy)).
  Program Definition safe_pred_partial := safe_pred 1.

  MetaCoq Run (t <- tmQuoteRecTransp safe_pred_full false ;;
               tmDefinition (s_to_bs "safe_pred_full_syn") t).

  (* In fully applied case the last argument of [safe_pred] is removed*)
  Redirect "tests/extracted-code/elm-extract/SafePredFull.elm"
  Compute general_wrapped safe_pred_full_syn
  (Preambule "SafePredFull" ++ Common.nl ++ elm_false_rec)
  (main_and_test "Expect.equal safe_pred_full (Exist O)")
  [] [].

  MetaCoq Run (t <- tmQuoteRecTransp safe_pred_partial false ;;
               mpath <- tmCurrentModPath tt;;
               Σeta <- run_transforms_list t.1
                 [template_eta (fun _ => None) true true [<%% @safe_pred_partial %%>] (fun _ => false)] ;;

               Certifying.gen_defs_and_proofs (declarations t.1) (declarations Σeta) mpath (s_to_bs "_cert_pass")
                                              (KernameSet.singleton <%% @safe_pred_partial %%> )).

  MetaCoq Run (t <- tmQuoteRecTransp ConCert_Extraction_Tests_ElmExtractExamples_ElmExamples_safe_pred_partial_cert_pass false;;
               tmDefinition (s_to_bs "safe_pred_partial_syn") t).

  (* After eta-expansion the main [safe_pred_partial] is guarded by a lambda *)

  Redirect "tests/extracted-code/elm-extract/SafePredPartial.elm"
  Compute general_wrapped safe_pred_partial_syn
          (Preambule "SafePredPartial" ++ Common.nl ++ elm_false_rec)
          (main_and_test "Expect.equal (conCert_Extraction_Tests_ElmExtractExamples_ElmExamples_safe_pred_partial_cert_pass ()) (Exist O)")
          [] [].


  MetaCoq Quote Recursively Definition rev_syn := List.rev.

  Definition ackermann := Eval compute in ack.

  MetaCoq Run (t <- tmQuoteRecTransp ackermann false ;;
               tmDefinition (s_to_bs "ackermann_syn") t).

  Redirect "tests/extracted-code/elm-extract/Ackermann.elm"
  Compute wrapped ackermann_syn
          (Preambule "Ackermann")
          (main_and_test "Expect.equal (ackermann (Pair (S (S (S O))) (S (S (S O))))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))").

  Redirect "tests/extracted-code/elm-extract/Rev.elm"
           Compute wrapped rev_syn
           (Preambule "Rev")
           (main_and_test "Expect.equal (rev (Cons 3 (Cons 2 (Cons 1 (Cons 0 Nil))))) (Cons 0 (Cons 1 (Cons 2 (Cons 3 Nil))))").


  MetaCoq Quote Recursively Definition nth_syn := List.nth.

  Definition result_nth :=
    <$ "type Nat";
       "  = O";
       "  | S Nat";
       "";
       "type List a";
       "  = Nil";
       "  | Cons a (List a)";
       "";
       "nth : Nat -> List a -> a -> a";
       "nth n l default =";
       "  case n of";
       "    O ->";
       "      case l of";
       "        Nil ->";
       "          default";
       "        Cons x l2 ->";
       "          x";
       "    S m ->";
       "      case l of";
       "        Nil ->";
       "          default";
       "        Cons x t ->";
       "          nth m t default" $>.

  Example ElmExamples_nth :
    extract nth_syn = Ok result_nth.
  Proof. vm_compute. reflexivity. Qed.

  Redirect "tests/extracted-code/elm-extract/Nth.elm"
  Compute wrapped nth_syn
  (Preambule "Nth")
  (main_and_test "Expect.equal (nth O (Cons 1 (Cons 0 Nil)) 0) 1").

  MetaCoq Quote Recursively Definition map_syn := List.map.
  Definition result_map :=
    <$ "type List a";
       "  = Nil";
       "  | Cons a (List a)";
         "";
       "map : (a -> b) -> List a -> List b";
       "map f =";
       "  let";
       "    map2 l =";
       "      case l of";
       "        Nil ->";
       "          Nil";
       "        Cons a t ->";
       "          Cons (f a) (map2 t)";
       "  in";
       "  map2" $>.

  Redirect "tests/extracted-code/elm-extract/Map.elm"
  Compute wrapped map_syn
  (Preambule "Map")
  (main_and_test "Expect.equal (map (\x->x+1) (Cons 1 (Cons 0 Nil))) (Cons 2 (Cons 1 Nil))").

  Example ElmList_map :
    extract map_syn = Ok result_map.
  Proof. reflexivity. Qed.

  MetaCoq Quote Recursively Definition foldl_syn := List.fold_left.
  Definition result_foldl :=
  <$ "type List a";
      "  = Nil";
      "  | Cons a (List a)";
        "";
      "fold_left : (a -> b -> a) -> List b -> a -> a";
      "fold_left f =";
        "  let";
      "    fold_left2 l a0 =";
      "      case l of";
      "        Nil ->";
      "          a0";
      "        Cons b t ->";
      "          fold_left2 t (f a0 b)";
      "  in";
      "  fold_left2" $>.

  Redirect "tests/extracted-code/elm-extract/Fold.elm"
  Compute wrapped foldl_syn
  (Preambule "Fold")
  (main_and_test "(Expect.equal (fold_left (+) (Cons 1 (Cons 0 Nil)) 0)) 1").

  Example ElmList_foldl :
    extract foldl_syn = Ok result_foldl.
  Proof. reflexivity. Qed.

  Local Open Scope nat.
  Program Definition inc_counter (st : nat) (inc : {z : nat | 0 <? z}) :
    {new_st : nat | st <? new_st} :=
    st + inc.
  Next Obligation.
    unfold is_true in *.
    rewrite Nat.ltb_lt in *. lia.
  Qed.

  MetaCoq Run (t <- tmQuoteRecTransp inc_counter false ;;
               tmDefinition (s_to_bs "inc_counter_syn") t).

  Redirect "tests/extracted-code/elm-extract/Increment.elm"
  Compute wrapped inc_counter_syn
         (Preambule "Increment")
         (main_and_test "Expect.equal (inc_counter O (Exist (S O))) (Exist (S O))").

  MetaCoq Quote Recursively Definition last_syn := List.last.

  Redirect "tests/extracted-code/elm-extract/Last.elm"
  Compute wrapped last_syn
  (Preambule "Last")
  (main_and_test "Expect.equal (last (Cons 1 (Cons 10 Nil)) 0) 10").

  Program Definition safe_head {A} (non_empty_list : {l : list A | List.length l > 0}) : A :=
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
    intros;cbn in*; lia.
  Qed.

  Program Definition head_of_repeat_plus_one {A} (n : nat) (a : A) : A
    := safe_head (repeat a (1+n)).
  Next Obligation.
    intros. cbn. lia.
  Qed.

  MetaCoq Run (t <- tmQuoteRecTransp (@head_of_repeat_plus_one) false ;;
               tmDefinition (s_to_bs "head_of_repeat_plus_one_syn") t).

  Redirect "tests/extracted-code/elm-extract/SafeHead.elm"
  Compute general_wrapped head_of_repeat_plus_one_syn
  (Preambule "SafeHead" ++ Common.nl ++ elm_false_rec)
  (main_and_test "Expect.equal (head_of_repeat_plus_one (S O) 1) 1")
  [] [].

End ElmExamples.
