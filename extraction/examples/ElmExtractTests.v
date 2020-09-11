(** * Tests for extraction to Elm *)
(** Uses the same pretty-printer as Midlang, since Midlang is a fork of Elm.
    The examples are writen into files which are later processed and passed to the Elm compiler as part of the building process. *)

(** Warning: this file does not work in the interactive mode due to the problems with paths for [Redirect]. We have to stick to the path, relative to the project root and in the interactive mode current directory is different. *)
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import MidlangExtract.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import StringExtra.
From ConCert.Extraction.Examples Require Import MidlangExtractTests.
From ConCert.Extraction.Examples Require Import Ack.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Arith.
From Coq Require Import Lia.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq Require Import monad_utils.
From MetaCoq Require Import utils.

Import MonadNotation.

Instance ElmBoxes : BoxSymbol :=
  {| term_box_symbol := "()"; (* the inhabitant of the unit type *)
     type_box_symbol := "()"; (* unit type *)
     any_type_symbol := "()"(* unit type *) |}.


Definition general_wrapped (p : program) (pre post : string)
  (ignore: list kername) (TT : list (kername * string)) : result string string :=
  entry <- match p.2 with
           | tConst kn _ => ret kn
           | _ => Err "Expected program to be a tConst"
           end;;
  Σ <- specialize_erase_debox_template_env_no_wf_check p.1 [entry] ignore;;
  let TT_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') TT) in
  '(_, s) <- finish_print (print_env Σ p.1 TT_fun);;
  ret (pre ++ nl ++ s ++ nl ++ post).

Definition wrapped (p : program) (pre post : string) : result string string :=
  general_wrapped p pre post [] [].

Module ElmExamples.

  Import Lia.

  Definition Preambule mod_name :=
    String.concat nl
                  ["module " ++ mod_name ++ " exposing (..)";
                  "import Test";
                  "import Html";
                  "import Expect exposing (Expectation)"].

  Definition elm_false_rec :=
    String.concat nl
                  ["false_rec : () -> a";
                   "false_rec _ = false_rec ()"].

  Definition main_and_test (test : string) :=
    "main = Html.text "++ parens false ("Debug.toString " ++ parens false test) ++ nl ++
    "suite = Test.test (Debug.toString 1)" ++ parens false ("\ _ -> " ++ test).

  MetaCoq Quote Recursively Definition rev_syn := List.rev.

  Definition ackermann := Eval compute in ack.

  MetaCoq Run (t <- tmQuoteRecTransp ackermann false ;;
               tmDefinition "ackermann_syn" t).

  Redirect "./extraction/examples/elm-extract/Ackermann.elm"
  Compute wrapped ackermann_syn
          (Preambule "Ackermann")
          (main_and_test "Expect.equal (ackermann (Pair (S (S (S O))) (S (S (S O))))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))").

  Redirect "./extraction/examples/elm-extract/Rev.elm"
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
  Proof. reflexivity. Qed.

  Redirect "./extraction/examples/elm-extract/Nth.elm" Compute wrapped nth_syn
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

  Redirect "./extraction/examples/elm-extract/Map.elm" Compute wrapped map_syn
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

  Redirect "./extraction/examples/elm-extract/Fold.elm" Compute wrapped foldl_syn
         (Preambule "Fold")
         (main_and_test "(Expect.equal (fold_left (+) (Cons 1 (Cons 0 Nil)) 0)) 1").

  Example ElmList_foldl :
    extract foldl_syn = Ok result_foldl.
  Proof. reflexivity. Qed.

  Program Definition inc_counter (st : nat) (inc : {z : nat | 0 <? z}) :
    {new_st : nat | st <? new_st} :=
    st + inc.
  Next Obligation.
    intros ? inc0. unfold is_true in *.
    destruct inc0;simpl.
    rewrite NPeano.Nat.ltb_lt in *. lia.
  Qed.

  MetaCoq Run (t <- tmQuoteRecTransp inc_counter false ;;
               tmDefinition "inc_counter_syn" t).

  Redirect "./extraction/examples/elm-extract/Increment.elm"
  Compute wrapped inc_counter_syn
         (Preambule "Increment")
         (main_and_test "Expect.equal (inc_counter O (Exist (S O))) (Exist (S O))").


  MetaCoq Quote Recursively Definition last_syn := List.last.

  Redirect "./extraction/examples/elm-extract/Last.elm" Compute wrapped last_syn
          (Preambule "Last")
          (main_and_test "Expect.equal (last (Cons 1 (Cons 10 Nil)) 0) 10").


  Lemma O_gt_False : 0 > 0 -> False.
  Proof. intros H;inversion H. Qed.

  Program Definition safe_head {A} (non_empty_list : {l : list A | length l > 0}) : A :=
    match non_empty_list as l' return l' = non_empty_list -> A  with
    | [] => fun _ => False_rect _ _
    | hd :: tl => fun _ => hd
    end eq_refl.
  Next Obligation.
    intros. destruct non_empty_list as [l H1]. cbn in *;subst.
    apply O_gt_False;auto.
  Qed.

  Program Definition head_of_repeat_2 {A} (a : A) := safe_head (repeat a 2).
  Next Obligation.
    intros. cbn. auto.
  Qed.

  MetaCoq Run (t <- tmQuoteRecTransp (@head_of_repeat_2) false ;;
               tmDefinition "head_of_repeat_2_syn" t).

  Redirect "./extraction/examples/elm-extract/SafeHead.elm"
           Compute general_wrapped head_of_repeat_2_syn
          (Preambule "SafeHead" ++ nl ++ elm_false_rec)
          (main_and_test "Expect.equal (head_of_repeat_2 1) 1")
          [<%% False_rect %%>] [(<%% False_rect %%>, "false_rec ()")].

End ElmExamples.
