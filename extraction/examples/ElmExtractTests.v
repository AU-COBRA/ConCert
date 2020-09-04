(** * Tests for extraction to Elm *)
(** Uses the same pretty-printer as Midlang, since Midlang is a fork of Elm.
    The examples are writen into files which are later processed and passed to the Elm compiler as part of the building process. *)

(** Warning: this file does not work in the interactive mode due to the problems with paths for [Redirect]. We have to stick to the path, relative to the project root and in the interactive mode current directory is different. *)
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import MidlangExtract.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import MidlangExtractTests.
From Coq Require Import Arith.
From Coq Require Import String.
From Coq Require Import String Ascii.
From Coq Require Import List.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq Require Import monad_utils.
From MetaCoq Require Import utils.

Import MonadNotation.

Definition wrapped (p : program) (pre post : string) : result string string :=
  entry <- match p.2 with
           | tConst kn _ => ret kn
           | _ => Err "Expected program to be a tConst"
           end;;
  Σ <- specialize_erase_debox_template_env p.1 [entry] [];;
  '(_, s) <- finish_print (print_env Σ p.1 (fun _ => None));;
  ret (pre ++ nl ++ s ++ nl ++ post).

Module ElmExamples.
  Definition Preambule mod_name :=
    String.concat nl
                  ["module " ++ mod_name ++ " exposing (..)";
                  "import Test";
                  "import Html";
                  "import Expect exposing (Expectation)"].

  Definition main_and_test (test : string) :=
    "main = Html.text "++ parens false ("Debug.toString " ++ parens false test) ++ nl ++
    "suite = Test.test (Debug.toString 1)" ++ parens false ("\ _ -> " ++ test).

  MetaCoq Quote Recursively Definition map_syn := List.map.
  Definition result_map :=
    String.concat nl
      ["type List a";
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
      "  map2"].


  Redirect "./extraction/examples/elm-extract/Map.elm" Compute wrapped map_syn
          (Preambule "Map")
          (main_and_test "Expect.equal (map (\x->x+1) (Cons 1 (Cons 0 Nil))) (Cons 2 (Cons 1 Nil))").

  Example ElmList_map :
    extract map_syn = Ok result_map.
  Proof. reflexivity. Qed.

  MetaCoq Quote Recursively Definition foldl_syn := List.fold_left.
  Definition result_foldl :=
    String.concat nl
      ["type List a";
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
      "  fold_left2"].

  Redirect "./extraction/examples/elm-extract/Fold.elm" Compute wrapped foldl_syn
         (Preambule "Fold")
         (main_and_test "(Expect.equal (fold_left (+) (Cons 1 (Cons 0 Nil)) 0)) 1").

  Example ElmList_foldl :
    extract foldl_syn = Ok result_foldl.
  Proof. reflexivity. Qed.

  Import Lia.

  Program Definition inc_counter (st : nat) (inc : {z : nat | 0 <? z}) :
    {new_st : nat | st <? new_st} :=
    st + inc.
  Next Obligation.
    intros st inc. unfold is_true in *.
    destruct inc;simpl.
    rewrite NPeano.Nat.ltb_lt in *. lia.
  Qed.

  MetaCoq Run (t <- tmQuoteRecTransp inc_counter false ;;
               tmDefinition "inc_counter_syn" t).

  Redirect "./extraction/examples/elm-extract/Increment.elm"
  Compute wrapped inc_counter_syn
         (Preambule "Increment")
         (main_and_test "Expect.equal (inc_counter O (Exist (S O))) (Exist (S O))").


End ElmExamples.
