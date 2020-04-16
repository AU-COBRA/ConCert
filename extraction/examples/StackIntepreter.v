From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Extraction Require Import LPretty Certified.
From ConCert.Extraction Require Import Counter.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.
From Equations Require Import Equations.

Import ListNotations.
Import MonadNotation.

Module Interpreter.

  Inductive op : Set := Add | And | Equal.

  Inductive instruction :=
  | IPushZ : Z -> instruction
  | IPushB : bool -> instruction
  | IOp : op -> instruction.

  Inductive value : Set := BVal : bool -> value | ZVal : Z -> value.

  Definition storage := list value.

  Fixpoint interp (insts : list instruction) (s : list value) :=
    match insts with
    | [] => Some s
    | hd :: inst' =>
      match hd with
      | IPushZ i => interp inst' (ZVal i :: s)
      | IPushB b => interp inst' (BVal b :: s)
      | IOp op => match op with
                   | Add => match s with
                            | ZVal i :: ZVal j :: s' => interp inst' (ZVal (i+j) :: s')%Z
                            | _ => None
                            end
                   | And => match s with
                            | BVal i :: BVal j :: s' => interp inst' (BVal (i && j) :: s')%Z
                            | _ => None
                           end
                   | Equal => match s with
                            | ZVal i :: ZVal j :: s' => interp inst' (BVal (i =? j) :: s')%Z
                            | _ => None
                             end
                 end
      end
    end.

Fail Program Fixpoint interp' (insts_s : list inst * list Z) : option (list Z) :=
  match insts_s with
  | ([],s) => Some s
  | (hd :: inst', s) =>
      match hd with
      | PushZ i => interp' (inst', (i :: s))
      | AddOne => match s with
                 | i :: s' => interp' (inst', (i+1 :: s'))%Z
                 | _ => None
                 end
      end
  end.


Definition main :=
       "let%entry main (prog : instruction list) s ="
    ++ nl
    ++ "let s = interp (prog,[]) in"
    ++ nl
    ++ "match s with"
    ++ nl
    ++ "| Some res -> ( [], res ) "
    ++ nl
    ++ "| _ -> Current.failwith s".

End Interpreter.

Import Interpreter.

(** A translation table for various constants we want to rename *)
Definition TT : env string :=
  [  remap <% Z.add %> "addInt"
     ; remap <% Z.eqb %> "eqInt"
     ; remap <% Z %> "int"
     ; remap <% nat %> "address"
     ; ("Zpos" ,"")
     ; ("xH" ,"1")
     ; ("nil", "[]")
     ; local <% @fst %>
     ; local <% @snd %>
     ; local <% value %>
     ; local <% op %>
     ; local <% bool %>
     ; local <% list %>
     ; local <% andb %>
  ].

Time Run TemplateProgram
    (storage_def <- tmQuoteConstant "storage" false ;;
     storage_body <- opt_to_template storage_def.(cst_body) ;;
     ind1 <- tmQuoteInductive "op" ;;
     ind_liq1 <- get_one_ind_body TT ind1.(ind_bodies);;
     ind2 <- tmQuoteInductive "instruction" ;;
     ind_liq2 <- get_one_ind_body TT ind2.(ind_bodies);;
     ind3 <- tmQuoteInductive "value" ;;
     ind_liq3 <- get_one_ind_body TT ind3.(ind_bodies);;
     t1 <- toLiquidity TT interp ;;
     res <- tmEval lazy
                  (prod_ops ++ nl ++ int_ops ++ nl ++ bool_ops
                     ++ nl ++ nl
                     ++ ind_liq1
                     ++ nl ++ nl
                     ++ ind_liq2
                     ++ nl ++ nl
                     ++ ind_liq3
                     ++ nl ++ nl
                     ++ "type storage = " ++ print_liq_type TT storage_body
                     ++ nl ++ nl
                     ++ "let%init storage = []"
                     ++ nl ++ nl
                     ++ t1
                     ++ nl ++ nl
                     ++ main) ;;
    tmDefinition "interp_extracted" res).

Print interp_extracted.
