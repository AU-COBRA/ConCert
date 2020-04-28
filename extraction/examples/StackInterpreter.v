From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader SafeTemplateErasure.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Extraction Require Import LPretty Certified.
From ConCert.Extraction Require Import Counter.
From ConCert.Execution Require Import Containers.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

(** Quoting this runs forever, because of many dependencies *)
Definition my_lookup (m : FMap string Z) (k : string) := FMap.find k m.
(* Quote Recursively Definition zz := (my_lookup). *)

(** To overcome the dependency issue, we parameterise the development with a module of the following type *)
Module Type FiniteMap.
  Parameter FM : Type -> Type.
  Parameter lookup : forall {V}, (string * Z) -> FM V -> option V.
End FiniteMap.

Module Interpreter (FinMap : FiniteMap).

  Inductive op : Set := Add | And | Equal.

  Inductive instruction :=
  | IPushZ : Z -> instruction
  | IPushB : bool -> instruction
  | IObs : string -> Z -> instruction
  | IOp : op -> instruction.

  Inductive value : Set := BVal : bool -> value | ZVal : Z -> value.

  Definition ext_map := FinMap.FM value.

  Definition storage := list value.

  Definition obs0 s := IObs s 0.

  Definition key_eq (k1 : string * Z) (k2 : string * Z)
    := (k1.1 =? k2.1) && (k1.2 =? k2.2)%Z.

  Fixpoint interp (ext : ext_map) (insts : list instruction) (s : list value) :=
    match insts with
    | [] => Some s
    | hd :: inst' =>
      match hd with
      | IPushZ i => interp ext inst' (ZVal i :: s)
      | IPushB b => interp ext inst' (BVal b :: s)
      | IObs l i => match FinMap.lookup (l,i) ext with
                   | Some v => Some (v :: s)
                   | None => None
                   end
      | IOp Add => match s with
                   | ZVal i :: ZVal j :: s' => interp ext inst' (ZVal (i+j) :: s')%Z
                   | _ => None
                   end
      | IOp And => match s with
                   | BVal i :: BVal j :: s' => interp ext inst' (BVal (i && j) :: s')%Z
                   | _ => None
                   end
      | IOp Equal => match s with
                     | ZVal i :: ZVal j :: s' => interp ext inst' (BVal (i =? j) :: s')%Z
                     | _ => None
                     end
      end
    end.

(** A wrapper for calling the main functionality. It is important to be explicit about types for all the parameters of entry points *)
Definition main (param_type : string):=
       "let%entry main (prog : " ++ param_type ++ ")" ++ " s ="
    ++ nl
    ++ "let s = interp (prog.(1), prog.(0) ,[]) in"
    ++ nl
    ++ "match s with"
    ++ nl
    ++ "| Some res -> ( [], res ) "
    ++ nl
    ++ "| _ -> Current.failwith s".

End Interpreter.

(** Now, we create a module of  [FiniteMap] type using the [FMap] functionality *)
Module MyFinMap : FiniteMap.
  Definition FM := FMap (string * Z).
  Definition lookup {V} : (string * Z) -> FM V -> option V :=
    FMap.find.
End MyFinMap.

Module Interp := Interpreter MyFinMap.

Import Interp.

(** A translation table for various constants we want to rename *)
Definition TT : env string :=
  [   (* remapping types *)
       remap <% Z %> "int"
     ; remap <% bool %> "bool"
     ; remap <% nat %> "address"
     ; remap <% list %> "list"
     ; remap <% string %> "string"
     ; remap <% ext_map %> "((string*int),value) map"

     (* remapping operations *)
     ; remap <% Z.add %> "addInt"
     ; remap <% Z.eqb %> "eqInt"
     ; remap <% @MyFinMap.lookup %> "Map.find"

     (* remapping constructors *)
     ; ("Z0" ,"0")
     ; ("nil", "[]")

     (* local declarations (available in the same module or in the prelude) *)
     ; local <% @fst %>
     ; local <% @snd %>
     ; local <% andb %>

     (* local types *)
     ; local <% storage %>
     ; local <% value %>
     ; local <% op %>
  ].

MetaCoq Erase (@map nat nat S [1; 2; 3]).

Definition test : TemplateMonad unit :=
  p <- tmQuoteRec (@map nat nat) ;;
  x <- tmEval lazy (erase_template_program p) ;;
  tmPrint x;;
  ret tt.
  (*tmMsg (erase_check_debox_all_print TT "foo" [] p).*)

Run TemplateProgram test.



(** We translate required definitions and print them into a single string containing the whole program. *)
Time Run TemplateProgram
    (storage_def <- tmQuoteConstant "storage" false ;;
     storage_body <- opt_to_template storage_def.(cst_body) ;;
     (* ext_map_def <- tmQuoteConstant "ext_map" false ;; *)
     (* ext_map_body <- opt_to_template ext_map_def.(cst_body) ;; *)
     ind1 <- tmQuoteInductive "op" ;;
     ind_liq1 <- print_one_ind_body TT ind1.(ind_bodies);;
     ind2 <- tmQuoteInductive "instruction" ;;
     ind_liq2 <- print_one_ind_body TT ind2.(ind_bodies);;
     ind3 <- tmQuoteInductive "value" ;;
     ind_liq3 <- print_one_ind_body TT ind3.(ind_bodies);;
     t0 <- toLiquidity TT obs0 ;;
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
                     ++ t0
                     ++ nl ++ nl
                     ++ t1
                     ++ nl ++ nl
                     ++ main "(instruction list) * ((string * int,value) map)") ;;
    tmDefinition "interp_extracted" res).

Definition my_lookup' (m : FMap string Z) (k : string) := FMap.find k m.

(** The extracted program can be printed and copy-pasted to the online Liquidity editor *)
Print interp_extracted.

(** or redirected to a file, creating "interp.liq.out".
 The contents require further post-processing to be compiled with the Liquidity compiler.*)
Redirect "interp.liq" Compute interp_extracted. (* creates "interp.liq.out"*)
