From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

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

Definition my_lookup (m : FMap string Z) (k : string) := FMap.find k m.

(* Quoting this runs forever *)
(* Quote Recursively Definition zz := (my_lookup). *)

Module Interpreter.

  Inductive op : Set := Add | And | Equal.

  Inductive instruction :=
  | IPushZ : Z -> instruction
  | IPushB : bool -> instruction
  | IObs : string -> Z -> instruction
  | IOp : op -> instruction.

  Inductive value : Set := BVal : bool -> value | ZVal : Z -> value.

  (** We will use this approximation of finite maps, because using FMap causes quoting recursively to run forever. It seems it's trying to fetch all the dependencies, and there are many of these. *)
  Definition fmap (K V : Type) := list (K * V).
  Definition ext_map := fmap (string * Z) value.

  Definition storage := list value.

  Definition obs0 s := IObs s 0.

  Definition key_eq (k1 : string * Z) (k2 : string * Z)
    := (k1.1 =? k2.1) && (k1.2 =? k2.2)%Z.

  Fixpoint lookup_map (key : (string * Z)) (m : ext_map ) : option value :=
    match m with
    | [] => None
    | (k,v) :: m' =>
      if (key_eq key k) then Some v else lookup_map key m'
    end.

  Fixpoint interp (ext : ext_map) (insts : list instruction) (s : list value) :=
    match insts with
    | [] => Some s
    | hd :: inst' =>
      match hd with
      | IPushZ i => interp ext inst' (ZVal i :: s)
      | IPushB b => interp ext inst' (BVal b :: s)
      | IObs l i => match lookup_map (l,i) ext with
                   | Some v => Some (v :: s)
                   | None => None
                   end
      | IOp op => match op with
                   | Add => match s with
                            | ZVal i :: ZVal j :: s' => interp ext inst' (ZVal (i+j) :: s')%Z
                            | _ => None
                            end
                   | And => match s with
                            | BVal i :: BVal j :: s' => interp ext inst' (BVal (i && j) :: s')%Z
                            | _ => None
                           end
                   | Equal => match s with
                            | ZVal i :: ZVal j :: s' => interp ext inst' (BVal (i =? j) :: s')%Z
                            | _ => None
                             end
                 end
      end
    end.

(** A wrapper for calling the main functionality. It is important to be explicit about types for all the parameters of entry points *)
Definition main :=
       "let%entry main (prog : (instruction list) * ext_map) s ="
    ++ nl
    ++ "let s = interp (prog.(1), prog.(0) ,[]) in"
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
  [   (* remapping types *)
       remap <% Z %> "int"
     ; remap <% bool %> "bool"
     ; remap <% nat %> "address"
     ; remap <% list %> "list"
     ; remap <% string %> "string"
     ; remap <% fmap %> "map"

     (* remapping operations *)
     ; remap <% Z.add %> "addInt"
     ; remap <% Z.eqb %> "eqInt"
     ; remap <% lookup_map %> "Map.find"

     (* remapping constructors *)
     ; ("Z0" ,"0")
     ; ("nil", "[]")

     (* local declarations (available in the same module or in the prelude) *)
     ; local <% @fst %>
     ; local <% @snd %>
     ; local <% andb %>

     (* local types *)
     ; local <% value %>
     ; local <% op %>
  ].

(** We translate required definitions and print them into a single string containing a whole program. *)
Time Run TemplateProgram
    (storage_def <- tmQuoteConstant "storage" false ;;
     storage_body <- opt_to_template storage_def.(cst_body) ;;
     ext_map_def <- tmQuoteConstant "ext_map" false ;;
     ext_map_body <- opt_to_template ext_map_def.(cst_body) ;;
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
                     ++ "type ext_map = " ++ print_liq_type TT ext_map_body
                     ++ nl ++ nl
                     ++ "let%init storage = []"
                     ++ nl ++ nl
                     ++ t0
                     ++ nl ++ nl
                     ++ t1
                     ++ nl ++ nl
                     ++ main) ;;
    tmDefinition "interp_extracted" res).

(** *)
Print interp_extracted.
