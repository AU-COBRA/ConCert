From Coq Require Import List.
From MetaCoq.Erasure Require Export EAst.

Import ListNotations.

Inductive box_type :=
| TBox
| TAny
| TArr (dom : box_type) (codom : box_type)
| TApp (_ : box_type) (_ : box_type)
| TVar (_ : nat) (* Index of type variable *)
| TInd (_ : inductive)
| TConst (_ : kername).

Fixpoint decompose_arr (bt : box_type) : list box_type * box_type :=
  match bt with
  | TArr dom cod => let (args, res) := decompose_arr cod in
                    (dom :: args, res)
  | _ => ([], bt)
  end.

Record constant_body :=
  { cst_type : list name * box_type;
    cst_body : option term; }.

(* The arity of an inductive is an iterated product that we will
     decompose into type vars. Each type var has information about its
     type associated with it. Here are a couple of examples:

     1. [sig : forall (A : Type), (A -> Prop) -> Type] returns [[a; b]] where

          tvar_is_logical a = false,
          tvar_is_arity a = true,
          tvar_is_sort a = true,

          tvar_is_logical b = true,
          tvar_is_arity b = true,
          tvar_is_sort b = false,

     2. [Vector.t : Type -> nat -> Type] returns [[a; b]] where

          tvar_is_logical a = false,
          tvar_is_arity a = true,
          tvar_is_sort a = true,

          tvar_is_logical b = false,
          tvar_is_arity b = false,
          tvar_is_sort b = false *)
Record oib_type_var :=
  { tvar_name : name;
    tvar_is_logical : bool;
    tvar_is_arity : bool;
    tvar_is_sort : bool; }.

Record one_inductive_body :=
  { ind_name : ident;
    ind_type_vars : list oib_type_var;
    ind_ctors : list (ident * list box_type);
    ind_projs : list (ident * box_type); }.

Record mutual_inductive_body :=
  { ind_npars : nat;
    ind_bodies : list one_inductive_body }.

Inductive global_decl :=
| ConstantDecl : constant_body -> global_decl
| InductiveDecl : mutual_inductive_body -> global_decl.

Definition global_env := list (kername * global_decl).

Fixpoint lookup_env (Σ : global_env) (id : kername) : option global_decl :=
  match Σ with
  | [] => None
  | (name, decl) :: Σ => if eq_kername id name then Some decl else lookup_env Σ id
  end.
