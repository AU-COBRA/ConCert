From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Erasure Require Export EAst.
From MetaCoq.Erasure Require EPretty.

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

Definition can_have_args (bt : box_type) : bool :=
  match bt with
  | TInd _
  | TConst _ => true
  | _ => false
  end.

Fixpoint mkTApps (hd : box_type) (args : list box_type) : box_type :=
  match args with
  | [] => hd
  | a :: args => mkTApps (TApp hd a) args
  end.

Record constant_body :=
  { cst_type : list name * box_type;
    cst_body : option term; }.

(* The arity of an inductive and type alias is an iterated product that we will
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
Record type_var_info :=
  { tvar_name : name;
    tvar_is_logical : bool;
    tvar_is_arity : bool;
    tvar_is_sort : bool; }.

Record one_inductive_body :=
  { ind_name : ident;
    ind_type_vars : list type_var_info;
    ind_ctors : list (ident * list box_type);
    ind_projs : list (ident * box_type); }.

Record mutual_inductive_body :=
  { ind_npars : nat;
    ind_bodies : list one_inductive_body }.

Inductive global_decl :=
| ConstantDecl : constant_body -> global_decl
| InductiveDecl : mutual_inductive_body -> global_decl
| TypeAliasDecl : option (list type_var_info * box_type) -> global_decl.

(* has_deps specified whether the environment includes dependencies of this global *)
Definition global_env := list (kername * bool (* has_deps *) * global_decl).

Fixpoint lookup_env (Σ : global_env) (id : kername) : option global_decl :=
  match Σ with
  | [] => None
  | (name, _, decl) :: Σ => if eq_kername id name then Some decl else lookup_env Σ id
  end.

Definition lookup_constant (Σ : global_env) (kn : kername) : option constant_body :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cst) => Some cst
  | _ => None
  end.

Definition lookup_minductive (Σ : global_env) (kn : kername) : option mutual_inductive_body :=
  match lookup_env Σ kn with
  | Some (InductiveDecl mib) => Some mib
  | _ => None
  end.

Definition lookup_inductive (Σ : global_env) (ind : inductive) : option one_inductive_body :=
  match lookup_minductive Σ (inductive_mind ind) with
  | Some mib => nth_error (ind_bodies mib) (inductive_ind ind)
  | None => None
  end.

Definition lookup_constructor
           (Σ : global_env)
           (ind : inductive) (c : nat) : option (ident * list box_type) :=
  match lookup_inductive Σ ind with
  | Some oib => nth_error (ind_ctors oib) c
  | None => None
  end.

Definition trans_cst_for_printing (cst : constant_body) : EAst.constant_body :=
  {| EAst.cst_body := cst_body cst |}.

Definition trans_oib_for_printing (oib : one_inductive_body) : EAst.one_inductive_body :=
  {| EAst.ind_name := oib.(ind_name);
     EAst.ind_kelim := InType; (* just a "random" pick, not involved in printing *)
     EAst.ind_ctors := map (fun '(nm, args) => (nm, #|args|)) oib.(ind_ctors);
     EAst.ind_projs := map fst oib.(ind_projs) |}.

Definition trans_mib_for_printing
           (mib : mutual_inductive_body) : EAst.mutual_inductive_body :=
  {| EAst.ind_npars := mib.(ind_npars);
     EAst.ind_bodies := map trans_oib_for_printing mib.(ind_bodies) |}.

Definition trans_global_decls_for_printing (Σ : global_env) : EAst.global_context :=
  let map_decl kn (decl : global_decl) : list (kername * EAst.global_decl) :=
      match decl with
      | ConstantDecl cst => [(kn, EAst.ConstantDecl (trans_cst_for_printing cst))]
      | InductiveDecl mib => [(kn, EAst.InductiveDecl (trans_mib_for_printing mib))]
      | TypeAliasDecl _ => []
      end in
  flat_map (fun '(kn, _, decl) => map_decl kn decl) Σ.

Definition print_term (Σ : global_env) (t : term) : string :=
  EPretty.print_term (trans_global_decls_for_printing Σ) [] true false t.
