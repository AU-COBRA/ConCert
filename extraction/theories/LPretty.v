(** Adapted from [EPretty] of MetaCoq.Erasure *)

From Coq Require Import List Program String Ascii.
From ConCert Require Import MyEnv Ast.
From MetaCoq.Template Require Import utils Loader Environment.
From MetaCoq.Template Require Pretty.
From MetaCoq.Erasure Require Import EAst EAstUtils ETyping.

(** Pretty printing *)

Section print_term.
  Context (Σ : global_context).

  Local Open Scope string_scope.

  Definition look (e : env string) (s : string) : option string :=
    lookup e s.

  Definition is_rel (t : Ast.term) :=
  match t with
  | Ast.tRel _ => true
  | _ => false
  end.

  (** Not efficient, but fine for our case *)
  Fixpoint tokenize_aux (buffer : string) (sep : ascii) (s : string) : list string :=
  match s with
  | EmptyString => if (buffer =? EmptyString)%string then []
                  else [buffer]
  | String c tl =>
    if Ascii.eqb c sep
    then buffer :: tokenize_aux EmptyString sep tl
    else tokenize_aux (buffer ++ String c EmptyString) sep tl
  end.

  Definition tokenize := tokenize_aux EmptyString.

  Eval simpl in (tokenize "." "Coq.ZArith.BinInt.Z.add").

  (** Extracts a constant name, inductive name or returns None *)
  Definition to_name (t : Ast.term) : option string:=
  match t with
  | Ast.tConst c _ => Some c
  | Ast.tInd c _ => Some c.(inductive_mind)
  | _ => None
  end.

(** Takes a fully qualified name and returns the last part, e.g.
  for "Coq.ZArith.BinInt.Z.add" returns "add" *)
  Definition unqual_name nm := last (tokenize "." nm) ("Error (Malformed_qualified_name)").


  Fixpoint print_liq_type (TT : env string) (t : Ast.term) :=
  let error := "Error (not_supported_type " ++ Pretty.print_term (Ast.empty_ext []) [] true t ++ ")" in
  match t with
  | Ast.tInd ind _ =>
    match look TT ind.(inductive_mind) with
    | Some nm => nm
    | None => ind.(inductive_mind)
    end
  | Ast.tApp (Ast.tInd ind _) [t1;t2] =>
      if (Ast.from_option (to_name <% prod %>) "" =? ind.(inductive_mind))%string then
        print_liq_type TT t1 ++ " * " ++ print_liq_type TT t2
      else error
  | _ => "Error (not_supported_type " ++ Pretty.print_term (Ast.empty_ext []) [] true t ++ ")"
  end.

  Fixpoint get_ctor_type (TT : env string) (ty : Ast.term) : list string:=
    match ty with
    | Ast.tProd _ dom codom =>
      if negb (is_rel dom)
      then print_liq_type TT dom :: get_ctor_type TT codom
      else []
    | _ => if is_rel ty then [] else
             ["Error (not_supported_type " ++ Pretty.print_term (Ast.empty_ext []) [] true ty ++ ")"]
  end.

  Definition print_ctor_type (TT : env string) (ty : Ast.term) : string :=
    concat " * " (get_ctor_type TT ty).

  Definition print_ctor (TT : env string) (nm_ty : ident * Ast.term) : string :=
    let (nm,ty) := nm_ty in
    let tys := get_ctor_type TT ty in
    match tys with
    | [] => nm
    | _ => nm ++ " of " ++ concat " * " (get_ctor_type TT ty)
    end.

  Definition print_inductive (TT : env string) (oib : Ast.one_inductive_body) : string :=
    "type " ++ oib.(Ast.ind_name) ++ " = "
                              ++ nl ++ concat "| " (map (fun p => print_ctor TT p.1 ++ nl) oib.(Ast.ind_ctors)).

    Definition print_def {A : Set} (f : A -> string) (def : def A) :=
    string_of_name (dname def) ++ " { struct " ++ string_of_nat (rarg def) ++ " }"
                   ++ " := " ++ nl ++ f (dbody def).

    Definition print_defs (print_term : context -> bool -> bool -> term -> string) Γ (defs : mfixpoint term) :=
    let ctx' := List.map (fun d => {| decl_name := dname d; decl_body := None |}) defs in
    print_list (print_def (print_term (ctx' ++ Γ)%list true false)) (nl ++ " with ") defs.

  Definition lookup_ind_decl ind i :=
    match lookup_env Σ ind with
    | Some (InductiveDecl {| ind_bodies := l |}) =>
      match nth_error l i with
      | Some body => Some body
      | None => None
      end
    | _ => None
    end.

  Fixpoint decompose_lam (t : term) (n : nat) : (list aname) * term :=
    match n with
    | 0 => ([], t)
    | S n =>
      match t with
      | tLambda na B => let (ns, B) := decompose_lam B n in
                        (na :: ns, B)
      | _ => ([], t)
      end
    end.

  Definition is_fresh (Γ : context) (id : ident) :=
    List.forallb
      (fun decl =>
         match decl.(decl_name) with
         | nNamed id' => negb (ident_eq id id')
         | nAnon => true
         end) Γ.

  Fixpoint name_from_term (t : term) :=
    match t with
    | tRel _ | tVar _ | tEvar _ _ => "H"
    | tLambda na t => "f"
    | tLetIn na b t' => name_from_term t'
    | tApp f _ => name_from_term f
    | tConst c => "x"
    | _ => "U"
    end.

  Definition fresh_id_from Γ n id :=
    let fix aux i :=
      match i with
      | 0 => id
      | S i' =>
        let id' := id ++ string_of_nat (n - i) in
        if is_fresh Γ id' then id'
        else aux i'
      end
    in aux n.

  Definition fresh_name (Γ : context) (na : name) (t : term) :=
    let id := match na with
              | nNamed id => id
              | nAnon => name_from_term t
              end
    in
    if is_fresh Γ id then nNamed id
    else nNamed (fresh_id_from Γ 10 id).

  Fixpoint print_constr (TT : env string) (ind : inductive) (i : nat) :=
    match lookup_ind_decl ind.(inductive_mind) ind.(inductive_ind) with
    | Some oib =>
      match nth_error oib.(ind_ctors) i with
      | Some (na, _, _) =>
        match (look TT na) with
        | Some c => c
        | None => na
        end
      | None =>
        "UnboundConstruct(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ ")"
      end
    | None =>
      "UnboundConstruct(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ ")"
    end.

  Fixpoint print_term (TT : env string) (Γ : context) (top : bool) (inapp : bool) (t : term) {struct t} :=
  match t with
  | tBox _ => "()" (* boxes become the contructor of the [unit] type *)
  | tRel n =>
    match nth_error Γ n with
    | Some {| decl_name := na |} =>
      match na with
      | nAnon => "Anonymous (" ++ string_of_nat n ++ ")"
      | nNamed id => id
      end
    | None => "UnboundRel(" ++ string_of_nat n ++ ")"
    end
  | tVar n => "Var(" ++ n ++ ")"
  | tEvar ev args => "Evar(" ++ string_of_nat ev ++ "[]" (* TODO *)  ++ ")"
  | tLambda na body =>
    let na' := fresh_name Γ na t in
    parens top ("fun " ++ string_of_name na'
                                ++ " -> " ++ print_term TT (vass na' :: Γ) true false body)
  | tLetIn na def body =>
    let na' := fresh_name Γ na t in
    parens top ("let " ++ string_of_name na' ++
                      " = " ++ print_term TT Γ true false def ++ " in " ++ nl ++
                      print_term TT (vdef na' def :: Γ) true false body)
  | tApp f l =>
    match f with
    (* is it a pair ? *)
    | tApp (tConstruct ind _) e1' =>
      if String.eqb ind.(inductive_mind) "Coq.Init.Datatypes.prod"
      then parens false (print_term TT Γ true false e1' ++ ", " ++ print_term TT Γ true false l)
      else parens (top || inapp) (print_term TT Γ false true f ++ " " ++ print_term TT Γ false false l)
    | _ => parens (top || inapp) (print_term TT Γ false true f ++ " " ++ print_term TT Γ false false l)
    end
  | tConst c =>
    match look TT c with
    | Some op => op
    | _ => c
    end
  | tConstruct ind l => print_constr TT ind l
  | tCase (mkInd mind i as ind, pars) t brs =>
    (* [if-then-else] is a special case *)
    if mind =? "Coq.Init.Datatypes.bool" then
      match brs with
      | [b1;b2] =>
        parens top
                ("if " ++ print_term TT Γ true false t
                       ++ " then " ++ print_term TT Γ true false (snd b1)
                       ++ " else " ++ print_term TT Γ true false (snd b2))
      | _ => "Error (Malformed pattern-mathing on bool: given "
               ++ string_of_nat (List.length brs) ++ " branches " ++ ")"
      end
    else
    match lookup_ind_decl mind i with
    | Some oib =>
      let fix print_branch Γ arity br {struct br} :=
          match arity with
            | 0 => "-> " ++ print_term TT Γ false false br
            | S n =>
              match br with
              | tLambda na B =>
                let na' := fresh_name Γ na br in
                string_of_name na' ++ "  " ++ print_branch (vass na' :: Γ) n B
              | t => "-> " ++ print_term TT Γ false false br
              end
            end
        in
        let brs := map (fun '(arity, br) =>
                          print_branch Γ arity br) brs in
        let brs := combine brs oib.(ind_ctors) in
        parens top ("match " ++ print_term TT Γ true false t ++
                    " with " ++ nl ++
                    print_list (fun '(b, (na, _, _)) =>
                                  from_option (look TT na) na ++ " " ++ b)
                    (nl ++ " | ") brs)
    | None =>
      "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
              ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
    end
  | tProj (mkInd mind i as ind, pars, k) c =>
    match lookup_ind_decl mind i with
    | Some oib =>
      match nth_error oib.(ind_projs) k with
      | Some (na, _) => print_term TT Γ false false c ++ ".(" ++ na ++ ")"
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term TT Γ true false c ++ ")"
      end
    | None =>
      "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                     ++ print_term TT Γ true false c ++ ")"
    end


    (** TODO: implement fix printing properly. Currently it prints in the same ways as in the erasure *)
  | tFix l n =>
    parens top ("let fix " ++ print_defs (print_term TT) Γ l ++ nl ++
                          " in " ++ List.nth_default (string_of_nat n) (map (string_of_name ∘ dname) l) n)
  | tCoFix l n =>
    parens top ("let cofix " ++ print_defs (print_term TT) Γ l ++ nl ++
                              " in " ++ List.nth_default (string_of_nat n) (map (string_of_name ∘ dname) l) n)
  end.

End print_term.

Local Open Scope string_scope.


(** We un-overload operations and add definitions that are more convenient to use during the pretty-printing phase. This part must be included to all the contracts. *)

Definition prod_ops :=
       "let[@inline] fst (p : 'a * 'b) : 'a = p.(0)"
    ++ nl
    ++ "let[@inline] snd (p : 'a * 'b) : 'b = p.(1)".

Definition int_ops :=
       "let[@inline] addInt (i : int) (j : int) = i + j"
    ++ nl
    ++ "let[@inline] subInt (i : int) (j : int) = i - j"
    ++ nl
    ++ "let[@inline] leInt (i : int) (j : int) = i <= j"
    ++ nl
    ++ "let[@inline] ltInt (i : int) (j : int) = i < j"
    ++ nl
    ++ "let[@inline] eqInt (i : int) (j : int) = i = j".

Definition tez_ops :=
       "let[@inline] addTez (n : tez) (m : tez) = n + m"
    ++ nl
    ++ "let[@inline] subTez (n : tez) (m : tez) = n - m"
    ++ nl
    ++ "let[@inline] leTez (a : tez ) (b : tez ) = a <= b"
    ++ nl
    ++ "let[@inline] ltTez (a : tez ) (b : tez ) =  a < b"
    ++ nl
    ++ "let[@inline] eqTez (a : tez ) (b : tez ) = a = b".

Definition nat_ops :=
       "let[@inline] eqN (a : nat ) (b : nat ) = a = b"
    ++ nl
    ++ "let[@inline] lebN (a : nat ) (b : nat ) = a <= b"
    ++ nl
    ++ "let[@inline] ltbN (a : nat ) (b : nat ) = a < b".

Definition bool_ops :=
  "let[@inline] andb (a : bool ) (b : bool ) = a & b".

Definition time_ops :=
       "let[@inline] eqb_time (a1 : timestamp) (a2 : timestamp) = a1 = a2"
    ++ nl
    ++ "let[@inline] leb_time (a1 : timestamp) (a2 : timestamp) = a1 <= a2"
    ++ nl
    ++ "let[@inline] ltb_time (a1 : timestamp) (a2 : timestamp) = a1 < a2".

Definition address_ops :=
  "let[@inline] eq_addr (a1 : address) (a2 : address) = a1 = a2".


Definition LiquidityPrelude :=
  print_list id (nl ++ nl)
             [prod_ops; int_ops; tez_ops; nat_ops;
             bool_ops; time_ops; address_ops].

Definition printWrapper (contract : string): string :=
  "let wrapper param (st : storage)"
        ++ " = "
        ++ "match " ++ contract ++ " param st" ++ " with"
        ++ "| Some v -> v"
        ++ "| None -> failwith ()".

Definition printMain :=
  "let%entry main param st = wrapper param st".
