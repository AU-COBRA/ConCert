(** Adapted from [EPretty] of MetaCoq.Erasure *)

From Coq Require Import List Program String Ascii.
From ConCert Require Import MyEnv Ast.
From MetaCoq.Template Require Import utils Loader Environment.
From MetaCoq.Template Require Pretty.
From MetaCoq.Erasure Require Import Debox EAst EAstUtils ETyping.

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
  | Ast.tApp (Ast.tInd ind i) [t1] =>
    if (Ast.from_option (to_name <% list %>) "" =? ind.(inductive_mind))%string then
      print_liq_type TT t1 ++ " " ++ "list"
    else error
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

  (* This is more fixpoint friendly defintion, using [Edecompose_lam] doesn't work well with print_def calls, bacuse we pass print_term to [print_defs] and this is sensitive to how the decreasing argument is determined *)
  Fixpoint lam_body (t : E.term) : E.term :=
    match t with
    | E.tLambda n b => lam_body b
    | _ => t
    end.

  Definition print_def (f : context -> term -> string) (def : def term) :=
    let (args, _) := Edecompose_lam (dbody def) in
    let ctx := rev (map (vass ∘ binder_name) args) in
    let sargs := concat " ," (map (fun x => string_of_name x.(binder_name)) args) in
    string_of_name (dname def) ++ parens false sargs  ++ " = "
                   ++ nl ++ f ctx (lam_body (dbody def)).

    Definition print_defs (print_term : list string -> context -> bool -> bool -> term -> string) (FT : list string) (Γ : context) (defs : mfixpoint term) :=
      let ctx' := List.map (fun d => {| decl_name := dname d; decl_body := None |}) defs in
      let fix_names := List.map (string_of_name ∘ dname) defs in
    print_list (print_def (fun Γ' => print_term (fix_names ++ FT)%list (Γ' ++ ctx' ++ Γ)%list true false)) (nl ++ " with ") defs.

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


  Definition is_pair_constr (ind : inductive) :=
    String.eqb ind.(inductive_mind) "Coq.Init.Datatypes.prod".

  Definition print_pair (f : term -> string) (t1 : term) (t2 : term) :=
    parens false ((f t1) ++ " ," ++ (f t2)).

  Definition is_list_cons (ind : inductive) (ctor_num : nat):=
    andb (String.eqb ind.(inductive_mind) "Coq.Init.Datatypes.list")
         (Nat.eqb ctor_num 1).

  Definition print_list_cons (f : term -> string) (t1 : term) (t2 : term) :=
    (f t1) ++ " :: " ++ (f t2).


  Definition app_args {A} (f : E.term -> A) :=
    fix go (t : E.term) := match t with
    | E.tApp t1 t2 => f t2 :: go t1
    | _ => []
    end.

  Fixpoint in_list {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
           (l : list A) (a : A) : bool :=
    match l with
    | [] => false
    | hd :: tl => if eq_dec hd a then true
                else in_list eq_dec tl a
    end.

  Definition get_fix_rel_applied (FT : list string) (Γ : context) (t : E.term) :=
    let (b,_) := decompose_app t in
    match b with
    | E.tRel i => match nth_error Γ i with
                 | Some d =>
                   let nm := (string_of_name d.(decl_name)) in
                   if in_list String.string_dec FT nm then Some nm
                   else None
                 | None => None
                 end
    | _ => None
    end.

  (* Builds a context for the branch *)
  Definition get_ctx_from_branch (Γ : context) : nat -> E.term -> context :=
    let fix go (ctx : context) (arity: nat) (branch : E.term) :=
    match arity with
    | 0 => []
    | S n =>
      match branch with
      | tLambda na B =>
        let na' := fresh_name Γ na branch in
        go (vass na' :: ctx) n B
      | t => []
      end
    end
    in go [].

  (* Definition print_branch (f : context -> E.term -> string) (branch : nat × E.term ) : string := *)
  (*   let (arity, br) = branch in *)
  (*   get_ctx_from_branch *)


  Fixpoint print_term (FT : list string) (TT : env string) (Γ : context) (top : bool) (inapp : bool) (t : term) {struct t} :=
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
                                ++ " -> " ++ print_term FT TT (vass na' :: Γ) true false body)
  | tLetIn na def body =>
    let na' := fresh_name Γ na t in
    parens top ("let " ++ string_of_name na' ++
                      " = " ++ print_term FT TT Γ true false def ++ " in " ++ nl ++
                      print_term FT TT (vdef na' def :: Γ) true false body)
  | tApp f l =>
    match get_fix_rel_applied FT Γ f with
    | Some nm =>
      let apps := rev (app_args (print_term FT TT Γ true false) t) in
      nm ++ " " ++ parens false (concat ", " apps)
    | None =>
      match f with
      | tApp (tConstruct ind i) e1' =>
      (* is it a pair ? *)
        if is_pair_constr ind then print_pair (print_term FT TT Γ true false) e1' l
        else
          (* is it a cons ? *)
          if is_list_cons ind i then print_list_cons (print_term FT TT Γ true false) e1' l
          else  parens (top || inapp) (print_term FT TT Γ false true f ++ " " ++ print_term FT TT Γ false false l)
      | _ => parens (top || inapp) (print_term FT TT Γ false true f ++ " " ++ print_term FT TT Γ false false l)
      end
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
                ("if " ++ print_term FT TT Γ true false t
                       ++ " then " ++ print_term FT TT Γ true false (snd b1)
                       ++ " else " ++ print_term FT TT Γ true false (snd b2))
      | _ => "Error (Malformed pattern-mathing on bool: given "
               ++ string_of_nat (List.length brs) ++ " branches " ++ ")"
      end
    else
      (* [list is a special case] is a special case *)
      if mind =? "Coq.Init.Datatypes.list" then
        match brs with
        | [b1;b2] =>
          let nil_case := "[] -> " ++ print_term FT TT Γ false false b1.2 in
          let (cons_args, _) := Edecompose_lam b2.2 in
          let cons_body := lam_body b2.2 in
          let cons_pat := concat " :: " (map (fun x => string_of_name (fresh_name Γ x.(binder_name) b2.2)) cons_args) in
          let cons_ctx := rev (map (vass ∘ binder_name) cons_args) in
          let cons_case := cons_pat ++ " -> " ++ print_term FT TT (cons_ctx ++ Γ)%list false false cons_body in
          parens top
             ("match " ++ print_term FT TT Γ true false t
                       ++ " with " ++ nl
                       ++ concat (nl ++ " | ") [nil_case;cons_case])
        | _ => "Error (Malformed pattern-mathing on bool: given "
                ++ string_of_nat (List.length brs) ++ " branches " ++ ")"
        end
      else
    match lookup_ind_decl mind i with
    | Some oib =>
      let fix print_branch Γ sep arity br {struct br} :=
          match arity with
            | 0 => "-> " ++ print_term FT TT Γ false false br
            | S n =>
              match br with
              | tLambda na B =>
                let na' := fresh_name Γ na br in
                string_of_name na' ++ sep ++ print_branch (vass na' :: Γ) sep n B
              | t => "-> " ++ print_term FT TT Γ false false br
              end
            end
      in
      let brs := map (fun '(arity, br) =>
                        print_branch Γ "  " arity br) brs in
      let brs := combine brs oib.(ind_ctors) in
      parens top
             ("match " ++ print_term FT TT Γ true false t
                       ++ " with " ++ nl
                       ++ print_list (fun '(b, (na, _, _)) =>
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
      | Some (na, _) => print_term FT TT Γ false false c ++ ".(" ++ na ++ ")"
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term FT TT Γ true false c ++ ")"
      end
    | None =>
      "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                     ++ print_term FT TT Γ true false c ++ ")"
    end
  | tFix l n =>
    parens top ("let rec " ++ print_defs (fun ft => print_term ft TT) FT Γ l ++ nl ++
                          " in " ++ List.nth_default (string_of_nat n) (map (string_of_name ∘ dname) l) n)
  | tCoFix l n => "NotSupportedCoFix"
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
