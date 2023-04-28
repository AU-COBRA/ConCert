(** * Pretty-printing Liquidity code *)
(** Adapted from [EPretty] of MetaCoq.Erasure. *)

(** ** Features/limitations *)

(** Printing covers most constructs of CIC_box (terms after erasure).
    Usually we have to remove redundant boxes before printing.
    There are some limitations on what can work after extraction, due to the
    nature of Liquidity, or sometimes, lack of proper support.

    Liquidity allows only tail-recursive calls and recursive functions must
    have only one argument. So, we pack multiple arguments in a tuple.
    In order for that to be correct, we assume that all fixpoints are fully applied.

    Another issue: constructors accept only one argument, so we have to uncurry
    (pack in a tuple) applications as well. This transformation is applied to all
    constructors and the pretty-printing stage. Again, we assume that the constructors
    are fully applied (e.g. eta-expanded at the previous stage).

    Pattern-matching: pattern-matching on pairs is not supported by Liquidity,
    so all the programs must use projections. *)
From Coq Require Import Basics.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import ssrfun.
From Coq Require Import ZArith.
From ConCert.Utils Require Import Env.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import StringExtra.
From ConCert.Extraction Require Import Common.
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Utils Require Import MCList.
From MetaCoq.Utils Require Import monad_utils.

Local Open Scope string_scope.
Local Open Scope program_scope.

Import String ListNotations MCMonadNotation.

(* F# style piping notation for convenience *)
Notation "f <| x" := (f x) (at level 32, left associativity, only parsing).
(* i.e. f <| x <| y = (f <| x) <| y, and means (f x) y *)
Notation "x |> f" := (f x) (at level 31, left associativity, only parsing).
(* i.e. x |> f |> g = (x |> f) |> g, and means g (f x) *)

Notation "s1 ^ s2" := (String.append s1 s2).

Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).

Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).

Local Coercion bytestring.String.to_string : bytestring.String.t >-> string.


Section print_term.
  Context (Σ : ExAst.global_env).

  Import BasicAst.

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

(** Takes a fully qualified name and returns the last part, e.g.
  for "Coq.ZArith.BinInt.Z.add" returns "add" *)
  Definition unqual_name nm := last (tokenize "." nm) ("Error (Malformed_qualified_name)").

  Definition print_uncurried (s : string) (args : list string) :=
    let print_parens := (Nat.ltb 0 (List.length args)) in
    s ++ " " ++ parens ((negb print_parens)) (concat ", " args).

  Definition is_arr (bt : box_type) : bool :=
  match bt with
  | TArr _ _ => true
  | _ => false
  end.

  Definition map_targs (f : box_type -> string) : box_type -> list string :=
    fix go bt := match bt with
                 | TApp t1 t2 => (go t1 ++ [f t2])%list
                 | _ => []
                 end.

  Fixpoint get_tapp_hd (bt : box_type) : box_type :=
    match bt with
    | TApp t1 t2 => get_tapp_hd t1
    | _ => bt
    end.

  Definition print_type_var (v : name) (i : nat) :=
    match v with
    | nNamed nm => "'" ++ uncapitalize nm
    | nAnon => "anon_tvar" ++ string_of_nat i
    end.


  Definition print_box_type (prefix : string) (TT : env string) (vars : list name)
    : box_type -> string :=
    fix go (bt : box_type) :=
  match bt with
  | TBox => "unit"
  | TArr dom codom => parens (negb (is_arr dom)) (go dom) ++ " -> " ++ go codom
  | TApp t1 t2 =>
    let hd := get_tapp_hd t1 in
    let args := map_targs go bt in
    match hd with
    | TInd ind =>
      (* a special case of products - infix *)
      if eq_kername <%% prod %%> ind.(inductive_mind) then
        parens false (concat " * " args)
      else parens false (print_uncurried "" args ++ " " ++ go hd)
    | _ => parens false (print_uncurried "" args ++ " " ++ go hd)
    end
  | TVar i => match nth_error vars i with
             | Some nm => print_type_var nm i
             | None => "UnknownTypeVar(" ++ string_of_nat i ++ ")"
             end
  | TInd s =>
    let full_ind_name := string_of_kername s.(inductive_mind) in
    uncapitalize (with_default (prefix ++ s.(inductive_mind).2) (look TT full_ind_name))
  | TConst s =>
    let full_cst_name := string_of_kername s in
    uncapitalize (with_default (prefix ++ s.2) (look TT full_cst_name))
  | TAny => "UnknownType"
  end.

  Definition print_ctor
             (prefix : string)
             (TT : env string)
             (vars : list name)
             (ctor : ident * list (name * box_type)) :=
    let (nm,tys) := ctor in
    let nm := capitalize nm in
    match tys with
    | [] => prefix ++ nm
    | _ => prefix ++ nm ++ " of "
                  ++ concat " * " (map (print_box_type prefix TT vars ∘ snd) tys)
    end.

  Definition print_proj (prefix : string)
             (TT : env string)
             (vars : list name)
             (proj : ident * box_type) : string :=
    let (nm, ty) := proj in
    prefix
      ^ nm
      ^ " : "
      ^ print_box_type prefix TT vars ty.

  Definition is_one_constructor_inductive_and_not_record (oib : ExAst.one_inductive_body) :=
    match oib.(ExAst.ind_ctors), oib.(ExAst.ind_projs) with
    | [_], _::_::_ => false (* it is a record because it has projections, and one constructor *)
    (* 1-inductive that's not a record *)
    | [(_, [_],_)],_ => true
    (* record without primitive projections; 1-inductive with > args in its constructor *)
    | [_],[] => false
    | _,_ => false
    end.


  Definition print_inductive (prefix : string) (TT : env string)
             (oib : ExAst.one_inductive_body) :=
    let ind_nm := with_default (prefix ++ oib.(ExAst.ind_name)) (lookup TT oib.(ExAst.ind_name)) in
    let vars := map tvar_name oib.(ind_type_vars) in
    let params :=
        if (Nat.eqb #|oib.(ind_type_vars)| 0) then ""
        else let ps := concat "," (mapi (fun i v => print_type_var v i) vars) in
             (parens (Nat.ltb #|oib.(ind_type_vars)| 1) ps) ++ " " in
    let print_record projs_and_ctors :=
      let projs_and_ctors_printed :=
        map (fun '(p, (proj_nm, ty)) => print_proj (capitalize prefix) TT vars (p.1, ty)) projs_and_ctors in
      "type " ++ params ++ uncapitalize ind_nm ++ " = {" ++ nl
            ++ concat (";" ++ nl) projs_and_ctors_printed ++ nl
            ++ "}" in
    (* one-constructor inductives with non-empty ind_projs (projection identifiers)
       and > 1 projections
       are assumed to be records *)
    match oib.(ExAst.ind_ctors), oib.(ExAst.ind_projs) with
    | [build_record_ctor], _::_::_ =>
      let '(_, ctors,_) := build_record_ctor in
      let projs_and_ctors := combine oib.(ExAst.ind_projs) ctors in
      print_record projs_and_ctors
      (* otherwise, one-constructor inductives are printed as aliases
         since liquidity doesn't allow inductives with 1 constructor. *)
      | [(_, [ctor_arg], _)], _ => "type " ++ params ++ uncapitalize ind_nm ++" = "
      ++ concat " * " (map (print_box_type prefix TT vars ∘ snd) [ctor_arg])
      (* otherwise, the record might be defined without primitive projections.
         Hence, we look for "projections" in the constructor *)
      | [(_,ctor_args,_)],[] =>
      let projs := map (fun '(nm, bt) => (string_of_name nm, bt)) ctor_args in
      let projs_and_ctors := combine projs ctor_args in
      print_record projs_and_ctors

    | _,_ => "type " ++ params ++ uncapitalize ind_nm ++" = "
            ++ nl
            ++ concat "| " (map (fun p => print_ctor (capitalize prefix) TT vars p.1 ++ nl) oib.(ExAst.ind_ctors))
    end.

  Definition is_sort (t : Ast.term) :=
    match t with
    | Ast.tSort _ => true
    | _ => false
    end.

  Definition is_prod (t : Ast.term) :=
    match t with
    | Ast.tProd _ _ _ => true
    | _ => false
    end.

  Open Scope bool.

  Fixpoint Edecompose_lam (t : term) : (list name) * term :=
  match t with
  | tLambda n b =>
      let (ns, b) := Edecompose_lam b in
      (n :: ns, b)
  | _ => ([], t)
  end.


  (* NOTE: This is more fixpoint-friendly definition, using [Edecompose_lam]
    doesn't work well with print_def calls, because we pass print_term to
    [print_defs] and this is sensitive to how the decreasing argument is determined *)
  Fixpoint lam_body (t : term) : term :=
    match t with
    | tLambda n b => lam_body b
    | _ => t
    end.

  Import EAst.

  Definition print_def (print_term : context -> bool -> bool -> term -> string)
                       (Γ : context) (fdef : def term) :=
      let ctx' := [{| decl_name := dname fdef; decl_body := None |}] in
      let fix_name := string_of_name (fdef.(dname)) in
      let (args, _) := Edecompose_lam (fdef.(dbody)) in
      let ctx := rev (map vass args) in
      let sargs := print_uncurried "" (map (fun x => bs_to_s (string_of_name x)) args) in
      string_of_name fdef.(dname)
          ++ " " ++ sargs ++ " = "
          ++ nl
          ++ print_term (ctx ++ ctx' ++ Γ)%list true false (lam_body fdef.(dbody)).

  Definition lookup_ind_decl ind i :=
    match ExAst.lookup_env Σ ind with
    | Some (ExAst.InductiveDecl {| ExAst.ind_bodies := l |}) =>
      match nth_error l i with
      | Some body => Some body
      | None => None
      end
    | _ => None
    end.

  (* Certain names in Liquidity are reserved (like 'to' and others) so we
     ensure no fresh names are reserved *)
  (* Note: for reserved names from the syntax (like 'let', 'in', 'match', etc.)
     we don't need to add them since they are also reserved names in Coq, hence
     we can't write Coq programs with these names anyway. *)
  Definition is_reserved_name (id : string) (reserved : list string) :=
    List.existsb (eqb id) reserved.

  Definition liquidity_reserved_names : list string :=
    [
       "to"
      ; "from"
      ; "val"
      ; "balance"
      ; "continue"
    ].

  Definition is_fresh (Γ : context) (id : string) :=
    negb (is_reserved_name id liquidity_reserved_names)
    &&
    List.forallb
      (fun decl =>
         match decl.(decl_name) with
         | nNamed id' =>
           (* NOTE: we compare the identifiers up to
              the capitalization of the first letters *)
           negb (eqb (uncapitalize id) (uncapitalize id'))
         | nAnon => true
         end) Γ.

  Fixpoint name_from_term (t : term) :=
    match t with
    | tRel _ | tVar _ | tEvar _ _ => "h"
    | tLambda na t => "f"
    | tLetIn na b t' => name_from_term t'
    | tApp f _ => name_from_term f
    | tConst c => "x"
    | _ => "u"
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


  Definition fresh_string_name (Γ : context) (na : name) (t : term) : string :=
    let id := match na with
              | nNamed id => id
              | nAnon => name_from_term t
              end
    in
    let id := uncapitalize id in
    if is_fresh Γ id then id
    else fresh_id_from Γ 10 (s_to_bs id).

  Definition get_constr_name (ind : inductive) (i : nat) : string :=
    match lookup_ind_decl ind.(inductive_mind) ind.(inductive_ind) with
    | Some oib =>
      match nth_error oib.(ExAst.ind_ctors) i with
      | Some (na, _, _) => na
      | None =>
        "UnboundConstruct(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ ")"
      end
    | None =>
      "UnboundConstruct(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ ")"
    end.

  Definition is_pair_constr (ind : inductive) :=
    eq_kername ind.(inductive_mind) <%% prod %%>.

  Definition print_pair (f : term -> string) (t1 : term) (t2 : term) :=
    parens false ((f t1) ++ " ," ++ (f t2)).

  Definition is_list_cons (ind : inductive) (ctor_num : nat) :=
    andb (eq_kername ind.(inductive_mind) <%% list %%>)
         (Nat.eqb ctor_num 1).

  Definition print_list_cons (f : term -> string) (t1 : term) (t2 : term) :=
    (f t1) ++ " :: " ++ (f t2).

  Definition is_record_constr (t : term)
                              (projs : list (ident * ExAst.one_inductive_body))
                              : option ExAst.one_inductive_body :=
    match t with
    | tConstruct (mkInd mind j as ind) i [] =>
      match lookup_ind_decl mind i with
      (* Check if it has only 1 constructor, and projections are specified, and > 1 projections *)
      | Some oib => if is_one_constructor_inductive_and_not_record oib
                    then None
                    else if Nat.eqb 1 (List.length oib.(ExAst.ind_ctors))
                    then Some oib
                    else None
      | _ => None
      end
    | tConst kn => option_map snd (List.find (fun p => string_of_kername kn =? bs_to_s p.1) projs)
    | _ => None
  end.

Definition get_record_projs (oib : ExAst.one_inductive_body) : list string :=
    match oib.(ExAst.ind_ctors), oib.(ExAst.ind_projs) with
    (* it is a record because it has projections, and one constructor *)
    | [_], _::_::_ => map (fun x => bs_to_s (fst x)) oib.(ExAst.ind_projs)
    (* 1-inductive that's not a record *)
    | [(_, projs, _)],_ => projs |> map fst
                                  |> map (fun x => bs_to_s (string_of_name x))
    (* record without primitive projections; 1-inductive with > args in its constructor *)
    | _,_ => []
    end.

  Definition is_name_remapped nm TT :=
    match (look TT nm) with
    | Some nm' => true
    | None => false
    end.

  Definition app_args {A} (f : term -> A) :=
    fix go (t : term) := match t with
    | tApp t1 t2 => f t2 :: go t1
    | _ => []
    end.

  Fixpoint in_list {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
           (l : list A) (a : A) : bool :=
    match l with
    | [] => false
    | hd :: tl => if eq_dec hd a then true
                else in_list eq_dec tl a
    end.

  (** Builds a context for the branch *)
  Definition get_ctx_from_branch (Γ : context) : nat -> term -> context :=
    let fix go (ctx : context) (arity: nat) (branch : term) :=
    match arity with
    | 0 => []
    | S n =>
      match branch with
      | tLambda na B =>
        let na' := fresh_string_name Γ na branch in
        go (vass (nNamed (s_to_bs na')) :: ctx) n B
      | _ => []
      end
    end
    in go [].

  Fixpoint fresh_string_names (Γ : context) (vs : list name) : context * list string :=
    match vs with
    | [] => (Γ, [])
    | v :: vs0 =>
      let nm := fresh_string_name Γ v (tVar (s_to_bs "dummy")) in
      (* add name to the context to avoid shadowing due to name clashes *)
      let Γ0 := vass (nNamed (s_to_bs nm)) :: Γ in
      let '(Γ1, vs1) := fresh_string_names Γ0 vs0 in
      (Γ1, nm :: vs1)
    end.

  (* [print_pat] expects that the names in pt.1 are already checked for freshness *)
  Definition print_pat (Γ : context) (prefix : string)
                       (TT : env string) (ctor : string)
                       (infix : bool) (pt : list string * string) : string :=
    let vars := rev pt.1 in
    if infix then
      concat (" " ++ ctor ++ " ") vars ++ " -> " ++ pt.2
    else
      let ctor_nm := with_default (capitalize prefix ++ capitalize ctor) (look TT ctor) in
      let ctor_nm := if ctor_nm =? "Pair" then "" else ctor_nm in
      let print_parens := (Nat.ltb 1 (List.length pt.1)) in
      print_uncurried ctor_nm vars ++ " -> " ++ pt.2.

  Definition print_transfer (args : list string) :=
    match args with
    | [] => "MalformedTransfer()"
    | [a1; a2] => "Contract.call " ++ a1 ++ " " ++ a2 ++ " "
                                 ++ "default" ++ " ()"
    | _ => "MalformedTransfer(" ++ concat "," args ++ ")"
    end.

  (** ** The pretty-printer *)

  (** [prefix] - a sting pre-pended to the constants' and constructors' names to avoid clashes
      [FT] - list of fixpoint names. Used to determine if uncurrying is needed for an
      applied variable (if it corresponds to a recursive call).
      The initial value is an empty list. Once we fit a fixpoint case, we add the fixpoint
      name to [FT], so all the recursive calls in the fixpoint body are packed into a tuple.

      [TT] - translation table allowing for remapping constants and constructors
      to Liquidity primitives, if required.

      [Γ] - context that gets updated when we go under lambda, let, pattern or fixpoint.

      [top,inapp] - flags used to determine how to print parenthesis.

      [t] - a term to be printed.
   *)
  Fixpoint print_term (projs : list (ident * ExAst.one_inductive_body))
                      (prefix : string)
                      (FT : list string)
                      (TT : env string)
                      (Γ : context)
                      (top : bool)
                      (inapp : bool)
                      (t : term) {struct t} :=
  let print_term := print_term projs in
  match t with
  | tBox => "()" (* boxes become the constructor of the [unit] type *)
  | tRel n =>
    match nth_error Γ n with
    | Some {| decl_name := na |} =>
      match na with
      | nAnon => "Anonymous (" ++ string_of_nat n ++ ")"
      | nNamed id => uncapitalize id
      end
    | None => "UnboundRel(" ++ string_of_nat n ++ ")"
    end
  | tVar n => "Var(" ++ n ++ ")"
  | tEvar ev args => "Evar(" ++ string_of_nat ev ++ "[]" (* TODO *) ++ ")"
  | tLambda na body =>
    let na' := fresh_string_name Γ na t in
    parens top ("fun " ++ na'
                       ++ " -> " ++ print_term prefix FT TT (vass (nNamed (s_to_bs na')) :: Γ) true false body)
  | tLetIn na def body =>
    let na' := fresh_string_name Γ na t in
    parens top ("let " ++ na' ++
                      " = " ++ print_term prefix FT TT Γ true false def ++ " in " ++ nl ++
                      print_term prefix FT TT (vdef (nNamed (s_to_bs na')) def :: Γ) true false body)
  | tApp f l =>
    let apps := rev (app_args (print_term prefix FT TT Γ false false) t) in
    let (b,_) := decompose_app f in
    match b with
      (* if the variable corresponds to a fixpoint, we pack the arguments into a tuple *)
    | tRel i =>
      match nth_error Γ i with
      | Some d =>
        let nm := (string_of_name d.(decl_name)) in
        if in_list String.string_dec FT nm
        then parens top (print_uncurried nm apps)
        else parens (top || inapp) (print_term prefix FT TT Γ false true f ++ " " ++ print_term prefix FT TT Γ false false l)
      | None => "UnboundRel(" ++ string_of_nat i ++ ")"
      end
    | tConst c =>
      let cst_name := string_of_kername c in
      let nm := with_default (uncapitalize prefix ++ uncapitalize c.2) (look TT cst_name) in
      if nm =? "fst" then
        (concat " " (map (parens true) apps)) ++ ".(0)"
      else if nm =? "snd" then
        (concat " " (map (parens true) apps)) ++ ".(1)"
      (* check if it is a record projection *)
      else
        match List.find (fun '(na,_) => (bs_to_s na) =? nm) projs with
        | Some (proj_na, oib) =>
          (* check if it's a 1-ind with *)
          if is_one_constructor_inductive_and_not_record oib then
            concat " " (map (parens true) apps)
          else (concat " " (map (parens true) apps)) ++ "." ++ proj_na
        | None => parens (top || inapp) (nm ++ " " ++ (concat " " (map (parens true) apps)))
        end
    | tConstruct ind i [] =>
      let nm := get_constr_name ind i in
      (* is it an natural number literal? *)
      if (nm =? "Z") || (nm =? "S") then
        with_default "Error(Not a natural number literal)" (option_map (fun x => string_of_nat x ++ "p") (nat_syn_to_nat t))
      else
        (* is it an integer number literal? *)
        (* NOTE: we check whether [Z] is remapped to [tez], if so, we add "tz" to the literal *)
        let Z_remapped := with_default "" (look TT (string_of_kername <%% Z %%>)) in
        let units := if (Z_remapped =? "tez") || (Z_remapped =? "dun") then "tz" else "" in
        if (nm =? "Z0") || (nm =? "Zpos") || (nm =? "Zneg") then
          with_default "Error(Not an integer literal)" (option_map (fun x => string_of_Z x ++ units) (Z_syn_to_Z t))
        else
      (* is it a pair ? *)
      if (nm =? "pair") then print_uncurried "" apps
      (* is it a cons ? *)
      else if (nm =? "cons") then
        parens top (concat " :: " apps)
      (* is it a transfer *)
      else if (uncapitalize nm =? "act_transfer") then print_transfer apps
      (* is it a record declaration? *)
          (* if it is an inductive with one constructor, and not a record,
             then it is an alias, so we don't print the constructor *)
      else match lookup_ind_decl ind.(inductive_mind) ind.(inductive_ind) with
      | Some oib => (* Check if it has only 1 constructor, and projections are specified, and > 1 projections *)
                    if is_one_constructor_inductive_and_not_record oib then
                      print_term prefix FT TT Γ false false l
                    else
                      match is_name_remapped nm TT, is_record_constr b projs with
                      | false, Some oib =>
                        let projs : list string := get_record_projs oib in
                        let projs_and_apps := combine projs apps in
                        let field_decls_printed := projs_and_apps |> map (fun '(proj, e) => proj ++ " = " ++ e)
                                                                  |> concat "; " in
                        "{" ++ field_decls_printed ++ "}"
                      | _,_ => let nm' := with_default ((capitalize prefix) ++ nm) (look TT nm) in
                                parens top (print_uncurried nm' apps)
                      end
      | None => let nm' := with_default ((capitalize prefix) ++ nm) (look TT nm) in
                parens top (print_uncurried nm' apps)
      end
    | tConstruct ind l (_ :: _) => "Error(constructors_as_blocks_not_supported)"
    | _ => parens (top || inapp) (print_term prefix FT TT Γ false true f ++ " " ++ print_term prefix FT TT Γ false false l)
    end
  | tConst c =>
    let cst_name := string_of_kername c in
    with_default (prefix ++ c.2) (look TT cst_name)
  | tConstruct ind l [] =>
    (* if it is an inductive with one constructor, and not a record,
       then it is an alias, so we don't print the constructor *)
    match lookup_ind_decl ind.(inductive_mind) ind.(inductive_ind) with
    (* Check if it has only 1 constructor, and projections are specified, and > 1 projections *)
    | Some oib => if is_one_constructor_inductive_and_not_record oib then ""
                  else let nm := get_constr_name ind l in
                       with_default (capitalize prefix ++ capitalize nm) (look TT nm)
    | None =>
      let nm := get_constr_name ind l in
      with_default (capitalize prefix ++ capitalize nm) (look TT nm)
    end
  | tConstruct ind l (_ :: _) => "Error(constructors_as_blocks_not_supported)"
  | tCase (mkInd mind i as ind, nparam) t brs =>
    match brs with
    | [] => "failwith () (* absurd case *)"
    | _ =>
      (* [if-then-else] is a special case *)
      if eq_kername mind <%% bool %%> then
        match brs with
        | [b1; b2] =>
          parens top
                  ("if " ++ print_term prefix FT TT Γ true false t
                         ++ " then " ++ print_term prefix FT TT Γ true false (snd b1)
                         ++ " else " ++ print_term prefix FT TT Γ true false (snd b2))
        | _ => "Error (Malformed pattern-mathing on bool: given "
                 ++ string_of_nat (List.length brs) ++ " branches " ++ ")"
        end
      else match lookup_ind_decl mind i with
           | Some oib =>
               let print_branch ctx (br_ctx : list name) (br_body : term) : list string * string :=
                 let ctx' := map vass br_ctx in
                 let nas' := fresh_string_names (ctx ++ ctx')%list br_ctx in
                 let b := print_term prefix FT TT (fst nas') false false br_body in
                 (List.rev (snd nas'), b)%list in

        (* let fix print_branch Γ arity params br {struct br} := *)
        (*     match arity with *)
        (*       | 0 => (params, print_term prefix FT TT Γ false false br) *)
        (*       | S n => *)
        (*         match br with *)
        (*         | tLambda na B => *)
        (*             let na' := fresh_string_name Γ na br in *)
        (*             let (ps, b) := print_branch (vass (nNamed (s_to_bs na')) :: Γ) n params B in *)
        (*             (ps ++ [na'], b)%list *)
        (*         | t => (params , print_term prefix FT TT Γ false false br) *)
        (*         end *)
        (*       end in *)
        let brs := map (fun '(br_ctx, br) =>
                          print_branch Γ br_ctx br) brs in
        let brs := combine brs oib.(ExAst.ind_ctors) in
        let brs_printed : string :=
          print_list (fun '(b, (na, _, _)) =>
                        (* [list] is a special case *)
                        let na := bs_to_s na in
                        if (eq_kername mind <%% list %%>) && (na =? "cons") then
                          print_pat Γ prefix TT "::" true b
                        else if (eq_kername mind <%% list %%>) && (na =? "nil") then
                               print_pat Γ "" TT "[]" false b
                             else if (eq_kername mind <%% prod %%>) then
                                    "let (" ++ concat "," (rev' b.1) ++ ") = " ++ print_term prefix FT TT Γ true false t ++ " in "
                                            ++ b.2
                                  else
                                    print_pat Γ prefix TT na false b)
                     (nl ++ " | ") brs in
        (* products are unfolded on the spot because pattern matching on pairs is not allowed in liquidity *)
        if eq_kername mind <%% prod %%> then
          parens top brs_printed
        else parens top
               ("match " ++ print_term prefix FT TT Γ true false t
                         ++ " with " ++ nl
                         ++ brs_printed)

      | None =>
        "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
                ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
      end
    end
  | tProj (Kernames.mkProjection (mkInd mind i) pars k) c =>
      let ind := mkInd mind i in
    match lookup_ind_decl mind i with
    | Some oib =>
      match nth_error oib.(ExAst.ind_projs) k with
      | Some (na, _) => (* if it is an inductive with one constructor, and not a record,
                           then it is an alias, so we don't print the projection *)
                        if is_one_constructor_inductive_and_not_record oib then
                          print_term prefix FT TT Γ false false c
                        else print_term prefix FT TT Γ false false c ++ "." ++ na
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ ","
                       ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term prefix FT TT Γ true false c ++ ")"
      end
    | None =>
      "UnboundProj(" ++ string_of_inductive ind ++ ","
                     ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                     ++ print_term prefix FT TT Γ true false c ++ ")"
    end
  | tFix l n =>
    match l with
    | [fix_decl] => (* NOTE: We assume that the fixpoints are not mutual *)
      let fix_name := string_of_name fix_decl.(dname) in
      let body := fix_decl.(dbody) in
      let (args, _) := Edecompose_lam body in
      let sargs := map (fun x => bs_to_s (string_of_name x)) args in
      let fix_call :=
          "fun " ++ concat " " sargs ++ " -> "
                 ++ print_uncurried fix_name sargs in
      let FT' := (bs_to_s fix_name) :: FT in
      parens top ("let rec " ++ print_def (print_term prefix FT' TT) Γ fix_decl ++ nl ++
                             " in " ++ fix_call)
    | [] => "FixWithNoBody"
    | _ => "NotSupportedMutualFix"
    end
  | tCoFix l n => "NotSupportedCoFix"
  | tPrim _ => "NotSupportedCoqPrimitive"
  end.

End print_term.

Fixpoint get_fix_names (t : term) : list BasicAst.name :=
  match t with
  | tEvar _ args => List.concat (map get_fix_names args)
  | tLambda _ b => get_fix_names b
  | tLetIn _ t1 t2 => get_fix_names t1 ++ get_fix_names t2
  | tApp t1 t2 => get_fix_names t1 ++ get_fix_names t2
  | tCase _ t1 brs => get_fix_names t1
                        ++ List.concat (map (get_fix_names ∘ snd) brs)
  | tProj _ t1 => get_fix_names t1
  | tFix mfix _ => map dname mfix ++ List.concat (map (get_fix_names ∘ dbody) mfix)
  | tCoFix mfix _ => map dname mfix ++ List.concat (map (get_fix_names ∘ dbody) mfix)
  | _ => []
  end.

Definition print_decl (prefix : string)
           (TT : env string) (* translation table *)
           (Σ : ExAst.global_env)
           (projs : list (Kernames.ident * ExAst.one_inductive_body))
           (decl_name : string)
           (modifier : option string)
           (wrap : string -> string)
           (ty : list BasicAst.name * box_type)
           (t : term) :=
  let (tys,_) := decompose_arr ty.2 in
  let (args,lam_body) := Edecompose_lam t in
  let (ctx, args) := fresh_string_names [] args in
  let targs := combine args (map (print_box_type prefix TT ty.1) tys) in
  let printed_targs :=
      map (fun '(x,ty) => parens false (uncapitalize x ++ " : " ++ ty)) targs in
  let decl := uncapitalize prefix ++ uncapitalize decl_name ++ " " ++ concat " " printed_targs in
  let modif := match modifier with
               | Some m => "%"++m
               | None => ""
               end in
  "let" ++ modif ++ " " ++ decl ++ " = "
        ++ wrap (LiquidityPretty.print_term Σ projs prefix [] TT ctx true false lam_body).

Definition print_init (prefix : string)
          (* tranlation table *)
           (TT : env string)
           (* record projections and the record names they project *)
           (projs : list (Kernames.ident * ExAst.one_inductive_body))
           (* a string that corresponds to a call context *)
           (build_call_ctx : string)
           (* operations available in the [init] as local definitions.
              Liquidity does not allow referring to global definitions in [init]*)
           (init_prelude : string)
           (Σ : ExAst.global_env)
           (cst : ExAst.constant_body) : option string :=
  b <- cst.(ExAst.cst_body) ;;
  let ty := cst.(ExAst.cst_type) in
  let (tys,_) := decompose_arr ty.2 in
  let (args,lam_body) := Edecompose_lam b in
  let targs_inner := combine args (map (print_box_type prefix TT ty.1) tys) in
  let printed_targs_inner :=
      map (fun '(x,ty) => parens false ((bs_to_s (BasicAst.string_of_name x)) ^ " : " ^ ty)) targs_inner in
  let decl_inner := "inner " ++ concat " " printed_targs_inner in
  let ctx := map (fun x => Build_context_decl x None) (rev args) in
  let wrap t := "match " ++ t ++ " with Ok v -> v | Err e -> failwith e" in
  let let_inner :=
      "let " ++ decl_inner ++ " = "
             ++ LiquidityPretty.print_term Σ projs prefix [] TT ctx true false lam_body
             ++ " in" in
  (* ignore the first argument because it's a call context *)
  let printed_targs_outer := tl printed_targs_inner in
  let decl_outer := "storage " ++ concat " " printed_targs_outer in
  let let_ctx := "let ctx = " ++ build_call_ctx ++ " in" in
  let inner_app := "inner " ++ concat " " ( "ctx" :: map (fun x => bs_to_s (BasicAst.string_of_name x)) (tl args)) in
  ret ("let%init " ++ decl_outer ++ " = "
                   ++ init_prelude
                   ++ nl
                   ++ let_inner
                   ++ nl
                   ++ let_ctx
                   ++ nl
                   ++ wrap (parens false inner_app)).


Definition print_cst (prefix : string)
           (TT : env string) (* translation table *)
           (Σ : ExAst.global_env)
           (kn : Kernames.kername)
           (cst : ExAst.constant_body)
           (projs : list (Kernames.ident * ExAst.one_inductive_body))
           : string :=
  match cst.(ExAst.cst_body) with
  | Some cst_body =>
    (* NOTE: ignoring the path part *)
    let (_, decl_name) := kn in
    print_decl prefix TT Σ projs decl_name None id cst.(ExAst.cst_type) cst_body
  | None => ""
  end.

Definition print_global_decl (prefix : string) (TT : env string)
           (nm : Kernames.kername)
           (Σ : ExAst.global_env)
           (d : ExAst.global_decl)
           (projs : list (Kernames.ident * ExAst.one_inductive_body))
           : Kernames.kername * string :=
  match d with
  | ExAst.ConstantDecl cst =>
      (* don't print record projection definitions *)
      if List.existsb (fun p => bytestring.String.eqb nm.2 p.1) projs
      then (nm, "")
      (* (nm, "projs: " ++ nm.2 ++ " : " ++ String.concat ";" (map fst projs )) *)
      else
      (nm, print_cst prefix TT Σ nm cst projs)
  | ExAst.InductiveDecl mib =>
    match mib.(ExAst.ind_bodies) with
    | [oib] => (nm, print_inductive prefix TT oib)
    | _ => (nm,"Only non-mutual inductives are supported")
    end
  | TypeAliasDecl (Some (params, ty)) =>
    let ta_nm := with_default (prefix ++ nm.2) (lookup TT (Kernames.string_of_kername nm)) in
    (nm, "type " ++ parens (Nat.ltb #|params| 1) (concat "," (mapi (fun i v => print_type_var v.(tvar_name) i) params))
                 ++ " " ++ uncapitalize ta_nm
                 ++ " = "
            ++ print_box_type prefix TT (map tvar_name params) ty)
  | TypeAliasDecl None => (nm, "")
  end.

Fixpoint print_global_env (prefix : string) (TT : env string)
           (Σ : ExAst.global_env)
           (projs : list (Kernames.ident * ExAst.one_inductive_body))
           : list (Kernames.kername * string) :=
  match Σ with
  | (kn, has_deps, decl) :: Σ' =>
    let printed :=
        (* only print decls for which the environment includes dependencies *)
        if has_deps then
          print_global_decl prefix TT kn Σ' decl projs
        else
          (kn, "") in
    printed :: print_global_env prefix TT Σ' projs
  | [] => []
  end.


Local Open Scope string_scope.

(** We un-overload operations and add definitions that are more convenient
    to use during the pretty-printing phase. These part should be included
    when printing contracts that use the corresponding operations. *)

Definition prod_ops :=
       "let[@inline] fst (p : 'a * 'b) : 'a = p.(0)"
    ++ nl
    ++ "let[@inline] snd (p : 'a * 'b) : 'b = p.(1)".

Definition int_ops :=
       "let[@inline] addInt (i : int) (j : int) = i + j"
    ++ nl
    ++ "let[@inline] mulInt (i : int) (j : int) = i * j"
    ++ nl
    ++ "let[@inline] subInt (i : int) (j : int) = i - j"
    ++ nl
    ++ "let[@inline] leInt (i : int) (j : int) = i <= j"
    ++ nl
    ++ "let[@inline] ltInt (i : int) (j : int) = i < j"
    ++ nl
    ++ "let[@inline] eqInt (i : int) (j : int) = i = j"
    ++ nl
    ++ "let[@inline] modInt(a : int)(b : int) : int = match a/b with | Some (_, r) -> int r | None -> 0"
    ++ nl
    ++ "let rec powIntAcc((a,b,acc) : int*int*int) =
        if b <= 0 then acc
        else powIntAcc(a, (b-1), acc * a)"
    ++ nl
    ++ "let powInt(a : int)(b : int) = powIntAcc(a,b,1)".

Definition tez_ops :=
       "let[@inline] addTez (n : tez) (m : tez) = n + m"
    ++ nl
    ++ "let[@inline] subTez (n : tez) (m : tez) = n - m"
    ++ nl
    ++ "let[@inline] leTez (a : tez ) (b : tez ) = a <= b"
    ++ nl
    ++ "let[@inline] ltTez (a : tez ) (b : tez ) = a < b"
    ++ nl
    ++ "let[@inline] gtTez (a : tez ) (b : tez ) = a > b"
    ++ nl
    ++ "let[@inline] eqTez (a : tez ) (b : tez ) = a = b"
    ++ nl
    ++ "let[@inline] evenTez (i : tez) = match i/2tz with | Some (_, r) -> r=0tz | None -> false"
    ++ nl
    ++ "let tez_to_nat (a : tez) : nat =" ++ nl
    ++ "let (n, _) = match a / 1DUN with" ++ nl
    ++ "| Some qr -> qr" ++ nl
    ++ "| None -> failwith () (* impossible case *)" ++ nl
    ++ "in n"
    ++ nl
    ++ "let[@inline] divTez (a : tez) (b : tez) : tez = match a/(tez_to_nat b) with Some(d,_) -> d | None -> 0tz"
    ++ nl
    ++ "let[@inline] multTez (n : tez) (m : tez) : tez = n * tez_to_nat m".


Definition nat_ops :=
      "let[@inline] addNat (i : nat) (j : nat) = i + j"
    ++ nl
    ++ "let[@inline] mulNat (i : nat) (j : nat) = i * j"
    ++ nl
    ++ "let[@inline] subNat (i : nat) (j : nat) = i - j"
    ++ nl
    ++ "let[@inline] leNat (i : nat) (j : nat) = i <= j"
    ++ nl
    ++ "let[@inline] ltNat (i : nat) (j : nat) = i < j"
    ++ nl
    ++ "let[@inline] lxorNat (i : nat) (j : nat) = i lxor j"
    ++ nl
    ++ "let[@inline] eqNat (i : nat) (j : nat) = i = j".

Definition bool_ops :=
     "let[@inline] andb (a : bool ) (b : bool ) = a & b"
  ++ nl
  ++ "let[@inline] orb (a : bool ) (b : bool ) = a || b".

Definition time_ops :=
       "let[@inline] eqb_time (a1 : timestamp) (a2 : timestamp) = a1 = a2"
    ++ nl
    ++ "let[@inline] leb_time (a1 : timestamp) (a2 : timestamp) = a1 <= a2"
    ++ nl
    ++ "let[@inline] ltb_time (a1 : timestamp) (a2 : timestamp) = a1 < a2".

Definition address_ops :=
  "let[@inline] eq_addr (a1 : address) (a2 : address) = a1 = a2".


Definition address_map :=
  "type 'a addrMap = (address, 'a) map".

Definition false_elim_decl :=
  "let false_elim (_ : unit) = failwith ()".

Definition result_def :=
  <$
    "type ('t,'e) result ="
  ; "  Ok of 't"
  ; "| Err of 'e"
  $>.

Definition LiquidityPrelude :=
  print_list id (nl ++ nl)
             [prod_ops; int_ops; tez_ops; nat_ops;
             bool_ops; time_ops; address_ops;
             address_map; result_def].

Definition printWrapper (contract : string): string :=
  "let wrapper param (st : storage)"
        ++ " = "
        ++ "match " ++ contract ++ " param st" ++ " with"
        ++ "| Ok v -> v"
        ++ "| Err e -> failwith e".

Definition printMain :=
  "let%entry main param st = wrapper param st".
