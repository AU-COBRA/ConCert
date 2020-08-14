(** * Pretty-printing Liquidity code *)
(** Adapted from [EPretty] of MetaCoq.Erasure. *)

(** ** Features/limitations *)

(** Printing covers most constructs of CIC_box (terms after erasure). Usually we have to remove redundant boxes before printing. There are some limitations on what can work after extraction, due to the nature of Liquidity, or some times, lack of proper support.

Liquidity allows only tail-recursive calls and recursive functions must have only one argument. So, we pack multiple arguments in a tuple. In order for that to be correct, we assume that all fixpoints are fully applied.

Another issue (mostly solved): constructors accept only one argument, so we have to uncurry (pack in a tuple) applications as well. This transformation is applied to all constructors and the pretty-printing stage. Again, we assume that the constructors are fully applied (e.g. eta-expanded at the previous stage).

Pattern-macthing: pattern-matching on pairs is not supported by Liquidity, so all the programs must use projections.

Records are currently not supported. Should be represented as iterated products.

Printing polymoprhic definitions is not supported currently (due to the need of removing redundant types from the type scheme). But the machinery is there, just need to switch to erased types. *)

From Coq Require Import List Program String Ascii.
From ConCert.Extraction Require Import StringExtra ExAst Common.
From ConCert.Embedding Require Import MyEnv Ast.
From MetaCoq.Template Require Import utils Loader Environment.
From MetaCoq.Template Require Pretty.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Erasure Require Import EAst EAstUtils ETyping EPretty.

Import monad_utils.MonadNotation.
Local Open Scope string_scope.

Section print_term.
  Context (Σ : ExAst.global_env).

  Definition look (e : MyEnv.env string) (s : string) : option string :=
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

  Eval lazy in (tokenize "." "Coq.ZArith.BinInt.Z.add").

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

  Definition map_targs (f : box_type -> string) :  box_type -> list string
    := fix go bt := match bt with
                    | TApp t1 t2 => (go t1 ++ [f t2])%list
                    | _ => []
                    end.

  Fixpoint get_tapp_hd (bt : box_type) : box_type :=
    match bt with
    | TApp t1 t2 => get_tapp_hd t1
    | _ => bt
    end.

  Definition print_box_type (prefix : string) (TT : env string)
    : box_type -> string :=
    fix go  (bt : box_type) :=
  match bt with
  | TBox => "Box"
  | TArr dom codom => parens (negb (is_arr dom)) (go dom) ++ " → " ++ go codom
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
  | TVar i => "'a" ++ string_of_nat i (* TODO: pass context with type variables *)
  | TInd s =>
    let full_ind_name := string_of_kername s.(inductive_mind) in
    uncapitalize (from_option (look TT full_ind_name) (prefix ++ s.(inductive_mind).2))
  | TConst s =>
    let full_cst_name := string_of_kername s in
    uncapitalize (from_option (look TT full_cst_name) (prefix ++ s.2))

  | TAny => "UnknownType"
  end.

  Compute print_box_type "" []
          (TApp (TApp (TInd (mkInd <%% prod %%> 0)) (TVar 0)) (TVar 1)).

  Compute print_box_type "" []
          (TApp (TApp (TApp (TApp (TInd (mkInd (MPfile [], "list") 0)) (TVar 0)) (TVar 1)) (TVar 2))(TVar 3)).


  Definition print_ctor (prefix : string) (TT : env string) (ctor : ident × list box_type) :=
    let (nm,tys) := ctor in
    match tys with
    | [] => prefix ++ nm
    | _ => prefix ++ nm ++ " of "
                  ++ concat " * " (map (print_box_type prefix TT) tys)
    end.

  Compute print_ctor "" []
          ("blah",[TInd (mkInd (MPfile [], "nat") 0);
                  (TApp (TApp (TInd (mkInd <%% prod %%> 0)) (TVar 0)) (TVar 1))]).

  Definition print_inductive (prefix : string) (TT : env string)
             (oib : ExAst.one_inductive_body) :=
    let ind_nm := from_option (lookup TT oib.(ExAst.ind_name))
                              (prefix ++ oib.(ExAst.ind_name)) in
    let print_type_var (i : nat) :=
        "'a" ++ string_of_nat i in
    let params :=
        if (Nat.eqb #|oib.(ind_type_vars)| 0) then ""
        else let ps := concat "," (mapi (fun i _ => print_type_var i) oib.(ind_type_vars)) in
             (parens (Nat.eqb #|oib.(ind_type_vars)| 1) ps) ++ " " in
    "type " ++ params ++ uncapitalize ind_nm ++" = "
            ++ nl
            ++ concat "| " (map (fun p => print_ctor (capitalize prefix) TT p ++ nl) oib.(ExAst.ind_ctors)).

  Fixpoint print_liq_type (prefix : string) (TT : env string) (t : Ast.term) :=
  let error := "Error (not_supported_type " ++ Pretty.print_term (Ast.empty_ext []) [] true t ++ ")" in
  match t with
  | Ast.tInd ind _ =>
    let nm := string_of_kername ind.(inductive_mind) in
    from_option (look TT nm) (prefix ++ ind.(inductive_mind).2)
  | Ast.tApp (Ast.tInd ind _) [t1;t2] =>
    (* a special case of products - infix *)
    if eq_kername <%% prod %%> ind.(inductive_mind) then
      parens false (print_liq_type prefix TT t1 ++ " * " ++ print_liq_type prefix TT t2)
      else error
  | Ast.tApp (Ast.tInd ind i) args =>
    (* the usual - postfix - case of an applied type constructor *)
    let nm := string_of_kername ind.(inductive_mind) in
    let nm' := from_option (look TT nm) (prefix ++ ind.(inductive_mind).2) in
    let printed_args := map (print_liq_type prefix TT) args in
    (print_uncurried "" printed_args) ++ " " ++ nm'
  | Ast.tApp (Ast.tConst nm _) args =>
    (* similarly we do for constants to enable remapping of aliases to types *)
    let cst_nm := string_of_kername nm in
    let nm' := from_option (look TT cst_nm) (prefix ++ nm.2) in
    let printed_args := map (print_liq_type prefix TT) args in
    (print_uncurried "" printed_args) ++ " " ++ nm'
  | Ast.tConst nm _ =>
    let cst_nm := string_of_kername nm in
    from_option (look TT cst_nm) (prefix ++ nm.2)
  | _ => error
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

  Fixpoint Edecompose_lam (t : term) : (list name) × term :=
  match t with
  | tLambda n b =>
      let (ns, b) := Edecompose_lam b in
      (n :: ns, b)
  | _ => ([], t)
  end.


  (* NOTE: This is more fixpoint-friendly definition, using [Edecompose_lam] doesn't work well with print_def calls, because we pass print_term to [print_defs] and this is sensitive to how the decreasing argument is determined *)
  Fixpoint lam_body (t : term) : term :=
    match t with
    | tLambda n b => lam_body b
    | _ => t
    end.

    Definition print_def (print_term : context -> bool -> bool -> term -> string) (Γ : context) (fdef : def  term) :=
      let ctx' := [{| decl_name := dname fdef; decl_body := None |}] in
      let fix_name := string_of_name (fdef.(dname)) in
      let (args, _) := Edecompose_lam (fdef.(dbody)) in
      let ctx := rev (map vass args) in
      let sargs := print_uncurried "" (map (fun x => string_of_name x) args) in
      string_of_name fdef.(dname)
          ++ " " ++ sargs  ++ " = "
          ++ nl
          ++ print_term (ctx ++ ctx' ++ Γ)%list true false (lam_body fdef.(dbody)).

  Definition lookup_ind_decl ind i :=
    match ExAst.lookup_env Σ ind with
    | Some (ExAst.InductiveDecl _ {| ExAst.ind_bodies := l |}) =>
      match nth_error l i with
      | Some body => Some body
      | None => None
      end
    | _ => None
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

  Definition get_constr_name (ind : inductive) (i : nat) :=
    match lookup_ind_decl ind.(inductive_mind) ind.(inductive_ind) with
    | Some oib =>
      match nth_error oib.(ExAst.ind_ctors) i with
      | Some (na, _) => na
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

  Definition is_list_cons (ind : inductive) (ctor_num : nat):=
    andb (eq_kername ind.(inductive_mind) <%% list %%>)
         (Nat.eqb ctor_num 1).

  Definition print_list_cons (f : term -> string) (t1 : term) (t2 : term) :=
    (f t1) ++ " :: " ++ (f t2).

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
        let na' := fresh_name Γ na branch in
        go (vass na' :: ctx) n B
      | t => []
      end
    end
    in go [].

  Definition print_pat (prefix : string) (TT : env string) (ctor : string) (pt : list string * string) :=
    let ctor_nm := from_option (look TT ctor) ((capitalize prefix) ++ ctor) in
    let print_parens := (Nat.ltb 1 (List.length pt.1)) in
    print_uncurried ctor_nm (rev pt.1) ++ " -> " ++ pt.2.


  Definition print_transfer (args : list string) :=
    match args with
    | [] => "MalformedTransfer()"
    | [a1;a2] => "Contract.call " ++ a1 ++ " " ++ a2 ++ " "
                                 ++ "default" ++ " ()"
    | _ => "MalformedTransfer(" ++ concat "," args ++ ")"
    end.

  (** ** The pretty-printer *)

  (** [prefix] - a sting pre-pended to the constants' and constructors' names to avoid clashes
      [FT] - list of fixpoint names. Used to determine if uncurrying is needed for an applied variable (if it corresponds to a recursive call). The initial value is an empty list. Once we fit a fixpoint case, we add the fixpoint name to [FT], so all the recursive calls in the fixpoint body are packed into a tuple.

      [TT] - translation table allowing for remapping constants and constructors to Liquidity primitives, if required.

      [Γ] - context that gets updated when we go under lambda, let, pattern or fixpoint.

      [top,inapp] - flags used to determine how to print parenthesis.

      [t] - a term to be printed.
   *)
  Fixpoint print_term (prefix : string) (FT : list string) (TT : env string) (Γ : context) (top : bool) (inapp : bool) (t : term) {struct t} :=
  match t with
  | tBox => "()" (* boxes become the contructor of the [unit] type *)
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
                       ++ " -> " ++ print_term prefix FT TT (vass na' :: Γ) true false body)
  | tLetIn na def body =>
    let na' := fresh_name Γ na t in
    parens top ("let " ++ string_of_name na' ++
                      " = " ++ print_term prefix FT TT Γ true false def ++ " in " ++ nl ++
                      print_term prefix FT TT (vdef na' def :: Γ) true false body)
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
      let nm := from_option (look TT cst_name) (prefix ++ c.2) in
      parens (top || inapp) (nm ++ " " ++ (concat " " (map (parens true) apps)))
    | tConstruct ind i =>
      let nm := get_constr_name ind i in
      (* is it a pair ? *)
      if (nm =? "pair") then print_uncurried "" apps
      else
      (* is it a cons ? *)
        if (nm =? "cons") then
          parens top (concat " :: " apps)
        else
      (* is it a transfer *)
          if (nm =? "Act_transfer") then print_transfer apps
          else
            let nm' := from_option (look TT nm) ((capitalize prefix) ++ nm) in
            parens top (print_uncurried nm' apps)
    | _ =>  parens (top || inapp) (print_term prefix FT TT Γ false true f ++ " " ++ print_term prefix FT TT Γ false false l)
    end
  | tConst c =>
    let cst_name := string_of_kername c in
    from_option (look TT cst_name) (prefix ++ c.2)
  | tConstruct ind l =>
    let nm := get_constr_name ind l in
    from_option (look TT nm) ((capitalize prefix) ++ nm)
  | tCase (mkInd mind i as ind, nparam) t brs =>
    (* [if-then-else] is a special case *)
    if eq_kername mind <%% bool %%> then
      match brs with
      | [b1;b2] =>
        parens top
                ("if " ++ print_term prefix FT TT Γ true false t
                       ++ " then " ++ print_term prefix FT TT Γ true false (snd b1)
                       ++ " else " ++ print_term prefix FT TT Γ true false (snd b2))
      | _ => "Error (Malformed pattern-mathing on bool: given "
               ++ string_of_nat (List.length brs) ++ " branches " ++ ")"
      end
    else
      (* [list] is a special case *)
      if eq_kername mind <%% list %%> then
        match brs with
        | [b1;b2] =>
          let nil_case := "[] -> " ++ print_term prefix FT TT Γ false false b1.2 in
          let (cons_args, _) := Edecompose_lam b2.2 in
          let cons_body := lam_body b2.2 in
          let cons_pat := concat " :: " (map (fun x => string_of_name (fresh_name Γ x b2.2)) cons_args) in
          let cons_ctx := rev (map vass cons_args) in
          let cons_case := cons_pat ++ " -> " ++ print_term prefix FT TT (cons_ctx ++ Γ)%list false false cons_body in
          parens top
             ("match " ++ print_term prefix FT TT Γ true false t
                       ++ " with " ++ nl
                       ++ concat (nl ++ " | ") [nil_case;cons_case])
        | _ => "Error (Malformed pattern-mathing on bool: given "
                ++ string_of_nat (List.length brs) ++ " branches " ++ ")"
        end
      else
    match lookup_ind_decl mind i with
    | Some oib =>
      (* TODO: use [print_branch] to cover the special case of lists *)
      let fix print_branch Γ arity params br {struct br} :=
          match arity with
            | 0 => (params, print_term prefix FT TT Γ false false br)
            | S n =>
              match br with
              | tLambda na B =>
                  let na' := fresh_name Γ na br in
                  let (ps, b) := print_branch (vass na' :: Γ) n params B in
                  (ps ++ [string_of_name na'], b)%list
              | t => (params , print_term prefix FT TT Γ false false br)
              end
            end in
      let brs := map (fun '(arity, br) =>
                        print_branch Γ arity [] br) brs in
      let brs := combine brs oib.(ExAst.ind_ctors) in
      parens top
             ("match " ++ print_term prefix FT TT Γ true false t
                       ++ " with " ++ nl
                       ++ print_list (fun '(b, (na, _)) =>
                                        print_pat prefix TT na b)
                       (nl ++ " | ") brs)
    | None =>
      "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
              ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
    end
  | tProj (mkInd mind i as ind, pars, k) c =>
    (*NOTE: since records are not supported, projections are not very meaningful, curretnly*)
    match lookup_ind_decl mind i with
    | Some oib =>
      match nth_error oib.(ExAst.ind_projs) k with
      | Some (na, _) => print_term prefix FT TT Γ false false c ++ ".(" ++ na ++ ")"
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term prefix FT TT Γ true false c ++ ")"
      end
    | None =>
      "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                     ++ print_term prefix FT TT Γ true false c ++ ")"
    end
  | tFix l n =>
    match l with
    | [fix_decl] => (* NOTE: We assume that the fixpoints are not mutual *)
      let fix_name := string_of_name fix_decl.(dname) in
      let body := fix_decl.(dbody) in
      let (args, _) := Edecompose_lam body in
      let sargs := map string_of_name args in
      let fix_call :=
          "fun " ++ concat " " sargs ++ " -> "
                 ++ print_uncurried fix_name sargs in
      let FT' := fix_name :: FT in
      parens top ("let rec " ++ print_def (print_term prefix FT' TT) Γ fix_decl ++ nl ++
                             " in " ++ fix_call)
    | [] => "FixWithNoBody"
    | _ => "NotSupportedMutualFix"
    end
  | tCoFix l n => "NotSupportedCoFix"
  end.

End print_term.

Fixpoint get_fix_names (t : term) : list name :=
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
           (TT : MyEnv.env string) (* tranlation table *)
           (Σ : ExAst.global_env)
           (decl_name : string)
           (modifier : option string)
           (wrap : string -> string)
           (ty : box_type)
           (t : term) :=
  let (tys,_) := decompose_arr ty in
  let (args,lam_body) := Edecompose_lam t in
  let targs := combine args (map (print_box_type prefix TT) tys) in
  let printed_targs :=
      map (fun '(x,ty) => parens false (string_of_name x ++ " : " ++ ty)) targs in
  let decl := prefix ++ decl_name ++ " " ++ concat " " printed_targs in
  let ctx := map (fun x => Build_context_decl x None) (rev args) in
  let modif := match modifier with
               | Some m => "%"++m
               | None => ""
               end in
  "let" ++ modif ++ " " ++ decl ++ " = "
        ++ wrap (LPretty.print_term Σ prefix [] TT ctx true false lam_body).

Definition print_init (prefix : string)
           (TT : MyEnv.env string) (* tranlation table *)
           (build_call_ctx : string) (* a string that corresponds to a call contex *)
           (init_prelude : string) (* operations available in the [init] as local definitions.
                                      Liquidity does not allow to refer to global definitions in [init]*)
           (Σ : ExAst.global_env)
           (cst : ExAst.constant_body) : option string :=
  b <- cst.(ExAst.cst_body) ;;
  let ty := cst.(ExAst.cst_type) in
  let (tys,_) := decompose_arr ty.2 in
  let (args,lam_body) := Edecompose_lam b in
  let targs_inner := combine args (map (print_box_type prefix TT) tys) in
  let printed_targs_inner :=
      map (fun '(x,ty) => parens false (string_of_name x ++ " : " ++ ty)) targs_inner in
  let decl_inner := "inner " ++ concat " " printed_targs_inner in
  let ctx := map (fun x => Build_context_decl x None) (rev args) in
  let wrap t := "match " ++ t ++ " with Some v -> v | None -> failwith ()" in
  let let_inner :=
      "let " ++ decl_inner ++ " = "
             ++ LPretty.print_term Σ prefix [] TT ctx true false lam_body
             ++ " in" in
  (* ignore the first argument because it's a call context *)
  let printed_targs_outer := tl printed_targs_inner in
  let decl_outer := "storage " ++ concat " " printed_targs_outer in
  let let_ctx := "let ctx = " ++ build_call_ctx ++ " in" in
  let inner_app := "inner " ++ concat " " ( "ctx" :: map string_of_name (tl args)) in
  ret ("let%init " ++ decl_outer ++ " = "
                   ++ init_prelude
                   ++ nl
                   ++ let_inner
                   ++ nl
                   ++ let_ctx
                   ++ nl
                   ++ wrap (parens false inner_app)).


Definition print_cst (prefix : string)
           (TT : MyEnv.env string) (* tranlation table *)
           (Σ : ExAst.global_env)
           (kn : kername)
           (cst : ExAst.constant_body) : string :=
  match cst.(ExAst.cst_body) with
  | Some cst_body =>
    (* NOTE: ignoring the path part *)
    let (_, decl_name) := kn in
    print_decl prefix TT Σ decl_name None id cst.(ExAst.cst_type).2 cst_body
  | None => ""
  end.

Definition print_global_decl (prefix : string) (TT : MyEnv.env string)
           (nm : kername)
           (Σ : ExAst.global_env)
           (d : ExAst.global_decl) : kername * string :=
  match d with
  | ExAst.ConstantDecl cst =>
      (nm, print_cst prefix TT Σ nm cst)
  | ExAst.InductiveDecl ignore mib =>
    if ignore then (nm,"") else
    match mib.(ExAst.ind_bodies) with
    | [oib] => (nm, print_inductive prefix TT oib)
    | _ => (nm,"Only non-mutual inductives are supported")
    end
  | TypeAliasDecl (params, ty) =>
    let ta_nm := from_option (lookup TT (string_of_kername nm))
                             (prefix ++ nm.2) in
    (nm, "type " ++ uncapitalize ta_nm ++ concat " " (map string_of_name params) ++  " = "
            ++ print_box_type prefix TT ty)
  end.

Fixpoint print_global_env (prefix : string) (TT : MyEnv.env string)
           (Σ : ExAst.global_env) : list (kername * string) :=
  match Σ with
  | (kn,decl) :: Σ' =>
    print_global_decl prefix TT kn Σ' decl :: print_global_env prefix TT Σ'
  | [] => []
  end.


Local Open Scope string_scope.

(** We un-overload operations and add definitions that are more convenient to use during the pretty-printing phase. These part should be included when printing contracts that use the corresponding operations. *)

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
