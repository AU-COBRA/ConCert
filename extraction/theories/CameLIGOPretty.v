(** * Pretty-printing CameLIGO code *)
(** Adapted from [EPretty] of MetaCoq.Erasure. *)

(** ** Features/limitations *)

(** Printing covers most constructs of CIC_box (terms after erasure). Usually we have to remove redundant boxes before printing. There are some limitations on what can work after extraction, due to the nature of CameLIGO, or some times, lack of proper support.

CameLIGO allows only tail-recursive calls and recursive functions must have only one argument. So, we pack multiple arguments in a tuple. In order for that to be correct, we assume that all fixpoints are fully applied.

Another issue (mostly solved): constructors accept only one argument, so we have to uncurry (pack in a tuple) applications as well. This transformation is applied to all constructors and the pretty-printing stage. Again, we assume that the constructors are fully applied (e.g. eta-expanded at the previous stage).

TODO: CHECK THIS FOR CAMELIGO
Pattern-macthing: pattern-matching on pairs is not supported by CameLIGO, so all the programs must use projections.

TODO: RECORDS ARE SUPPORTED IN CAMELIGO
Records are currently not supported. Should be represented as iterated products.

TODO:REWRITE
Printing polymoprhic definitions is not supported currently (due to the need of removing redundant types from the type scheme). But the machinery is there, just need to switch to erased types. *)

From Coq Require Import List Program String Ascii.
From ConCert.Extraction Require Import Aux StringExtra ExAst Common.
From ConCert.Extraction Require Import Annotations.
From ConCert.Extraction Require Import TypeAnnotations.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Extraction.
From ConCert.Embedding Require Import MyEnv Ast.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Erasure Require Import EAst EAstUtils.

Import monad_utils.MonadNotation.
Local Open Scope string_scope.
Import String.

(* F# style piping notation *)
Notation "f <| x" := (f x) (at level 32, left associativity, only parsing).
(* i.e. f <| x <| y = (f <| x) <| y, and means (f x) y *)
Notation "x |> f" := (f x) (at level 31, left associativity, only parsing).
(* i.e. x |> f |> g = (x |> f) |> g, and means g (f x) *)


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
  | TArr dom codom => parens (negb (is_arr dom)) (go dom) ++ " -> " ++ go codom
  | TApp t1 t2 =>
    let hd := get_tapp_hd t1 in
    let args := map_targs go bt in
    match hd with
    | TInd ind =>
      (* a special case of products - infix *)
      if eq_kername <%% prod %%> ind.(inductive_mind) then
        parens false (concat " * " args)
      
      (* inductives are printed with args prefix style, e.g. "int option" *)
      else print_uncurried "" args ++ " " ++ go hd
    | _ => print_uncurried "" args ++ " " ++ go hd
    end
  | TVar i => "a" ++ string_of_nat i (* TODO: pass context with type variables *)
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
                  ++ parens false <| concat " * " (map (print_box_type prefix TT) tys)
    end.

  Compute print_ctor "" []
          ("blah",[TInd (mkInd (MPfile [], "nat") 0);
                  (TApp (TApp (TInd (mkInd <%% prod %%> 0)) (TVar 0)) (TVar 1))]).

  Definition print_inductive (prefix : string) (TT : env string)
             (oib : ExAst.one_inductive_body) :=
    let ind_nm := from_option (lookup TT oib.(ExAst.ind_name))
                              (prefix ++ oib.(ExAst.ind_name)) in
    let print_type_var (i : nat) :=
        "a_" ++ string_of_nat i in
    let params :=
        if (Nat.eqb #|oib.(ind_type_vars)| 0) then ""
        else let ps := concat "," (mapi (fun i _ => print_type_var i) oib.(ind_type_vars)) in
             (parens (Nat.eqb #|oib.(ind_type_vars)| 1) ps) ++ " " in
    "type " ++ params ++ uncapitalize ind_nm ++" = "
            ++ nl
            ++ concat "| " (map (fun p => print_ctor (capitalize prefix) TT p ++ nl) oib.(ExAst.ind_ctors)).

  
  Fixpoint print_ligo_type (prefix : string) (TT : env string) (t : Ast.term) :=
  let error := "Error (not_supported_type " ++ Pretty.print_term (Ast.empty_ext []) [] true t ++ ")" in
  match t with
  | Ast.tInd ind _ =>
    let nm := string_of_kername ind.(inductive_mind) in
    from_option (look TT nm) (prefix ++ ind.(inductive_mind).2)
  | Ast.tApp (Ast.tInd ind _) [t1;t2] =>
    (* a special case of products - infix *)
    if eq_kername <%% prod %%> ind.(inductive_mind) then
      parens false (print_ligo_type prefix TT t1 ++ " * " ++ print_ligo_type prefix TT t2)
      else error
  | Ast.tApp (Ast.tInd ind i) args =>
    (* the usual - postfix - case of an applied type constructor *)
    let nm := string_of_kername ind.(inductive_mind) in
    let nm' := from_option (look TT nm) (prefix ++ ind.(inductive_mind).2) in
    let printed_args := map (print_ligo_type prefix TT) args in
    (print_uncurried "" printed_args) ++ " " ++ nm'
  | Ast.tApp (Ast.tConst nm _) args =>
    (* similarly we do for constants to enable remapping of aliases to types *)
    let cst_nm := string_of_kername nm in
    let nm' := from_option (look TT cst_nm) (prefix ++ nm.2) in
    let printed_args := map (print_ligo_type prefix TT) args in
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

  Fixpoint Edecompose_lam_annot {A} (t : term) : (annots A t) -> (list name) × (∑t, annots A t) :=
    match t return annots A t -> (list name) × (∑t, annots A t) with
    | tLambda n b => fun '(bt, a) =>
        let '(ns, (b; a)) := Edecompose_lam_annot b a  in
        (n :: ns, (b; a))
    | t => fun bt => ([], (t; bt))
    end.
  

  (* NOTE: This is more fixpoint-friendly definition, using [Edecompose_lam] doesn't work well with print_def calls, because we pass print_term to [print_defs] and this is sensitive to how the decreasing argument is determined *)
  Fixpoint lam_body (t : term) : term :=
    match t with
    | tLambda n b => lam_body b
    | _ => t
    end.


  Section lam_body_annot_cont.
  Context {A B : Type}.
  Context (f : forall t, annots A t -> B).
  Fixpoint lam_body_annot_cont (t : term) (a : annots A t) : B :=
    match t return annots A t -> B with
    | tLambda na b => fun '(_, ba) => lam_body_annot_cont b ba
    | _ => fun _ => f t a
    end a.
  End lam_body_annot_cont.

  (* Section print_branch.
  Context {A B : Type}.
  Context (f : forall t, annots A t -> B).
  Fixpoint print_branch ctx arity params (br : term) : annots A br -> (_ * B) :=      
  match br return annots A br -> (_ * B) with
  | tLambda na B as br => fun bt => 
    match arity with
    | S n =>
      let '(bt, a) := bt in
      let na' := fresh_name ctx na br in
      let (ps, b) := print_branch (vass na' :: ctx) n params B a in
      (ps ++ [string_of_name ctx na'], b)%list
    | 0 => (params , f br bt)
    end
  | t => fun btt => (params , f t btt)
  end.
  End print_branch. *)

  Definition lookup_ind_decl ind i :=
    match ExAst.lookup_env Σ ind with
    | Some (ExAst.InductiveDecl {| ExAst.ind_bodies := l |}) =>
      match nth_error l i with
      | Some body => Some body
      | None => None
      end
    | _ => None
    end.

  Definition is_fresh (ctx : context) (id : ident) :=
    List.forallb
      (fun decl =>
         match decl.(decl_name) with
         | nNamed id' => negb (ident_eq id id')
         | nAnon => true
         end) ctx.

  Fixpoint name_from_term (t : term) :=
    match t with
    | tRel _ | tVar _ | tEvar _ _ => "H"
    | tLambda na t => "f"
    | tLetIn na b t' => name_from_term t'
    | tApp f _ => name_from_term f
    | tConst c => "x"
    | _ => "U"
    end.

  Definition fresh_id_from ctx n id :=
    let fix aux i :=
      match i with
      | 0 => id
      | S i' =>
        let id' := id ++ string_of_nat (n - i) in
        if is_fresh ctx id' then id'
        else aux i'
      end
    in aux n.
  (* ligo doesn't support wildcard *)
  Definition string_of_name ctx (na : name) : string := 
    match na with
    | nAnon => fresh_id_from ctx 10 "a"
    | nNamed "_" => fresh_id_from ctx 10 "a"
    | nNamed n => n
    end.

  Definition fresh_name (ctx : context) (na : name) (t : term) :=
    let id := match na with
              | nNamed "_" => "a"
              | nAnon => "a"
              | nNamed id => id
              end
    in
    if is_fresh ctx id then nNamed id
    else nNamed (fresh_id_from ctx 10 id).

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

  Definition app_args_annot {A} (f : (∑t, annots box_type t) -> A) :=
    fix go (t : term) : annots box_type t -> list A := match t with
    | tApp t1 t2 => fun '(bt, (hda, arga)) => (f (t2; arga)) :: go t1 hda
    | _ => fun _ => []
    end.
(*   
  Equations app_args_annot {A B : Type} (f : term -> A) (t : term) (a : annots B t) : list (∑tt, annots B tt) :=
  app_args_annot f (tApp t1 t2) (bt, (hda, arga)) => (f t2; arga) :: app_args_annot f t1 hda;
  app_args_annot f t a := [].
 *)
  Fixpoint in_list {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
           (l : list A) (a : A) : bool :=
    match l with
    | [] => false
    | hd :: tl => if eq_dec hd a then true
                else in_list eq_dec tl a
    end.

  (** Builds a context for the branch *)
  Definition get_ctx_from_branch (ctx : context) : nat -> term -> context :=
    let fix go (ctx : context) (arity: nat) (branch : term) :=
    match arity with
    | 0 => []
    | S n =>
      match branch with
      | tLambda na B =>
        let na' := fresh_name ctx na branch in
        go (vass na' :: ctx) n B
      | t => []
      end
    end
    in go [].

  Definition print_def (print_term : context -> bool -> bool -> term -> string) (ctx : context) (fdef : def  term) :=
    let ctx' := [{| decl_name := dname fdef; decl_body := None |}] in
    let fix_name := string_of_name ctx (fdef.(dname)) in
    let (args, _) := Edecompose_lam (fdef.(dbody)) in
    let ctx := rev (map vass args) in
    let sargs := print_uncurried "" (map (fun x => string_of_name ctx x) args) in
    string_of_name ctx fdef.(dname)
        ++ " " ++ sargs  ++ " = "
        ++ nl
        ++ print_term (ctx ++ ctx' ++ ctx)%list true false (lam_body fdef.(dbody)).

  Definition print_pat (prefix : string) (TT : env string) (ctor : string) (pt : list string * string) :=
    let ctor_nm := from_option (look TT ctor) ((capitalize prefix) ++ ctor) in
    let print_parens := (Nat.ltb 1 (List.length pt.1)) in
    print_uncurried ctor_nm (rev pt.1) ++ " -> " ++ pt.2.


  Definition print_transfer (args : list string) :=
    match args with
    | [] => "MalformedTransfer()"
    | [a1;a2] => "Tezos.transaction unit " ++ a2 ++ " (get_contract_unit " ++ a1 ++ ")" 
    | _ => "MalformedTransfer(" ++ concat "," args ++ ")"
    end.

  (** ** The pretty-printer *)

  (** [prefix] - a sting pre-pended to the constants' and constructors' names to avoid clashes
      [FT] - list of fixpoint names. Used to determine if uncurrying is needed for an applied variable (if it corresponds to a recursive call). The initial value is an empty list. Once we fit a fixpoint case, we add the fixpoint name to [FT], so all the recursive calls in the fixpoint body are packed into a tuple.

      [TT] - translation table allowing for remapping constants and constructors to CameLIGO primitives, if required.

      [ctx] - context that gets updated when we go under lambda, let, pattern or fixpoint.

      [top,inapp] - flags used to determine how to print parenthesis.

      [t] - a term to be printed.
   *)

   Section map_with_bigprod.
    Context {X : Type}.
    Context {T : X -> Type}.
    Context {Y : Type}.
    Context (f : forall x, T x -> Y).
    Set Equations Transparent.
    Equations map_with_bigprod (xs : list X) (p : bigprod T xs) : list Y :=
    map_with_bigprod [] _ => [];
    map_with_bigprod (x :: xs) (Tx, bp) := f x Tx :: map_with_bigprod xs bp.
  End map_with_bigprod.

  Fixpoint print_term (prefix : string) (FT : list string) (TT : env string) (ctx : context) (top : bool) (inapp : bool) (t : term) {struct t} : annots box_type t -> string :=
  match t return annots box_type t -> string with
  | tBox => fun bt => "()" (* boxes become the contructor of the [unit] type *)
  | tRel n => fun bt =>
    match nth_error ctx n with
    | Some {| decl_name := na |} =>
      match na with
      | nAnon => "Anonymous (" ++ string_of_nat n ++ ")"
      | nNamed id => id
      end
    | None => "UnboundRel(" ++ string_of_nat n ++ ")"
    end
  | tVar n => fun bt => "Var(" ++ n ++ ")"
  | tEvar ev args => fun bt => "Evar(" ++ string_of_nat ev ++ "[]" (* TODO *)  ++ ")"
  | tLambda na body => fun '(bt, a) =>
    let na' := fresh_name ctx na t in
    parens top ("fun " ++ string_of_name ctx na'
                       ++ " -> " ++ print_term prefix FT TT (vass na' :: ctx) true false body a)

  | tLetIn na def body => fun '(bt, (vala, bodya)) =>
    let na' := fresh_name ctx na t in
    parens top ("let " ++ string_of_name ctx na' ++
                      " = " ++ print_term prefix FT TT ctx true false def vala ++ " in " ++ nl ++
                      print_term prefix FT TT (vdef na' def :: ctx) true false body bodya)
  | tApp f l as t => fun '(bt, (fa, la)) =>
    let apps := rev (app_args_annot (fun '(t; a) => print_term prefix FT TT ctx false false t a) t (bt, (fa, la))) in
    let (b,_) := decompose_app f in
    match b with
      (* if the variable corresponds to a fixpoint, we pack the arguments into a tuple *)
    | tRel i =>
      match nth_error ctx i with
      | Some d =>
        let nm := (string_of_name ctx d.(decl_name)) in
        if in_list String.string_dec FT nm
        then parens top (print_uncurried nm apps)
        else parens (top || inapp) (print_term prefix FT TT ctx false true f fa ++ " " ++ print_term prefix FT TT ctx false false l la)
      | None => "UnboundRel(" ++ string_of_nat i ++ ")"
      end
    | tConst c =>
      let cst_name := string_of_kername c in
      let nm := from_option (look TT cst_name) (prefix ++ c.2) in
      if nm =? "fst" then
        (concat " " (map (parens true) apps)) ++ ".0"
      else if nm =? "snd" then
        (concat " " (map (parens true) apps)) ++ ".1"
      else parens (top || inapp) (nm ++ " " ++ (concat " " (map (parens true) apps)))
    | tConstruct ind i =>
      let nm := get_constr_name ind i in
      (* is it a pair ? *)
      if (nm =? "pair") then
        print_uncurried "" apps
      (* is it a cons ? *)
      else if (nm =? "cons") then
        parens top (concat " :: " apps)
      (* is it a transfer *)
      else if (nm =? "Act_transfer") then 
        print_transfer apps
      else if (nm =? "_") then 
        fresh_id_from ctx 10 "a"
      else
        let nm' := from_option (look TT nm) ((capitalize prefix) ++ nm) in
        parens top (print_uncurried nm' apps)
    | _ => parens (top || inapp) (print_term prefix FT TT ctx false true f fa ++ " " ++ print_term prefix FT TT ctx false false l la)
    end
  | tConst c => fun bt =>
    let cst_name := string_of_kername c in
    from_option (look TT cst_name) (prefix ++ c.2)
  | tConstruct ind l => fun bt =>
    let nm := get_constr_name ind l in
    (* print annotations for 0-ary constructors of polymorphic types (like [] and None) *)
    if nm =? "nil" then
      "([]:" ++ print_box_type prefix TT (bt) ++ ")" 
    else if nm =? "None" then
      "(None:" ++ print_box_type prefix TT (bt) ++ ")" 
    else if nm =? "mnil" then
      "(Map.empty: " ++ print_box_type prefix TT (bt) ++ ")" 
    else from_option (look TT nm) ((capitalize prefix) ++ nm)
  | tCase (mkInd mind i as ind, nparam) t brs =>
    (* [if-then-else] is a special case *)
    if eq_kername mind <%% bool %%> then
      match brs with
      | [b1;b2] => fun '(bt, (ta, (b1a, (b2a, _)))) =>
        (* TODO *)
        parens top
                ("if " ++ print_term prefix FT TT ctx true false t ta 
                       ++ " then " ++ print_term prefix FT TT ctx true false (snd b1) b1a
                       ++ " else " ++ print_term prefix FT TT ctx true false (snd b2) b2a)
      | _ => fun bt => "Error (Malformed pattern-mathing on bool: given "
               ++ string_of_nat (List.length brs) ++ " branches " ++ ")"
      end
    else
      (* [list] is a special case *)
      if eq_kername mind <%% list %%> then
        match brs with
        | [b1;b2] => fun '(bt, (ta, (b1a, (b2a, _)))) =>
          let nil_case := "[] -> " ++ print_term prefix FT TT ctx false false b1.2 b1a in
          let (cons_args, _) := Edecompose_lam b2.2 in
          (* let '(cons_body; body_annot) := lam_body_annot_cont b2.2 b2a in *)
          let cons_pat := concat " :: " (map (fun x => string_of_name ctx (fresh_name ctx x b2.2)) cons_args) in
          let cons_ctx := rev (map vass cons_args) in
          let cons_case tbody tbodya := cons_pat ++ " -> " ++ print_term prefix FT TT (cons_ctx ++ ctx)%list false false tbody tbodya in
          parens top
             ("match " 
             ++ print_term prefix FT TT ctx true false t ta
                       ++ " with " ++ nl
                       ++ concat (nl ++ " | ") [nil_case;(lam_body_annot_cont cons_case b2.2 b2a)])
        | _ => fun bt => "Error (Malformed pattern-mathing on bool: given "
                ++ string_of_nat (List.length brs) ++ " branches " ++ ")"
        end
    else
    fun '(bt, (ta, trs)) =>
    match lookup_ind_decl mind i with
    | Some oib =>
      let fix print_branch ctx arity params (br : term) {struct br} : annots box_type br -> (_ * _) :=  
        match arity return annots box_type br -> (_ * _) with
        | S n =>
          match br return annots box_type br -> (_ * _) with
          | tLambda na B => fun '(bt, a) => 
            (* let na' := match na with
              | nAnon | nNamed "_" => CameLIGOPretty.print_term.fresh_name ctx (nNamed "a") br
              | nNamed id => CameLIGOPretty.print_term.fresh_name ctx na br
            end in *)
            let na' := CameLIGOPretty.print_term.fresh_name ctx na br in
            
            (* let na' := nNamed "a0" in *)
            let (ps, b) := print_branch (vass na' :: ctx) n params B a in
            (ps ++ [string_of_name ctx na'], b)%list
          (* | t => fun btt => (params , print_term prefix FT TT ctx false false t btt) *)
          | t => fun btt => (params , "UNEXPECTED ERROR IN print_branch")
        end
        | 0 => fun bt => (params , print_term prefix FT TT ctx false false br bt)
        end in
      
      let brs := map_with_bigprod (fun br tra => 
        print_branch ctx br.1 [] br.2 tra
      (* print_branch (fun tt ttra => print_term prefix FT TT ctx false false tt ttra) ctx br.1 [] br.2 tra *)
      ) brs trs in
      let brs_ := combine brs oib.(ExAst.ind_ctors) in
      let brs_printed : string := print_list (fun '(b, (na, _)) =>
                            print_pat prefix TT na b) (nl ++ " | ") brs_ in
       parens top
              ("match " 
                        ++ print_term prefix FT TT ctx true false t ta
                        ++ " with " ++ nl
                        ++ brs_printed)
    | None =>
      "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
              ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
    end
  | tProj (mkInd mind i as ind, pars, k) c => fun bt =>
    match lookup_ind_decl mind i with
    | Some oib =>
      match nth_error oib.(ExAst.ind_projs) k with
      | Some (na, _) => print_term prefix FT TT ctx false false c bt.2 ++ na
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term prefix FT TT ctx true false c bt.2 ++ ")"
      end
    | None =>
      "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                     ++ print_term prefix FT TT ctx true false c bt.2 ++ ")"
    end
  | tFix [fix_decl] n => fun '(bt, (fixa, _)) => (* NOTE: We assume that the fixpoints are not mutual *)
      let fix_name := string_of_name ctx fix_decl.(dname) in
      let body := fix_decl.(dbody) in
      let (args, _) := Edecompose_lam body in
      let sargs := map (string_of_name ctx) args in
      let fix_call :=
          "fun " ++ concat " " sargs ++ " -> "
                 ++ print_uncurried fix_name sargs in
      let FT' := fix_name :: FT in
      let print_def_annot (ctx : context) (fdef : def  term) : annots box_type fdef.(dbody) -> string   :=
        let ctx' := [{| decl_name := dname fdef; decl_body := None |}] in
        let fix_name := string_of_name ctx (fdef.(dname)) in
        let (args, _) := Edecompose_lam (fdef.(dbody)) in
        let ctx := rev (map vass args) in
        let sargs := print_uncurried "" (map (fun x => string_of_name ctx x) args) in
        fun btt => 
        string_of_name ctx fdef.(dname)
            ++ " " ++ sargs  ++ " = "
            ++ nl
            ++ lam_body_annot_cont (fun body body_annot => print_term prefix FT' TT (ctx ++ ctx' ++ ctx)%list true false body body_annot) fdef.(dbody) btt
      in
      parens top ("let rec " ++ print_def_annot ctx fix_decl fixa ++ nl ++
                             " in " ++ fix_call)
  | tFix [] _ => fun _ => "FixWithNoBody"
  | tFix _ _ => fun _ => "NotSupportedMutualFix"
  | tCoFix l n => fun _ => "NotSupportedCoFix"
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
           (env : ExAst.global_env)
           (decl_name : string)
           (modifier : option string)
           (wrap : string -> string)
           (ty : box_type)
           (t : term)
           (ta : annots box_type t)
            :=
  let (tys,_) := decompose_arr ty in
  let '(args,(lam_body; body_annot)) := Edecompose_lam_annot t ta in
  let targs := combine args (map (print_box_type prefix TT) tys) in
  let ctx := map (fun x => Build_context_decl x None) (rev args) in
  let printed_targs :=
      map (fun '(x,ty) => parens false (string_of_name ctx x ++ " : " ++ ty)) targs in
  let decl := prefix ++ decl_name ++ " " ++ concat " " printed_targs in
  (* let modif := match modifier with
               | Some m => "%"++m
               | None => ""
               end in *)
  "let" ++ " " ++ decl ++ " = "
        ++ wrap (CameLIGOPretty.print_term env prefix [] TT ctx true false lam_body body_annot).

Definition print_init (prefix : string)
           (TT : MyEnv.env string) (* tranlation table *)
           (build_call_ctx : string) (* a string that corresponds to a call contex *)
           (init_prelude : string) (* operations available in the [init] as local definitions.
                                      CameLIGO does not allow to refer to global definitions in [init]*)
           (env : ExAst.global_env)
           (cst : ExAst.constant_body) 
           : (constant_body_annots box_type cst) -> option string :=
    match cst.(ExAst.cst_body) as body return match body with
                                              | Some body => annots box_type body
                                              | None => unit
                                              end -> option string with
    | Some b => fun cstAnnot =>
    let '(args,(lam_body; body_annot)) := Edecompose_lam_annot b cstAnnot in
    let ty := cst.(ExAst.cst_type) in
    let (tys,inner_ret_ty) := decompose_arr ty.2 in
    let targs_inner := combine args (map (print_box_type prefix TT) tys) in
    let ctx := map (fun x => Build_context_decl x None) (rev args) in
    let printed_targs_inner :=
        map (fun '(x,ty) => parens false (string_of_name ctx x ++ " : " ++ ty)) targs_inner in
    let decl_inner := "inner " ++ concat " " printed_targs_inner in
    let printed_inner_ret_ty := print_box_type prefix TT inner_ret_ty in 
    let printed_outer_ret_ty :=
      match inner_ret_ty with
      | TApp (TInd ind) t1 =>
        if eq_kername <%% option %%> ind.(inductive_mind) then
          print_box_type prefix TT t1
        else print_box_type prefix TT inner_ret_ty
      | _ => print_box_type prefix TT inner_ret_ty 
      end in 
    let wrap t := 
      "match " ++ t ++ " with" ++ nl ++
      "  Some v -> v" ++ nl ++
      "| None -> (failwith (""""): " ++ printed_outer_ret_ty ++ ")" in
    let let_inner :=
        "let " ++ decl_inner ++ " :" ++ printed_inner_ret_ty ++ " = " ++ nl
              ++ CameLIGOPretty.print_term env prefix [] TT ctx true false lam_body body_annot
              ++ " in" in
    let printed_targs_outer := tl printed_targs_inner in
    (* ignore the first argument because it's a call context *)
    let decl_outer := 
      "init " ++ concat " " printed_targs_outer ++ " : " ++ printed_outer_ret_ty in
    let let_ctx := "let ctx = " ++ build_call_ctx ++ " in" in
    let inner_app := "inner " ++ concat " " ( "ctx" :: map (string_of_name ctx) (tl args)) in
    (* Type declaration of TODO *)
    let init_args_ty := "type init_args_ty = " ++ (tl tys |> map (print_box_type prefix TT) |> concat " * ") in
    let init_wrapper_args_printed tys :=
      match tys with
      | [] => ""
      | [ty] => " args"
      | tys => tys |> fold_right (fun _ '(i,s) => (i+1,s ++ " args." ++ string_of_nat i)) (0, "") |> snd
      end in
    let init_wrapper := 
         "let init_wrapper (args : init_args_ty) ="
      ++ nl
      ++ "  init" ++ (tl tys |> init_wrapper_args_printed) in 
    ret ("let " ++ decl_outer ++ " = "
                    ++ init_prelude
                    ++ nl
                    ++ let_inner
                    ++ nl
                    ++ let_ctx
                    ++ nl
                    ++ wrap (parens false inner_app)
                    ++ nl
                    ++ init_args_ty
                    ++ nl
                    ++ init_wrapper
                    ++ nl)
  | None => fun _ => None
  end. 


Definition print_cst (prefix : string)
           (TT : MyEnv.env string) (* tranlation table *)
           (env : ExAst.global_env)
           (kn : kername)
           (cst : ExAst.constant_body)
           : (constant_body_annots box_type cst) -> option string :=
  match cst.(ExAst.cst_body) as body return match body with
                                            | Some body => annots box_type body
                                            | None => unit
                                            end -> option string with
  | Some cst_body => fun annot =>
    (* NOTE: ignoring the path part *)
    let (_, decl_name) := kn in
    Some <| print_decl prefix TT env decl_name None id cst.(ExAst.cst_type).2 cst_body annot
  | None => fun _ => None
  end.

Section on_every.
  Import ExAst.
  Set Equations Transparent.
  Definition on_every_body (t : term) : annots box_type t -> unit := fun _ => tt.
  Equations on_every_constant (cst : Ex.constant_body) (a : constant_body_annots box_type cst) : unit :=
    on_every_constant {| cst_body := Some body |} a => on_every_body body a;
    on_every_constant _ _ => tt.

  Equations on_every_global_decl (decl : Ex.global_decl) (a : global_decl_annots box_type decl) : unit :=
    on_every_global_decl (Ex.ConstantDecl cst) a => on_every_constant cst a;
    on_every_global_decl _ _ => tt.

  Equations on_env (Σ : global_env) (Σa : env_annots box_type Σ) : list unit :=
    on_env ((kn, decl) :: Σ) (a, Σa) => on_every_global_decl decl a :: on_env Σ Σa;
    on_env [] _ => [].
End on_every.

Definition print_global_decl (prefix : string) (TT : MyEnv.env string)
           (nm : kername)
           (env : ExAst.global_env)
           (d : ExAst.global_decl) : 
           (global_decl_annots box_type d) -> kername * string :=
  match d return (global_decl_annots box_type d) -> kername * string with
  | ExAst.ConstantDecl cst => fun annot =>
    match print_cst prefix TT env nm cst annot with
    | Some r => (nm, r)
    | None => (nm, "TODO: print_global_decl ConstantDecl ERROR?")
    end
  | ExAst.InductiveDecl mib => fun annot =>
    match mib.(ExAst.ind_bodies) with
    | [oib] => (nm, print_inductive prefix TT oib)
    | _ => (nm,"Only non-mutual inductives are supported")
    end
  | TypeAliasDecl (Some (params, ty)) => fun annot =>
    let ta_nm := from_option (lookup TT (string_of_kername nm))
                             (prefix ++ nm.2) in
    (nm, "type " ++ uncapitalize ta_nm ++ concat " " (map ((string_of_name []) ∘ tvar_name) params) ++  " = "
            ++ print_box_type prefix TT ty)
  | TypeAliasDecl None => fun _ => (nm, "")
end.

Fixpoint print_global_env (prefix : string) (TT : MyEnv.env string)
           (env : ExAst.global_env) 
           : (env_annots box_type env) -> list (kername * string) :=
  match env return (env_annots box_type env) -> list (kername * string) with
  | (kn, has_deps, decl) :: env' => fun '(a,b) =>
    let printed :=
        (* only print decls for which the environment includes dependencies *)
        if has_deps then
          print_global_decl prefix TT kn env' decl a
        else
          (kn, "") in
    printed :: print_global_env prefix TT env' b
  | [] => fun _ => []
  end.

  
Local Open Scope string_scope.

(** We un-overload operations and add definitions that are more convenient to use during the pretty-printing phase. These part should be included when printing contracts that use the corresponding operations. *)

Definition int_ops :=
       "[@inline] let addInt (i : int) (j : int) = i + j"
    ++ nl
    ++ "[@inline] let subInt (i : int) (j : int) = i - j"
    ++ nl
    ++ "[@inline] let multInt (i : int) (j : int) = i * j"
    ++ nl
    ++ "[@inline] let divInt (i : int) (j : int) = i / j"
    ++ nl
    ++ "[@inline] let leInt (i : int) (j : int) = i <= j"
    ++ nl
    ++ "[@inline] let ltInt (i : int) (j : int) = i < j"
    ++ nl
    ++ "[@inline] let eqInt (i : int) (j : int) = i = j".

Definition tez_ops :=
       "[@inline] let addTez (n : tez) (m : tez) = n + m"
    ++ nl
    ++ "[@inline] let subTez (n : tez) (m : tez) = n - m"
    ++ nl
    ++ "[@inline] let leTez (a : tez ) (b : tez ) = a <= b"
    ++ nl
    ++ "[@inline] let ltTez (a : tez ) (b : tez ) =  a < b"
    ++ nl
    ++ "[@inline] let eqTez (a : tez ) (b : tez ) = a = b".

Definition nat_ops :=
       "[@inline] let modN (a : nat ) (b : nat ) = a mod b"
    ++ nl
    ++ "[@inline] let divN (a : nat ) (b : nat ) = a / b"
    ++ nl
    ++ "[@inline] let eqN (a : nat ) (b : nat ) = a = b"
    ++ nl
    ++ "[@inline] let lebN (a : nat ) (b : nat ) = a <= b"
    ++ nl
    ++ "[@inline] let ltbN (a : nat ) (b : nat ) = a < b".

Definition bool_ops :=
  "[@inline] let andb (a : bool ) (b : bool ) = a && b" ++ nl ++
  "[@inline] let orb (a : bool ) (b : bool ) = a || b".

Definition time_ops :=
       "[@inline] let eqb_time (a1 : timestamp) (a2 : timestamp) = a1 = a2"
    ++ nl
    ++ "[@inline] let leb_time (a1 : timestamp) (a2 : timestamp) = a1 <= a2"
    ++ nl
    ++ "[@inline] let ltb_time (a1 : timestamp) (a2 : timestamp) = a1 < a2".

Definition address_ops :=
  "[@inline] let eq_addr (a1 : address) (a2 : address) = a1 = a2".

Definition double_quote := String (ascii_of_byte "034") "".

Definition get_contract_def :=
     "let get_contract_unit (a : address) : unit contract  =" ++ nl
  ++ "  match (Tezos.get_contract_opt a : unit contract option) with" ++ nl
  ++ "    Some c -> c" ++ nl
  ++ "  | None -> (failwith (" ++ double_quote ++ "Contract not found." ++ double_quote ++ ") : unit contract)". 



Definition CameLIGOPrelude :=
  print_list id (nl ++ nl)
             [int_ops; tez_ops; nat_ops;
             bool_ops; time_ops; address_ops; get_contract_def].

(* TODO: need to revisit this for init *)
(* type parameter_wrapper = 
     Init of storage 
   | Call of parameter *)

Definition printWrapper (contract parameter_name storage_name : string): string :=
     "type return = (operation) list * (storage option)" ++ nl
  ++ "type parameter_wrapper =" ++ nl
  ++ "  Init of init_args_ty" ++ nl
  ++ "| Call of " ++ parameter_name ++ nl ++ nl
  ++ "let wrapper (param, st : parameter_wrapper * " ++ storage_name ++ " option) : return =" ++ nl
  ++ "  match param with  " ++ nl
  ++ "    Init init_args -> (([]: operation list), Some (init init_args))" ++ nl
  ++ "| Call p -> (" ++ nl
  ++ "  match st with" ++ nl
  ++ "    Some st -> (match (" ++ contract ++ " p st) with   " ++ nl
  ++ "                  Some v -> (v.0, Some v.1)" ++ nl
  ++ "                | None -> (failwith ("""") : return))" ++ nl
  ++ "  | None -> (failwith (""cannot call this endpoint before Init has been called""): return))".


Definition printMain :=
  "let main (action, st : parameter_wrapper * storage option) : return = wrapper (action, st)".
