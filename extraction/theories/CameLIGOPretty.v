(** * Pretty-printing CameLIGO code *)
(** Adapted from [EPretty] of MetaCoq.Erasure. *)

(** ** Features/limitations *)

(** Printing covers most constructs of CIC_box (terms after erasure).
    Usually we have to remove redundant boxes before printing.
    There are some limitations on what can work after extraction,
    due to the nature of CameLIGO, or sometimes, lack of proper support.

    CameLIGO allows only tail-recursive calls and recursive functions must
    have only one argument. So, we pack multiple arguments in a tuple.
    In order for that to be correct, we assume that all fixpoints are
    fully applied. *)
From MetaCoq.Erasure.Typed Require Import Utils.
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Utils Require Import MCList.
From MetaCoq.Utils Require Import MCPrelude.
From ConCert.Utils Require Import Env.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import StringExtra.
From ConCert.Execution Require ResultMonad.
From ConCert.Extraction Require Import Common.

From Coq Require Import String.
From Coq Require Import Nat.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Basics.

Local Open Scope string_scope.

Import Kernames ListNotations.

(* F# style piping notation *)
Notation "f <| x" := (f x) (at level 32, left associativity, only parsing).
(* i.e. f <| x <| y = (f <| x) <| y, and means (f x) y *)
Notation "x |> f" := (f x) (at level 31, left associativity, only parsing).
(* i.e. x |> f |> g = (x |> f) |> g, and means g (f x) *)

Notation "s1 ^ s2" := (String.append s1 s2).

Class CameLIGOPrintConfig :=
  { (* cosnstructors start with an uppercase letter *)
    print_ctor_name : kername -> string;

    (* types start with a lowercase letter *)
    print_type_name : kername -> string;

    (* constants start with a lowercase letter *)
    print_const_name : kername -> string }.

Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).

Local Coercion bytestring.String.to_string : bytestring.String.t >-> string.

(** Prepend the last module name all global declaration names to avoid name clashes. Due
    to limitations for constructors, use only part of the module name and cut the first
    31 letters *)
Module PrintConfAddModuleNames.


  Definition last_module_name (mp : modpath) : string :=
    match mp with
    | MPdot mp' nm => nm
    | MPfile (nm :: _) => nm
    | _ => ""
    end.

  Definition print_ctor_name_ (kn : kername) :=
    let lmn := last_module_name (fst kn) in
    let nm := (snd kn) in
    (* NOTE: CameLIGO has a limitation for the constructor name length,
       so we try our best to fit and don't get clashes *)
    let ctor_name := if lmn =? "" then bs_to_s nm else substring 0 4 lmn ^ "_" ^ nm in
    capitalize (substring 0 31 ctor_name).

  Definition print_ind_type_name_ (ind_kn : kername) :=
    let lmn := last_module_name (fst ind_kn) in
    let nm := snd ind_kn in
    let ty_name := if lmn =? "" then bs_to_s nm else lmn ^ "_" ^ nm in
    uncapitalize ty_name.

  Definition print_const_name_ (ind_kn : kername) :=
    let lmn := last_module_name (fst ind_kn) in
    let nm := (snd ind_kn) in
    let ty_name := if lmn =? "" then bs_to_s nm else lmn ^ "_" ^ nm in
    uncapitalize ty_name.

  Local Instance PrintWithModuleNames : CameLIGOPrintConfig :=
    {| print_ctor_name := print_ctor_name_;
       print_type_name := print_ind_type_name_;
       print_const_name := print_const_name_ |}.

End PrintConfAddModuleNames.

(** Print names only, don't prepend module names or any other parts of the
    fully qualified path. Gives more readable code, but might lead to name clashes *)
Module PrintConfShortNames.

  Local Instance PrintWithShortNames : CameLIGOPrintConfig :=
    {| print_ctor_name := fun kn => capitalize (snd kn);
       print_type_name := fun kn => uncapitalize (snd kn);
       print_const_name := fun kn => uncapitalize (snd kn) |}.

End PrintConfShortNames.

Section PPTerm.
  Context `{CameLIGOPrintConfig}.
  Context (Σ : ExAst.global_env).

  Definition look (e : env string) (s : string) : option string :=
    lookup e s.

  Definition is_rel (t : Ast.term) :=
  match t with
  | Ast.tRel _ => true
  | _ => false
  end.

  (* Use string_of_nat from StringExtra instead of MetaCoq's string_of_nat *)
  Definition string_of_nat := StringExtra.string_of_nat.
  Definition tokenize := str_split.

(** Takes a fully qualified name and returns the last part, e.g.
  for "Coq.ZArith.BinInt.Z.add" returns "add" *)
  Definition unqual_name nm := last (tokenize "." nm) ("Error (Malformed_qualified_name)").

  Definition print_uncurried (args : list string) :=
    let arg_len := #|args| in
    if (arg_len =? 0)%nat then
      ""
    else
      let no_parens := (#|args| =? 1)%nat in
      Common.parens (no_parens) (String.concat ", " args).

  Definition print_uncurried_app (s : string) (args : list string) :=
    let print_parens := (Nat.ltb 0 (List.length args)) in
    s ++ " " ++ print_uncurried args.

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

  (* Certain names in CameLIGO are reserved (like 'to' and others)
     so we ensure no fresh names are reserved *)
  (* Note: for reserved names from the syntax (like 'let', 'in', 'match', etc.)
     we don't need to add them since they are also reserved names in Coq, hence
     we can't write Coq programs with these names anyway. *)
  Definition is_reserved_name (id : string) (reserved : list string) :=
    List.existsb (String.eqb id) reserved.

  Definition ligo_reserved_names :=
    [
        "to"
      ; "val"
      ; "amount"
      ; "balance"
      ; "continue"
      ; "hash"
      ; "sender"
    ].

  (* NOTE: We should probably add more validation rules *)
  Definition ligo_valid_type_var (tv : string) : bool :=
    match String.index 0 "'" tv with
    | Some _ => false
    | None => true
    end.

  Open Scope bool.

  Import BasicAst EAst.

  Definition is_fresh (Γ : context) (id : string) :=
    negb (is_reserved_name id ligo_reserved_names)
    && List.forallb
      (fun decl =>
         match decl.(decl_name) with
         | nNamed id' =>
           (* NOTE: we compare the identifiers up to
              the capitalization of the first letters *)
           negb (String.eqb (uncapitalize id) (uncapitalize id'))
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

  Definition fresh_id_from ctx n (id : string) :=
    let fix aux i :=
      match i with
      | 0 => id
      | S i' =>
        let id' := id ^ string_of_nat (n - i) in
        if is_fresh ctx id' then id'
        else aux i'
      end
    in aux n.

  (* NOTE: LIGO doesn't support wildcard *)
  Definition fresh_string_name (ctx : context) (na : name) : string :=
    let id := match na with
              | nAnon => "a"
              | nNamed nm => if nm =? "_" then "a" else nm
              end
    in
    let id := uncapitalize id in
    if ligo_valid_type_var id then
      if is_fresh ctx id then id
      else
        fresh_id_from ctx (List.length ctx) id
    else fresh_id_from ctx (List.length ctx) "a".

  Definition fresh_string_names (Γ : context) (vs : list name) : context * list string :=
    let fix go (Γ : context) (vs : list name) : context * list string :=
    match vs with
    | [] => (Γ, [])
    | v :: vs0 =>
      let nm := fresh_string_name Γ v in
      (* add name to the context to avoid shadowing due to name clashes *)
      let Γ1 := vass (nNamed (bytestring.String.of_string nm)) :: Γ in
      let '(Γ2, vs1) := go Γ1 vs0 in
      (Γ2, nm :: vs1)
    end in
    go Γ vs.


  (** The [for_ind] flag tells the type printer whether the type is used in an inductive
      type definition or in a function, since the syntax is different for these two cases
      in CameLIGO *)
  Definition print_type_var_name (for_ind : bool) (var_name : string) :=
    let type_var_prefix := if for_ind then "'" else "" in
    type_var_prefix ++ var_name.

  (** Resolve a type level (index) into a variable name and print it *)
  (* INVARIANT: the names in the context are distinct *)
  Definition print_type_var (ty_ctx : list string) (for_ind : bool) (i : nat) :=
    match nth_error ty_ctx i with
    | Some var => print_type_var_name for_ind var
    | None => "UnboundTypeVar"
    end.

  Definition print_box_type_aux (for_ind : bool) (ty_ctx : list string) (TT : env string)
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
        parens false (String.concat " * " args)

      (* inductives are printed with args prefix style, e.g. "int option" *)
      else print_uncurried args ++ " " ++ go hd
    | _ => print_uncurried args ++ " " ++ go hd
    end
  | TVar i => print_type_var ty_ctx for_ind i (* TODO: pass context with type variables *)
  | TInd s =>
    let full_ind_name := string_of_kername s.(inductive_mind) in
    with_default (print_type_name s.(inductive_mind)) (look TT full_ind_name)
  | TConst s =>
    let full_cst_name := string_of_kername s in
    with_default (print_type_name s) (look TT full_cst_name)
  | TAny => "UnknownType"
  end.

  Open Scope program_scope.

  Definition print_box_type := print_box_type_aux false.
  Definition print_ind_box_type := print_box_type_aux true.
  Definition print_ctor
             (TT : env string)
             (ind_kn : kername)
             (ty_ctx : list string)
             (ctor : ident * list (name * box_type) * nat) :=
    let '(nm,tys,_) := ctor in
    let nm := print_ctor_name (fst ind_kn, nm) in
    match tys with
    | [] => nm
    | _ => let ctor_type := parens (#|tys| <=? 1)%nat <| String.concat " * " (map (print_ind_box_type ty_ctx TT ∘ snd) tys)
           in nm ^ " of " ^ ctor_type
    end.

  Definition print_proj (TT : env string) (ty_ctx : list string) (proj : ident * box_type) : string :=
    let (nm, ty) := proj in
    nm ^ " : " ^ print_ind_box_type ty_ctx TT ty.

  Definition print_type_params (ty_ctx : list string) : string :=
    if (Nat.eqb #|ty_ctx| 0) then ""
    else
      let ps := String.concat "," (map (print_type_var_name true) ty_ctx) in
      parens (Nat.eqb #|ty_ctx| 1) ps ^ " ".

  Definition print_type_declaration (nm : string) (ty_ctx : list string) (body : string) : string :=
    "type " ^ print_type_params ty_ctx ^ nm ^ " = " ^ body.

  Definition print_inductive (ind_kn : kername) (TT : env string)
             (oib : ExAst.one_inductive_body) :=
    let ind_nm := with_default (print_type_name (fst ind_kn, oib.(ExAst.ind_name)))
                               (lookup TT oib.(ExAst.ind_name)) in
    (* a context of type variable names, potentially renamed to avoid clashes *)
    let '(_, type_params_ctx) := fresh_string_names [] (map tvar_name oib.(ind_type_vars)) in
    (* one-constructor inductives are interpreted/printed as records *)
    match oib.(ExAst.ind_ctors), oib.(ExAst.ind_projs) with
    | [build_record_ctor], _ :: _ =>
      let '(_, ctors,_) := build_record_ctor in
      let projs_and_ctors := combine oib.(ExAst.ind_projs) ctors in
      let projs_and_ctors_printed := map (fun '(p, (na, ty)) => print_proj TT type_params_ctx (fst p, ty)) projs_and_ctors in
      let body :=
        <$ "{";
           String.concat (";" ^ nl) projs_and_ctors_printed;
           "}" $> in
      print_type_declaration ind_nm type_params_ctx body
    | _,_ =>
        let body :=
          <$ "";
             "  " ^ String.concat "| " (map (fun p => print_ctor TT ind_kn type_params_ctx p ^ nl) oib.(ExAst.ind_ctors)) $> in
        print_type_declaration ind_nm type_params_ctx body
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

  Definition lookup_ind_decl ind i :=
    match ExAst.lookup_env Σ ind with
    | Some (ExAst.InductiveDecl {| ExAst.ind_bodies := l |}) =>
      match nth_error l i with
      | Some body => Some body
      | None => None
      end
    | _ => None
    end.

  Definition get_constr_name (ind : inductive) (i : nat) : string :=
    match lookup_ind_decl ind.(inductive_mind) ind.(inductive_ind) with
    | Some oib =>
      match nth_error oib.(ExAst.ind_ctors) i with
      | Some (na, _,_) => bs_to_s na
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

  Definition is_record_constr (t : term) : option ExAst.one_inductive_body :=
    match t with
    | tConstruct (mkInd mind j as ind) i _ =>
      match lookup_ind_decl mind i with
      (* Check if it has only 1 constructor, and projections are specified *)
      | Some oib => match ExAst.ind_projs oib, Nat.eqb 1 (List.length oib.(ExAst.ind_ctors)) with
                    | _::_,true => Some oib
                    | _,_ => None
                    end
      | _ => None
      end
    | _ => None
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

  Definition app_args_annot {A} (f : (∑ t, annots box_type t) -> A) :=
    fix go (t : term) : annots box_type t -> list A :=
    match t with
    | tApp t1 t2 => fun '(bt, (hda, arga)) => (f (t2; arga)) :: go t1 hda
    | _ => fun _ => []
    end.

  (** Builds a context for the branch *)
  Definition get_ctx_from_branch (ctx : context) : nat -> term -> context :=
    let fix go (ctx : context) (arity: nat) (branch : term) :=
    match arity with
    | 0 => []
    | S n =>
      match branch with
      | tLambda na B =>
        let na' := fresh_string_name ctx na in
        go (vass (nNamed (bytestring.String.of_string na')) :: ctx) n B
      | _ => []
      end
    end
    in go [].

  Definition print_pat (TT : env string) (ind_kn : kername)
                       (ctor : string) (infix : bool)
                       (pt : list string * string) :=
    let vars := rev (fst pt) in
    if infix then
      String.concat (" " ++ ctor ++ " ") vars ++ " -> " ++ (snd pt)
    else
      let ctor_nm := with_default (print_ctor_name (fst ind_kn, bytestring.String.of_string ctor)) (look TT ctor) in
      let ctor_nm := if ctor_nm =? "Pair" then "" else ctor_nm in
      let print_parens := (Nat.ltb 1 (List.length (fst pt))) in
      print_uncurried_app ctor_nm vars ++ " -> " ++ (snd pt).

  Definition print_num_literal (TT : env string) (t : term) : option string :=
    (* is it a natural number literal? *)
    match nat_syn_to_nat t with
    | Some n => Some (string_of_nat n ^ "n")
    | None =>
      (* is it a positive binary number [positive] literal? *)
      match pos_syn_to_nat t with
      | Some k => Some (string_of_nat k ^ "n")
      | None => (* is it a binary natural number [N] literal? *)
        match N_syn_to_nat t with
        | Some m =>
          (* NOTE: we check whether [N] is remapped to [int], if it's NOT,
             we add "n", since we consider it a natural number *)
          let N_remapped := with_default "" (look TT (string_of_kername <%% N %%>)) in
          let units := if N_remapped =? "int" then "" else "n" in
          Some (string_of_nat m ^ units)
        | None =>
          (* is it an integer number [Z] literal? *)
          match Z_syn_to_Z t with
          | Some z =>
            (* NOTE: we check whether [Z] is remapped to [tez],
               if so, we add "tz" to the literal *)
            let Z_remapped := with_default "" (look TT (string_of_kername <%% BinInt.Z %%>)) in
            let units := if Z_remapped =? "tez" then "tez" else "" in
            Some (string_of_Z z ^ units)
          | None => None
          end
        end
      end
    end.

  Definition print_transfer (args : list string) :=
    match args with
    | [] => "MalformedTransfer()"
    | [a1; a2] => "Tezos.transaction unit " ++ a2 ++ " (get_contract_unit " ++ a1 ++ ")"
    | _ => "MalformedTransfer(" ++ String.concat "," args ++ ")"
    end.

  (** ** The pretty-printer *)

  (** [TT] - translation table allowing for remapping constants and constructors to
      CameLIGO primitives, if required.

      [ctx] - context that gets updated when we go under lambda, let, pattern or
      fixpoint.

      [ty_ctx] - context of type variables. Note that we don't update it, meaning that
      polymorphic definitions can be only top-level for now. To allow local polymorphic
      definitions (not sure whether these are supported in LIGO), we need to update type
      annotations, so they provide type context as well.

      [top,inapp] - flags used to determine how to print parenthesis.

      [t] - a term to be printed. *)

  Fixpoint print_term (TT : env string)
                      (ctx : context)
                      (ty_ctx : list string)
                      (top : bool)
                      (inapp : bool)
                      (t : term)
                      {struct t} : annots box_type t -> string :=
    match t return annots box_type t -> string with
    | tBox => fun bt => "()" (* boxes become the constructor of the [unit] type *)
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
    | tEvar ev args => fun bt => "Evar(" ++ string_of_nat ev ++ "[]" (* TODO *) ++ ")"
    | tLambda na body => fun '(bt, a) =>
      let na' := fresh_string_name ctx na in
      let (dom_tys, _) := ExAst.decompose_arr bt in
      let dom_ty := match nth_error dom_tys 0 with
                    | Some ty => print_box_type ty_ctx TT ty
                    | None => "LambdaError(NotAnArrowType)"
                    end in
      parens top ("fun (" ++ na' ++ " : "
                          ++ dom_ty ++ ")"
                          ++ " -> " ++ print_term TT (vass (nNamed (bytestring.String.of_string na')) :: ctx) ty_ctx true false body a)
    | tLetIn na def body => fun '(bt, (vala, bodya)) =>
      let na' := fresh_string_name ctx na in
      parens top ("let " ++ na' ++
                        " = " ++ print_term TT ctx ty_ctx true false def vala ++ " in " ++ nl ++
                        print_term TT (vdef (nNamed (bytestring.String.of_string na')) def :: ctx) ty_ctx true false body bodya)
    | tApp f l as t => fun '(bt, (fa, la)) =>
      let apps := rev (app_args_annot (fun '(t; a) => print_term TT ctx ty_ctx false false t a) t (bt, (fa, la))) in
      let '((b; ba),argas) := Edecompose_app_annot f fa in
      match apps with
      | [] => print_term TT ctx ty_ctx false true f fa
      | _ =>
          match b with
        | tConst c =>
          let cst_name := string_of_kername c in
          let nm := with_default (print_const_name c) (look TT cst_name) in
          (* primitive projections instead of 'fst' and 'snd' *)
          if nm =? "fst" then
            (String.concat " " (map (parens true) apps)) ++ ".0"
          else if nm =? "snd" then
            (String.concat " " (map (parens true) apps)) ++ ".1"
          else parens (top || inapp) (nm ++ " " ++ (String.concat " " (map (parens true) apps)))
        | tConstruct (mkInd mind j as ind) i [] =>
          let nm := get_constr_name ind i in
             (* is it a pair ? *)
            if (uncapitalize nm =? "pair") then
              print_uncurried apps
            (* is it a cons ? *)
            else if (uncapitalize nm =? "cons") then
              parens top (String.concat " :: " apps)
            (* is it a transfer *)
            else if (uncapitalize nm =? "act_transfer") then
              print_transfer apps
            (* is it a Ok *)
            else if ((nm =? "Ok") && (eq_kername mind <%% ConCert.Execution.ResultMonad.result %%>)) then
              "(" ++ parens false (print_uncurried_app nm apps) ++ ":" ++ print_box_type ty_ctx TT bt ++ ")"
            else if ((nm =? "Err") && (eq_kername mind <%% ConCert.Execution.ResultMonad.result %%>)) then
              "(" ++ parens false (print_uncurried_app nm apps) ++ ":" ++ print_box_type ty_ctx TT bt ++ ")"
            else if (nm =? "_") then
              fresh_id_from ctx 10 "a"
            (* inductive constructors of 1 arg are treated as records *)
            else
              match print_num_literal TT t with
              | Some s => s
              | None =>
                match is_name_remapped nm TT, is_record_constr b with
                | false, Some oib =>
                  let projs_and_apps := combine (map (bytestring.String.to_string ∘ fst) oib.(ExAst.ind_projs)) apps in
                  let field_decls_printed := projs_and_apps |> map (fun '(proj, e) => proj ++ " = " ++ e)
                                                          |> String.concat "; " in
                  "({" ++ field_decls_printed ++ "}: " ++ print_box_type ty_ctx TT bt ++ ")"
                | _,_ =>
                  let nm' := with_default (print_ctor_name (fst mind, bytestring.String.of_string nm)) (look TT nm) in
                  (* constructors take a single argument (uncurried),
                     so we wrap the args into a tuple *)
                  parens top (print_uncurried_app nm' apps)
                end
              end
        | _ => parens (top || inapp) (print_term TT ctx ty_ctx false true f fa ++ " " ++ print_term TT ctx ty_ctx false false l la)
        end
      end
    | tConst c => fun bt =>
      let cst_name := string_of_kername c in
      let nm_tt := with_default (print_const_name c) (look TT cst_name) in
      (* NOTE: empty maps require type annotations *)
      (* FIXME: this looks ad-hoc and should be controlled in remapping instead *)
      if (nm_tt =? "Map.empty") || (nm_tt =? "AddressMap.empty") then
        "(Map.empty: " ++ print_box_type ty_ctx TT bt ++ ")"
      else
        nm_tt
    | tConstruct ind l [] => fun bt =>
      let nm := get_constr_name ind l in
      match print_num_literal TT t with
      | Some lit => lit
      | None =>
        let nm_tt := with_default (print_ctor_name (fst ind.(inductive_mind), bytestring.String.of_string nm)) (look TT nm) in
        (* NOTE: print annotations for 0-ary constructors of polymorphic types (like [], None, and Map.empty) *)
        (* FIXME: this looks ad-hoc and should be controlled in remapping instead *)
        if (uncapitalize nm =? "nil") && (eq_kername ind.(inductive_mind) <%% list %%>) then
        "([]:" ++ print_box_type ty_ctx TT bt ++ ")"
        else if ((nm =? "None") && (eq_kername ind.(inductive_mind) <%% option %%>)) ||
             (nm_tt =? "Map.empty") then
               "(" ++ nm_tt ++ ":" ++ print_box_type ty_ctx TT bt ++ ")"
             else nm_tt
      end
    | tCase (mkInd mind i as ind, nparam) t brs =>
        let print_branch ctx (br_ctx : list name) (br_body : term) : annots box_type br_body -> (list string * string) :=
          fun a =>
            let ctx' := map vass br_ctx in
            let nas' := fresh_string_names (ctx ++ ctx')%list br_ctx in
            let b := print_term TT (fst nas') ty_ctx false false br_body a in
            (List.rev (snd nas'), b)%list in

      match brs with
      | [] => fun '(bt, (ta, trs)) => (parens false ("failwith 0 : " ^ print_box_type ty_ctx TT bt) ^ " (* absurd case *)")
      | _ =>
        (* [if-then-else] is a special case *)
        if eq_kername mind <%% bool %%> then
          match brs with
          | [b1; b2] => fun '(bt, (ta, (b1a, (b2a, _)))) =>
            parens top
                    ("if " ++ print_term TT ctx ty_ctx true false t ta
                           ++ " then " ++ print_term TT ctx ty_ctx true false (snd b1) b1a
                           ++ " else " ++ print_term TT ctx ty_ctx true false (snd b2) b2a)
          | _ => fun bt => "Error (Malformed pattern-mathing on bool: given "
                   ++ string_of_nat #|brs| ++ " branches " ++ ")"
          end
        else
          fun '(bt, (ta, trs)) =>
        match lookup_ind_decl mind i with
        | Some oib =>
          let brs :=
              map_with_bigprod _ (fun br tra => print_branch ctx (fst br) (snd br) tra) brs trs in
          let brs_ := combine brs oib.(ExAst.ind_ctors) in
          let brs_printed : string :=
              Common.print_list (fun '(b, (na, _,_)) =>
                            (* [list] is a special case *)
                            let na := bs_to_s na in
                            if (eq_kername mind <%% list %%>) && (na =? "cons") then
                              print_pat TT mind "::" true b
                            (* else if (eq_kername mind <%% list %%>) && (na =? "nil") then *)
                            (* print_pat "" TT mind "[]" false b *)
                            else
                            print_pat TT mind na false b)
                         (nl ++ " | ") brs_ in
           parens top
                  ("match " ++ print_term TT ctx ty_ctx true false t ta
                            ++ " with " ++ nl
                            ++ brs_printed)
        | None =>
          "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
                  ++ MCString.string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
        end
      end
    | tConstruct ind l (_ :: _) => fun _ => "Error(constructors_as_blocks_not_supported)"
    | tProj (Kernames.mkProjection (mkInd mind i) pars k) c => fun bt =>
      let ind := mkInd mind i in
      match lookup_ind_decl mind i with
      | Some oib =>
        match nth_error oib.(ExAst.ind_projs) k with
        | Some (na, _) => print_term TT ctx ty_ctx false false c (snd bt) ++ "." ++ na
        | None => "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                  ++ print_term TT ctx ty_ctx true false c (snd bt) ++ ")"
        end
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term TT ctx ty_ctx true false c (snd bt) ++ ")"
      end
    | tFix [fix_decl] n => fun '(bt, (fixa, _)) => (* NOTE: We assume that the fixpoints are not mutual *)
        let (tys,ret_ty) := decompose_arr bt in
        let fix_name := fresh_string_name ctx fix_decl.(dname) in
        let body := fix_decl.(dbody) in
        let '(args, _) := Edecompose_lam_annot body fixa in
        (* NOTE: adding the fix variable to the context *)
        let ctx := vass (nNamed (bytestring.String.of_string fix_name)) :: ctx in
        let sret_ty := print_box_type ty_ctx TT ret_ty in
        let (ctx, sargs) := fresh_string_names ctx args in
        let targs := combine sargs (map (print_box_type ty_ctx TT) tys) in
        let sargs_typed := String.concat " " (map (fun '(x,ty) => parens false (x ++ " : " ++ ty)) targs) in
        let fix_call := parens false (fix_name ^ " : " ^ print_box_type ty_ctx TT bt) in
        (* NOTE: we cannot directly use the result of decomposing with
           [Edecompose_lam_annot] because the guardedness check cannot see through it *)
        let fix_body := lam_body_annot_cont (fun body body_annot => print_term TT ctx ty_ctx true false body body_annot) fix_decl.(dbody) fixa in
        parens top ("let rec " ++ fix_name ^ " " ^ sargs_typed ^ " : " ^ sret_ty ^ " = " ^ nl ^
                      fix_body ^ nl ^
                    " in " ^ fix_call)
    | tFix [] _ => fun _ => "FixWithNoBody"
    | tFix _ _ => fun _ => "NotSupportedMutualFix"
    | tCoFix l n => fun _ => "NotSupportedCoFix"
    | tPrim _ => fun _ => "NotSupportedCoqPrimitive"
  end.

End PPTerm.

Section PPLigo.

  Context `{CameLIGOPrintConfig}.

  Fixpoint decompose_arr_n (n : nat) (bt : box_type) : list box_type * box_type :=
  match n, bt with
  | S m, TArr dom cod =>
      let (args, res) := decompose_arr_n m cod in (dom :: args, res)
  | _,_ => ([], bt)
  end.

  (* INVARIANT: the names in the contexts are distinct *)
  Definition print_forall (ty_ctx : list string) : string :=
    match ty_ctx with
    | [] => ""
    | _ => let binders := String.concat " " ty_ctx in
          parens false ("type " ++ binders)
    end.

  Example print_forall_ex :
    let (_, tys) := fresh_string_names []
      [BasicAst.nNamed (bytestring.String.of_string "a"); BasicAst.nNamed (bytestring.String.of_string "b"); BasicAst.nAnon] in
    print_forall tys = "(type a b a0)".
  Proof. reflexivity. Qed.

  Example print_forall_empty :
    print_forall [] = "".
  Proof. reflexivity. Qed.

  Import bytestring.String.
  Example print_ex1 :
    (let (args,_) := Edecompose_lam (tLambda (BasicAst.nNamed (bytestring.String.of_string "a"))
                                  (tLambda (BasicAst.nNamed (bytestring.String.of_string "b")) (tRel 0))) in
    fresh_string_names [{|
      Extract.E.decl_name := BasicAst.nNamed (String "b" EmptyString);
      Extract.E.decl_body := None
    |}] args) =
    ([{|
           Extract.E.decl_name :=
             BasicAst.nNamed (String "b" (String "0" EmptyString));
           Extract.E.decl_body := None
         |};
        {|
          Extract.E.decl_name := BasicAst.nNamed (String "a" EmptyString);
          Extract.E.decl_body := None
        |};
        {|
          Extract.E.decl_name := BasicAst.nNamed (String "b" EmptyString);
          Extract.E.decl_body := None
        |}], ["a"; "b0"]).
  Proof. reflexivity. Qed.

  Definition print_decl
             (TT : env string) (* translation table *)
             (env : ExAst.global_env)
             (decl_kn : kername)
             (wrap : string -> string)
             (ty_in_ctx : list BasicAst.name * box_type)
             (t : term)
             (ta : annots box_type t) :=
    let '(args,(lam_body; body_annot)) := Edecompose_lam_annot t ta in
    let (ctx, args) := fresh_string_names [] args in
    let '(ty_ctx, ty) := ty_in_ctx in
    let '(_, forall_abstractions) := fresh_string_names [] ty_ctx in
    let (tys,res_ty) := decompose_arr_n #|args| ty in
    let targs := combine args (map (print_box_type forall_abstractions TT) tys) in
    let printed_targs :=
      map (fun '(x,ty) => parens false (x ^ " : " ^ ty)) targs in
    let printed_res_ty := print_box_type forall_abstractions TT res_ty in
    let printed_forall := print_forall forall_abstractions in
    let decl := print_const_name decl_kn ^ printed_forall ^ " " ^ String.concat " " printed_targs in
    "let" ^ " " ^ decl ^ " : " ^ printed_res_ty ^ " = " ^ nl
    ^ wrap (print_term env TT ctx forall_abstractions true false lam_body body_annot).

  (* NOTE: we assume that [init] is not a polymorphic function, so we use an empty type
    context when printing types *)
  Definition print_init
             (TT : env string) (* translation table *)
             (build_call_ctx : string) (* a string that corresponds to a call context *)
             (init_prelude : string) (* operations available in the [init] as local definitions.
                                        CameLIGO does not allow referring to global definitions in [init]*)
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
      let (tys,inner_ret_ty) := decompose_arr (snd ty) in
      let '(ctx, sargs) := fresh_string_names [] args in
      let targs_inner := combine sargs (map (print_box_type [] TT) tys) in
      let printed_targs_inner :=
          map (fun '(x,ty) => parens false (x ++ " : " ++ ty)) targs_inner in
      let decl_inner := "inner " ++ String.concat " " printed_targs_inner in
      let printed_inner_ret_ty := print_box_type [] TT inner_ret_ty in
      let printed_outer_ret_ty :=
        match inner_ret_ty with
        | TApp (TInd ind) t1 =>
          if eq_kername <%% option %%> ind.(inductive_mind) then
            print_box_type [] TT t1
          else print_box_type [] TT inner_ret_ty
        | _ => print_box_type [] TT inner_ret_ty
        end in
      let wrap t :=
        "match " ++ t ++ " with" ++ nl ++
        "  Ok v -> Ok v"++ nl ++
        "| Err e -> (failwith e: " ++ printed_outer_ret_ty ++ ")" in
      let let_inner :=
          "let " ++ decl_inner ++ " :" ++ printed_inner_ret_ty ++ " = " ++ nl
                ++ print_term env TT ctx [] true false lam_body body_annot
                ++ " in" in
      let printed_targs_outer := printed_targs_inner in
      let decl_outer :=
        "init " ++ String.concat " " printed_targs_outer ++ " : " ++ printed_outer_ret_ty in
      let inner_app := "inner " ++ String.concat " " sargs in
      Some ("let " ++ decl_outer ++ " = "
                      ++ let_inner
                      ++ nl
                      ++ wrap (parens false inner_app))
    | None => fun _ => None
    end.

  Definition print_cst
             (TT : env string) (* translation table *)
             (env : ExAst.global_env)
             (kn : kername)
             (cst : ExAst.constant_body)
             : (constant_body_annots box_type cst) -> option string :=
    match cst.(ExAst.cst_body) as body return match body with
                                              | Some body => annots box_type body
                                              | None => unit
                                              end -> option string with
    | Some cst_body => fun annot =>
      Some (print_decl TT env kn id cst.(ExAst.cst_type) cst_body annot)
    | None => fun _ => None
    end.

  (* A wrapper type to separate declarations into type declarations ("type ... = ...")
     and constant declarations ("let x = ...") *)
  Inductive Decl a : Type :=
    | TyDecl : a -> Decl a
    | ConstDecl : a -> Decl a.
  Global Arguments TyDecl {_}.
  Global Arguments ConstDecl {_}.

  Definition print_global_decl (TT : env string)
             (nm : kername)
             (env : ExAst.global_env)
             (d : ExAst.global_decl) :
             (global_decl_annots box_type d) -> Decl (kername * string) :=
    match d return (global_decl_annots box_type d) -> Decl (kername * string) with
    | ExAst.ConstantDecl cst => fun annot =>
      match print_cst TT env nm cst annot with
      | Some r => ConstDecl (nm, r)
      | None => ConstDecl (nm, "print_global_decl ConstantDecl ERROR: " ++ string_of_kername nm)
      end
    | ExAst.InductiveDecl mib as d => fun annot =>
      match mib.(ExAst.ind_bodies) with
      | [oib] => TyDecl (nm, print_inductive nm TT oib)
      | _ => TyDecl (nm,"Only non-mutual inductives are supported; " ++ string_of_kername nm)
      end
    | TypeAliasDecl (Some (params, ty)) =>
        fun annot =>
          let ta_nm := with_default (print_type_name nm) (lookup TT (string_of_kername nm)) in
          let (_,ty_ctx) := fresh_string_names [] (map tvar_name params) in
      TyDecl (nm, print_type_declaration ta_nm ty_ctx (print_box_type ty_ctx TT ty))
    | TypeAliasDecl None => fun _ => TyDecl (nm, "")
  end.

  Fixpoint print_global_env (TT : env string)
             (env : ExAst.global_env)
             : (env_annots box_type env) -> list (Decl (kername * string)) :=
    match env return (env_annots box_type env) -> list (Decl (kername * string)) with
    | (kn, has_deps, decl) :: env' =>
      fun '(a,b) =>
        (* Filtering out empty type declarations *)
        (* TODO: possibly, move to extraction (requires modifications of the correctness proof) *)
        if is_empty_type_decl decl then print_global_env TT env' b
        else
          let printed :=
          (* only print decls for which the environment includes dependencies *)
          if has_deps then
            print_global_decl TT kn env' decl a
          else ConstDecl (kn, "") in
      printed :: print_global_env TT env' b
    | [] => fun _ => []
    end.

  Local Open Scope string_scope.

  (** We un-overload operations and add definitions that are more convenient
      to use during the pretty-printing phase. These part should be included
      when printing contracts that use the corresponding operations. *)

  Definition int_ops :=
    <$
    "[@inline] let addInt (i : int) (j : int) = i + j" ;
    "[@inline] let subInt (i : int) (j : int) = i - j" ;
    "[@inline] let subIntTruncated (a : int) (b : int) = let res = a - b in if res < 0 then 0 else res" ;
    "[@inline] let multInt (i : int) (j : int) = i * j" ;
    "[@inline] let divInt (i : int) (j : int) = i / j" ;
    "[@inline] let modInt (a : int)(b : int) : int = int (a mod b)" ;
    "[@inline] let leInt (i : int) (j : int) = i <= j" ;
    "[@inline] let ltInt (i : int) (j : int) = i < j" ;
    "[@inline] let eqInt (i : int) (j : int) = i = j"
    $>.

  Definition tez_ops :=
    <$
    "[@inline] let addTez (n : tez) (m : tez) = n + m" ;
    "[@inline] let subTez (n : tez) (m : tez) : tez option = n - m" ;
    "[@inline] let leTez (a : tez ) (b : tez ) = a <= b" ;
    "[@inline] let ltTez (a : tez ) (b : tez ) = a < b" ;
    "[@inline] let gtbTez (a : tez ) (b : tez ) = a > b" ;
    "[@inline] let eqTez (a : tez ) (b : tez ) = a = b" ;
    "[@inline] let natural_to_mutez (a: nat): tez = a * 1mutez" ;
    "[@inline] let divTez (a : tez) (b : tez) : tez = natural_to_mutez (a/b)" ;
    "[@inline] let multTez (n : tez) (m : tez) = (n/1tez) * m";
    "[@inline] let evenTez (i : tez) = (i mod 2n) = 0tez"
    $>.
  Definition nat_ops :=
    <$
    "[@inline] let addN (a : nat ) (b : nat ) = a + b" ;
    "[@inline] let multN (a : nat ) (b : nat ) = a * b" ;
    "[@inline] let modN (a : nat ) (b : nat ) = a mod b" ;
    "[@inline] let divN (a : nat ) (b : nat ) = a / b" ;
    "[@inline] let eqN (a : nat ) (b : nat ) = a = b" ;
    "[@inline] let lebN (a : nat ) (b : nat ) = a <= b" ;
    "[@inline] let ltbN (a : nat ) (b : nat ) = a < b";
    "let divN_opt (n : nat) (m : nat) : nat option = match ediv n m with | Some (q,_) -> Some q | None -> None";
    "let moduloN (n : nat) (m : nat) : nat = match ediv n m with | Some (_,r) -> r | None -> 0n";
    "let subOption (n : nat) (m : nat) : nat option = if n < m then None else Some (abs (n-m))";
    "let z_to_N (i : int) : nat = if i < 0 then 0n else abs i";
    "let z_of_N (n : nat) : int = int (n)"
    $>.

  Definition bool_ops :=
    <$
    "[@inline] let andb (a : bool ) (b : bool ) = a && b" ;
    "[@inline] let orb (a : bool ) (b : bool ) = a || b"
    $>.

  Definition time_ops :=
    <$
    "[@inline] let eqb_time (a1 : timestamp) (a2 : timestamp) = a1 = a2" ;
    "[@inline] let leb_time (a1 : timestamp) (a2 : timestamp) = a1 <= a2" ;
    "[@inline] let ltb_time (a1 : timestamp) (a2 : timestamp) = a1 < a2"
    $>.

  Definition address_ops :=
    "[@inline] let eq_addr (a1 : address) (a2 : address) = a1 = a2".

  Definition get_contract_def :=
    <$
    "let get_contract_unit (a : address) : unit contract =" ;
    "  match (Tezos.get_contract_opt a : unit contract option) with" ;
    "    Some c -> c" ;
    "  | None -> (failwith (""Contract not found."") : unit contract)"
    $>.

  Definition CameLIGO_call_ctx_type_name : string := "cctx".

  Definition CameLIGO_call_ctx_type :=
  <$ "(* ConCert's call context *)"
  ; "type " ^ CameLIGO_call_ctx_type_name ^ " = {"
  ; "  ctx_origin_ : address;"
  ; "  ctx_from_ : address;"
  ; "  ctx_contract_address_ : address;"
  ; "  ctx_contract_balance_ : tez;"
  ; "  ctx_amount_ : tez"
  ; "}"
  $>.

  Definition CameLIGO_call_ctx_instance :=
  <$"(* a call context instance with fields filled in with required data *)"
  ; "let cctx_instance : " ^ CameLIGO_call_ctx_type_name ^ "= "
  ; "{ ctx_origin_ = Tezos.get_source ();"
  ; "  ctx_from_ = Tezos.get_sender ();"
  ; "  ctx_contract_address_ = Tezos.get_self_address ();"
  ; "  ctx_contract_balance_ = Tezos.get_balance ();"
  ; "  ctx_amount_ = Tezos.get_amount ()"
  ; "}"
  ; ""
  ; "(* context projections as functions *)"
  ; "let ctx_from (c : " ^ CameLIGO_call_ctx_type_name ^ ") = c.ctx_from_"
  ; "let ctx_origin (c : " ^ CameLIGO_call_ctx_type_name ^ ") = c.ctx_origin_"
  ; "let ctx_contract_address (c : " ^ CameLIGO_call_ctx_type_name ^ ") = c.ctx_contract_address_"
  ; "let ctx_contract_balance (c : " ^ CameLIGO_call_ctx_type_name ^ ") = c.ctx_contract_balance_"
  ; "let ctx_amount (c : " ^ CameLIGO_call_ctx_type_name ^ ") = c.ctx_amount_"
  $>.

  Definition CameLIGO_chain_instance :=
  <$ (* ConCert's Chain type and its instance. Currently, we map all fields to Tezos.level *)
  "type chain = {"
  ; "  chain_height_     : nat;"
  ; "  current_slot_     : nat;"
  ; "  finalized_height_ : nat;"
  ; "}"
  ; ""
  ; "let dummy_chain : chain = {"
  ; "chain_height_     = Tezos.get_level ();"
  ; "current_slot_     = Tezos.get_level ();"
  ; "finalized_height_ = Tezos.get_level ();"
  ; "}"
  ; ""
  ; "(* chain projections as functions *)"
  ; "let chain_height (c : chain ) = c.chain_height_"
  ; "let current_slot (c : chain ) = c.current_slot_"
  ; "let finalized_height (c : chain) = c.finalized_height_"
  $>.

  Definition result_def :=
  <$
    "type ('t,'e) result ="
  ; "  Ok of 't"
  ; "| Err of 'e"
  $>.

  Definition CameLIGO_Chain_CallContext :=
  <$ CameLIGO_call_ctx_type
   ; CameLIGO_call_ctx_instance
   ; CameLIGO_chain_instance
  $>.

  Definition CameLIGOPrelude :=
    print_list id (nl ++ nl)
               [int_ops; tez_ops; nat_ops;
                bool_ops; time_ops; address_ops;
                result_def;
                get_contract_def; CameLIGO_Chain_CallContext].

  Definition printMain (contract parameter_name storage_name : string) : string :=
    <$ "" ;
       "type return = (operation) list * " ++ storage_name ;
       "" ;
       "let main (p, st : " ++ parameter_name ++ " option * " ++ storage_name ++ ") : return = " ;
       "   (match (" ++ contract ++ " dummy_chain cctx_instance " ++ " st p) with " ;
       "      Ok v -> (v.0, v.1)" ;
       "    | Err e -> (failwith e : return))" $>.

  Definition print_default_entry_point (state_nm : kername)
                                       (receive_nm : kername)
                                       (msg_nm : kername) :=
  let st := print_type_name state_nm in
  let rec := print_const_name receive_nm in
  let msg := print_type_name msg_nm in
  printMain rec msg st.
End PPLigo.
