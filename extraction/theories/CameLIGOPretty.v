(** * Pretty-printing CameLIGO code *)
(** Adapted from [EPretty] of MetaCoq.Erasure. *)

(** ** Features/limitations *)

(** Printing covers most constructs of CIC_box (terms after erasure). Usually we have to remove redundant boxes before printing. There are some limitations on what can work after extraction, due to the nature of CameLIGO, or some times, lack of proper support.

CameLIGO allows only tail-recursive calls and recursive functions must have only one argument. So, we pack multiple arguments in a tuple. In order for that to be correct, we assume that all fixpoints are fully applied. *)

From Coq Require Import List Program String Ascii.
From ConCert.Extraction Require Import Utils ExAst Common.
From ConCert.Extraction Require Import Annotations.
From ConCert.Extraction Require Import TypeAnnotations.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Extraction.
From ConCert.Embedding Require Import MyEnv Ast.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Erasure Require Import EAst EAstUtils.
From ConCert.Utils Require Import StringExtra.


Import monad_utils.MonadNotation.
Local Open Scope string_scope.
Import String.

(* F# style piping notation *)
Notation "f <| x" := (f x) (at level 32, left associativity, only parsing).
(* i.e. f <| x <| y = (f <| x) <| y, and means (f x) y *)
Notation "x |> f" := (f x) (at level 31, left associativity, only parsing).
(* i.e. x |> f |> g = (x |> f) |> g, and means g (f x) *)

Class CameLIGOPrintConfig :=
  { (* cosnstructors start with an uppercase letter *)
    print_ctor_name : kername -> string;

    (* types start with a lowercase letter  *)
    print_type_name : kername -> string;

    (* constants start with a lowercase letter *)
    print_const_name : kername -> string }.

(** Prepend the last module name all global declaration names to avoid name clashes.  Due
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
    let lmn := last_module_name kn.1 in
    let nm := kn.2 in
    (* NOTE: CameLIGO has a limitation for the constructor name length, so we try our best to fit and don't get clashes *)
    let ctor_name := if lmn =? "" then nm else substring 0 4 lmn ^ "_" ^ nm in
    capitalize (substring 0 31 ctor_name).

  Definition print_ind_type_name_ (ind_kn : kername) :=
    let lmn := last_module_name ind_kn.1 in
    let nm := ind_kn.2 in
    let ty_name := if lmn =? "" then nm else lmn ^ "_" ^ nm in
    uncapitalize ty_name.

  Definition print_const_name_ (ind_kn : kername) :=
    let lmn := last_module_name ind_kn.1 in
    let nm := ind_kn.2 in
    let ty_name := if lmn =? "" then nm else lmn ^ "_" ^ nm in
    uncapitalize ty_name.
  
  Local Instance PrintWithModuleNames : CameLIGOPrintConfig :=
    {| print_ctor_name := print_ctor_name_;
       print_type_name := print_ind_type_name_;
       print_const_name := print_const_name_ |}.

End PrintConfAddModuleNames.

(** Print names only, don't prepend module names or any other parts of the fully qualified path.
    Gives more readable code, but might lead to name clashes *)
Module PrintConfShortNames.

  Local Instance PrintWithShortNames : CameLIGOPrintConfig :=
    {| print_ctor_name := fun kn => capitalize kn.2;
       print_type_name := fun kn => uncapitalize kn.2;
       print_const_name := fun kn => uncapitalize kn.2 |}.

End PrintConfShortNames.

Section PPTerm.
  Context `{CameLIGOPrintConfig}.
  Context (Σ : ExAst.global_env).

  Definition look (e : MyEnv.env string) (s : string) : option string :=
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


  (** The [for_ind] flag tells the type printer whether the type is used in an inductive
      type definition or in a fucntion, since the syntax is different for these two cases
      in CameLIGO *)

  Definition print_type_var (for_ind : bool) (i : nat) :=
    let type_var_prefix := if for_ind then "'" else "_" in
    type_var_prefix ++ "a" ++ string_of_nat i.

  Definition print_box_type_aux (for_ind : bool) (TT : env string)
    : box_type -> string :=
    fix go  (bt : box_type) :=
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

      (* inductives are printed with args prefix style, e.g. "int option" *)
      else print_uncurried "" args ++ " " ++ go hd
    | _ => print_uncurried "" args ++ " " ++ go hd
    end
  | TVar i => print_type_var for_ind i (* TODO: pass context with type variables *)
  | TInd s =>
    let full_ind_name := string_of_kername s.(inductive_mind) in
    from_option (look TT full_ind_name)
                (print_type_name s.(inductive_mind))
  | TConst s =>
    let full_cst_name := string_of_kername s in
    from_option (look TT full_cst_name) (print_type_name s)
  | TAny => "UnknownType"
  end.

  Definition print_box_type := print_box_type_aux false.
  Definition print_ind_box_type := print_box_type_aux true.
  
  Definition print_ctor
             (TT : env string)
             (ind_kn : kername)
             (ctor : ident × list (name × box_type)) :=
    let (nm,tys) := ctor in
    let nm := print_ctor_name (ind_kn.1, nm) in
    match tys with
    | [] => nm
    | _ => let ctor_type := parens (#|tys| <=? 1) <| concat " * " (map (print_ind_box_type TT ∘ snd) tys)
           in nm ^ " of " ^ ctor_type
    end.

  Definition print_proj (TT : env string) (proj : ident × box_type) : string :=
    let (nm, ty) := proj in
    nm ^ " : " ^ print_ind_box_type TT ty.

  Definition print_type_params (vs : list type_var_info) : string :=
    if (Nat.eqb #|vs| 0) then ""
      else (let ps := concat "," (mapi (fun i _ => print_type_var true i) vs) in
            (parens (Nat.eqb #|vs| 1) ps ^ " ")).

  Definition print_type_declaration (nm : string) (params : list type_var_info) (body : string) : string :=
    "type " ^ print_type_params params ^ nm ^ " = " ^ body.
  
  Definition print_inductive (ind_kn : kername) (TT : env string)
             (oib : ExAst.one_inductive_body) :=
    let ind_nm := from_option (lookup TT oib.(ExAst.ind_name))
                              (print_type_name (ind_kn.1, oib.(ExAst.ind_name))) in
    (* one-constructor inductives are interpreted/printed as records *)
    match oib.(ExAst.ind_ctors), oib.(ExAst.ind_projs) with
    | [build_record_ctor], _::_ =>
      let '(_, ctors) := build_record_ctor in
      let projs_and_ctors := combine oib.(ExAst.ind_projs) ctors in
      let projs_and_ctors_printed := map (fun '(p, (na, ty)) => print_proj TT (p.1, ty)) projs_and_ctors in
      let body :=
        <$ "{";
             concat (";" ^ nl) projs_and_ctors_printed;
           "}" $> in
      print_type_declaration ind_nm oib.(ind_type_vars) body
    | _,_ =>
        let body :=
          <$ "";
             "  " ^ concat "| " (map (fun p => print_ctor TT ind_kn p ^ nl) oib.(ExAst.ind_ctors)) $> in
        print_type_declaration ind_nm oib.(ind_type_vars) body
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

  Definition lookup_ind_decl ind i :=
    match ExAst.lookup_env Σ ind with
    | Some (ExAst.InductiveDecl {| ExAst.ind_bodies := l |}) =>
      match nth_error l i with
      | Some body => Some body
      | None => None
      end
    | _ => None
    end.

  (* Certain names in CameLIGO are reserved (like 'to' and others) so we ensure no fresh names are reserved *)
  (* Note: for reserved names from the syntax (like 'let', 'in', 'match', etc.) we don't need to add them since
     they are also reserved names in Coq, hence we can't write coq programs with these names anyways. *)
  Definition is_reserved_name (id : ident) (reserved : list ident) := 
    List.existsb (ident_eq id) reserved.
  
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

  Definition is_fresh (Γ : context) (id : ident) :=
    negb (is_reserved_name id ligo_reserved_names)
    &&
    List.forallb
      (fun decl =>
         match decl.(decl_name) with
         | nNamed id' =>
           (* NOTE: we compare the identifiers up to the capitalisation of the first letters *)
           negb (ident_eq (uncapitalize id) (uncapitalize id'))
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
    let id := uncapitalize id in
    if is_fresh ctx id then nNamed id
    else nNamed (fresh_id_from ctx 10 id).

  Fixpoint fresh_names (Γ : context) (vs : list name) : context * list name :=
    match vs with
    | [] => (Γ, [])
    | v :: vs0 =>
      let nm := fresh_name Γ v (tVar "dummy") in
      let Γ0 := vass nm :: Γ in (* add name to the context to avoid shadowing due to name clashes *)
      let '(Γ1, vs1) := fresh_names Γ0 vs0 in
      (Γ1, nm :: vs1)
    end.


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

  Definition is_record_constr (t : term) : option ExAst.one_inductive_body := 
    match t with
    | tConstruct (mkInd mind j as ind) i =>
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

  Definition app_args_annot {A} (f : (∑t, annots box_type t) -> A) :=
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
        let na' := fresh_name ctx na branch in
        go (vass na' :: ctx) n B
      | t => []
      end
    end
    in go [].

  Definition print_pat (TT : env string) (ind_kn : kername) (ctor : string) (infix : bool) (pt : list string * string) :=
    let vars := rev pt.1 in
    if infix then
      concat (" " ++ ctor ++ " ") vars ++ " -> " ++ pt.2
    else
      let ctor_nm := from_option (look TT ctor) (print_ctor_name (ind_kn.1, ctor)) in
      let ctor_nm := if ctor_nm =? "Pair" then "" else ctor_nm in
      let print_parens := (Nat.ltb 1 (List.length pt.1)) in
      print_uncurried ctor_nm vars ++ " -> " ++ pt.2.

  Definition print_num_literal (TT : env string) (t : term) : option string :=
    (* is it an natural number literal? *)
    match nat_syn_to_nat t with
    | Some n => Some (string_of_nat n ^ "n")
    | None =>
      (* is it an positive binary number [positive] literal? *)
      match pos_syn_to_nat t with
      | Some k => Some (string_of_nat k ^ "n")
      | None => (* is it an binary natural number [N] literal? *)
        match N_syn_to_nat t with
        | Some m =>
          (* NOTE: we check whether [N] is remapped to [int], if it's NOT, we add "n", since we consider it a natural number *)
          let N_remapped := from_option (look TT (string_of_kername <%% N %%>)) "" in
          let units := if N_remapped =? "int" then "" else "n" in
          Some (string_of_nat m ^ units)
        | None =>
          (* is it an integer number [Z] literal? *)
          match Z_syn_to_Z t with
          | Some z =>
            (* NOTE: we check whether [Z] is remapped to [tez], if so, we add "tz" to the literal *)
            let Z_remapped := from_option (look TT (string_of_kername <%% Z %%>)) "" in
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
    | [a1;a2] => "Tezos.transaction unit " ++ a2 ++ " (get_contract_unit " ++ a1 ++ ")"
    | _ => "MalformedTransfer(" ++ concat "," args ++ ")"
    end.

  (** ** The pretty-printer *)

  (** [FT] - list of fixpoint names. Used to determine if uncurrying is needed for an applied variable (if it corresponds to a recursive call). The initial value is an empty list. Once we fit a fixpoint case, we add the fixpoint name to [FT], so all the recursive calls in the fixpoint body are packed into a tuple.

      [TT] - translation table allowing for remapping constants and constructors to CameLIGO primitives, if required.

      [ctx] - context that gets updated when we go under lambda, let, pattern or fixpoint.

      [top,inapp] - flags used to determine how to print parenthesis.

      [t] - a term to be printed.
   *)

  Fixpoint print_term (FT : list string)
                      (TT : env string)
                      (ctx : context)
                      (top : bool)
                      (inapp : bool)
                      (t : term)
                      {struct t} : annots box_type t -> string :=
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
      let (dom_tys, _) := ExAst.decompose_arr bt in
      let dom_ty := match nth_error dom_tys 0 with
                    | Some ty => print_box_type TT ty
                    | None => "LambdaError(NotAnArrowType)"
                    end in
      parens top ("fun (" ++ string_of_name ctx na' ++ " : "
                          ++ dom_ty ++ ")"
                          ++ " -> " ++ print_term  FT TT (vass na' :: ctx) true false body a)
    | tLetIn na def body => fun '(bt, (vala, bodya)) =>
      let na' := fresh_name ctx na t in
      parens top ("let " ++ string_of_name ctx na' ++
                        " = " ++ print_term  FT TT ctx true false def vala ++ " in " ++ nl ++
                        print_term  FT TT (vdef na' def :: ctx) true false body bodya)
    | tApp f l as t => fun '(bt, (fa, la)) =>
      let apps := rev (app_args_annot (fun '(t; a) => print_term  FT TT ctx false false t a) t (bt, (fa, la))) in
      let '((b;ba),argas) := Edecompose_app_annot f fa in
      match apps with
      | [] => print_term  FT TT ctx false true f fa
      | _ =>
          match b with
          (* if the variable corresponds to a fixpoint, we pack the arguments into a tuple *)
        | tRel i =>
          match nth_error ctx i with
          | Some d =>
            let nm := (string_of_name ctx d.(decl_name)) in
            if List.in_dec String.string_dec nm FT
            then parens top (print_uncurried nm apps)
            else parens (top || inapp) (print_term  FT TT ctx false true f fa ++ " " ++ print_term  FT TT ctx false false l la)
          | None => "UnboundRel(" ++ string_of_nat i ++ ")"
          end
        | tConst c =>
          let cst_name := string_of_kername c in
          let nm := from_option (look TT cst_name) (print_const_name c) in
          (* primitive projections instead of 'fst' and 'snd' *)
          if nm =? "fst" then
            (concat " " (map (parens true) apps)) ++ ".0"
          else if nm =? "snd" then
            (concat " " (map (parens true) apps)) ++ ".1"
          else parens (top || inapp) (nm ++ " " ++ (concat " " (map (parens true) apps)))
        | tConstruct (mkInd mind j as ind) i =>
          let nm := get_constr_name ind i in
             (* is it a pair ? *)
            if (uncapitalize nm =? "pair") then
              print_uncurried "" apps
            (* is it a cons ? *)
            else if (uncapitalize nm =? "cons") then
              parens top (concat " :: " apps)
            (* is it a transfer *)
            else if (uncapitalize nm =? "act_transfer") then
              print_transfer apps
            else if (nm =? "_") then
              fresh_id_from ctx 10 "a"
            (* inductive constructors of 1 arg are treated as records *)
            else
              match print_num_literal TT t with
              | Some s => s
              | None =>
                match is_name_remapped nm TT, is_record_constr b with
                | false, Some oib => 
                  let projs_and_apps := combine (map fst oib.(ExAst.ind_projs)) apps in 
                  let field_decls_printed := projs_and_apps |> map (fun '(proj, e) => proj ++ " = " ++ e)
                                                          |> concat "; " in
                  "({" ++ field_decls_printed ++ "}: " ++ print_box_type  TT bt ++ ")"
                | _,_ => 
                  (* constructors must be capitalized *)
                  let nm' := from_option (look TT nm) (print_ctor_name (mind.1, nm)) in
                  parens top (print_uncurried nm' apps)
                end
              end
        | _ => parens (top || inapp) (print_term  FT TT ctx false true f fa ++ " " ++ print_term  FT TT ctx false false l la)
        end
      end
    | tConst c => fun bt =>
      let cst_name := string_of_kername c in
      let nm_tt := from_option (look TT cst_name) (print_const_name c) in
      (* empty maps require type annotations *)
      if (nm_tt =? "Map.empty") || (nm_tt =? "AddressMap.empty") then
        "(Map.empty: " ++ print_box_type  TT bt ++ ")"
      else
        nm_tt
    | tConstruct
        ind l => fun bt =>
      let nm := get_constr_name ind l in
      match print_num_literal TT t with
      | Some lit => lit
      | None =>
        let nm_tt := from_option (look TT nm) (print_ctor_name (ind.(inductive_mind).1, nm)) in
        (* NOTE: print annotations for 0-ary constructors of polymorphic types (like [], None, and Map.empty) *)
        (* FIXME: this looks ad-hoc and should be controlled in remapping instead *)
        if (uncapitalize nm =? "nil") && (eq_kername ind.(inductive_mind) <%% list %%>) then
        "([]:" ++ print_box_type  TT bt ++ ")"
        else if ((nm =? "None") && (eq_kername ind.(inductive_mind) <%% option %%>)) ||
             (nm_tt =? "Map.empty") then
               "(" ++ nm_tt ++ ":" ++ print_box_type  TT bt ++ ")"
             else nm_tt
      end
    | tCase (mkInd mind i as ind, nparam) t brs =>
      let fix print_branch ctx arity params (br : term) {struct br} : annots box_type br -> (_ * _) :=
            match arity return annots box_type br -> (_ * _) with
            | S n =>
              match br return annots box_type br -> (_ * _) with
              | tLambda na B => fun '(bt, a) =>
                let na' := fresh_name ctx na br in
                let (ps, b) := print_branch (vass na' :: ctx) n params B a in
                (ps ++ [string_of_name ctx na'], b)%list
              (* Assuming all case-branches have been expanded this should never happen: *)
              | t => fun btt => (params , "ERROR: unexpected wildcard branch - currently not supported")
            end
            | 0 => fun bt => (params , print_term FT TT ctx false false br bt)
            end in

      match brs with
      | [] => fun '(bt, (ta, trs)) => (parens false ("failwith 0 : " ^ print_box_type  TT bt) ^ " (* absurd case *)")
      | _ =>
        (* [if-then-else] is a special case *)
        if eq_kername mind <%% bool %%> then
          match brs with
          | [b1;b2] => fun '(bt, (ta, (b1a, (b2a, _)))) =>
            parens top
                    ("if " ++ print_term  FT TT ctx true false t ta
                           ++ " then " ++ print_term  FT TT ctx true false (snd b1) b1a
                           ++ " else " ++ print_term  FT TT ctx true false (snd b2) b2a)
          | _ => fun bt => "Error (Malformed pattern-mathing on bool: given "
                   ++ string_of_nat (List.length brs) ++ " branches " ++ ")"
          end
        else
          fun '(bt, (ta, trs)) =>
        match lookup_ind_decl mind i with
        | Some oib =>
          let brs :=
              map_with_bigprod _ (fun br tra => print_branch ctx br.1 [] br.2 tra)
                               brs
                               trs in
          let brs_ := combine brs oib.(ExAst.ind_ctors) in
          let brs_printed : string :=
              print_list (fun '(b, (na, _)) =>
                            (* [list] is a special case *)
                            if (eq_kername mind <%% list %%>) && (na =? "cons") then
                              print_pat  TT mind "::" true b
                            (* else if (eq_kername mind <%% list %%>) && (na =? "nil") then *)
                            (*   print_pat "" TT mind "[]" false b *)
                            else
                            print_pat TT mind na false b)
                         (nl ++ " | ") brs_ in
           parens top
                  ("match " ++ print_term  FT TT ctx true false t ta
                            ++ " with " ++ nl
                            ++ brs_printed)
        | None =>
          "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
                  ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
        end
      end
    | tProj (mkInd mind i as ind, pars, k) c => fun bt =>
      match lookup_ind_decl mind i with
      | Some oib =>
        match nth_error oib.(ExAst.ind_projs) k with
        | Some (na, _) => print_term  FT TT ctx false false c bt.2 ++ "." ++ na
        | None => "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                  ++ print_term  FT TT ctx true false c bt.2 ++ ")"
        end
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term  FT TT ctx true false c bt.2 ++ ")"
      end
    | tFix [fix_decl] n => fun '(bt, (fixa, _)) => (* NOTE: We assume that the fixpoints are not mutual *)
        (* Given an arrow type, prints the arguments in a curried way *)
        let print_args_curried  TT ctx bt args :=
          let (tys,_) := decompose_arr bt  in
          let targs := combine args (map (print_box_type  TT) tys) in
          targs
            |> map (fun '(x,ty) => parens false (string_of_name ctx x ++ " : " ++ ty) )
            |> concat " " in
        let fix_name := string_of_name ctx fix_decl.(dname) in
        let body := fix_decl.(dbody) in
        let '(args, (lam_body; body_annot)) := Edecompose_lam_annot body fixa in

        let sargs := map (string_of_name ctx) args in
        let sargs_typed := print_args_curried  TT ctx bt args in
        let fix_call :=
            "fun " ++ sargs_typed ++ " -> "
                   ++ print_uncurried fix_name sargs in
        let FT' := fix_name :: FT in

        let print_def_annot (ctx : context) (fdef : def  term) : annots box_type fdef.(dbody) -> string   :=
          fun btt =>
          let ctx' := [{| decl_name := dname fdef; decl_body := None |}] in
          let fix_name := string_of_name ctx (fdef.(dname)) in
          let (tys,ret_ty) := decompose_arr bt  in
          let '(args,(lam_body; body_annot)) := Edecompose_lam_annot (fdef.(dbody)) btt in
          let ctx := rev (map vass args) in
          let sargs := map (string_of_name ctx) args in
          let tys_printed := map (print_box_type  TT) tys in
          let sargs_uncurried := parens false (concat ", " sargs ++ " : " ++ concat " * " tys_printed) in
          let ret_ty_printed := print_box_type  TT ret_ty in
              string_of_name ctx fdef.(dname) ++ " " ++ sargs_uncurried  ++
              " : " ++ ret_ty_printed ++ " = "
              ++ nl
              ++ lam_body_annot_cont (fun body body_annot => print_term  FT' TT (ctx ++ ctx' ++ ctx)%list true false body body_annot) fdef.(dbody) btt
        in
        parens top ("let rec " ++ print_def_annot ctx fix_decl fixa ++ nl ++
                               " in " ++ fix_call)
    | tFix [] _ => fun _ => "FixWithNoBody"
    | tFix _ _ => fun _ => "NotSupportedMutualFix"
    | tCoFix l n => fun _ => "NotSupportedCoFix"
    | tPrim _ => fun _ => "NotSupportedCoqPrimitive"
  end.

End PPTerm.

Section PPLigo.

  Context `{CameLIGOPrintConfig}.

  Fixpoint decompose_arr_n (n : nat) (bt : box_type) : list box_type × box_type :=
  match n, bt with
  | S m, TArr dom cod =>
      let (args, res) := decompose_arr_n m cod in (dom :: args, res)
  | _,_ => ([], bt)
  end.
  
  Definition print_decl
             (TT : MyEnv.env string) (* translation table *)
             (env : ExAst.global_env)
             (decl_kn : kername)
             (wrap : string -> string)
             (ty : box_type)
             (t : term)
             (ta : annots box_type t)
    :=
    let '(args,(lam_body; body_annot)) := Edecompose_lam_annot t ta in
    let (ctx, args) := fresh_names [] args in
    let (tys,res_ty) := decompose_arr_n #|args| ty in
    let targs := combine args (map (print_box_type TT) tys) in
    let printed_targs :=
      map (fun '(x,ty) => parens false (string_of_name ctx x ++ " : " ++ ty)) targs in
    let printed_res_ty := print_box_type TT res_ty in
    let decl := print_const_name decl_kn ++ concat " " printed_targs in
    "let" ++ " " ++ decl ++ " : " ++ printed_res_ty ++ " = "
            ++ wrap (print_term env [] TT ctx true false lam_body body_annot).

  Definition print_init
             (TT : MyEnv.env string) (* translation table *)
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
      let targs_inner := combine args (map (print_box_type TT) tys) in
      let ctx := map (fun x => Build_context_decl x None) (rev args) in
      let printed_targs_inner :=
          map (fun '(x,ty) => parens false (string_of_name ctx x ++ " : " ++ ty)) targs_inner in
      let decl_inner := "inner " ++ concat " " printed_targs_inner in
      let printed_inner_ret_ty := print_box_type TT inner_ret_ty in
      let printed_outer_ret_ty :=
        match inner_ret_ty with
        | TApp (TInd ind) t1 =>
          if eq_kername <%% option %%> ind.(inductive_mind) then
            print_box_type TT t1
          else print_box_type TT inner_ret_ty
        | _ => print_box_type TT inner_ret_ty
        end in
      let wrap t :=
        "match " ++ t ++ " with" ++ nl ++
        "  Some v -> v"++ nl ++
        "| None -> (failwith (""""): " ++ printed_outer_ret_ty ++ ")" in
      let let_inner :=
          "let " ++ decl_inner ++ " :" ++ printed_inner_ret_ty ++ " = " ++ nl
                ++ print_term env [] TT ctx true false lam_body body_annot
                ++ " in" in
      (* if init takes no parameters, we give it a unit parameter  *)
      let printed_targs_outer := match printed_targs_inner with
                                 | _::[] | [] => let arg_name := fresh_name ctx nAnon tBox in
                                         [parens false (string_of_name ctx arg_name ++ " : unit")]
                                 | _::xs => xs
                                 end in
      (* ignore the first argument because it's a call context *)
      let decl_outer :=
        "init " ++ concat " " printed_targs_outer ++ " : " ++ printed_outer_ret_ty in
      let let_ctx := "let ctx = " ++ build_call_ctx ++ " in" in
      let inner_app := "inner " ++ concat " " ( "ctx" :: map (string_of_name ctx) (tl args)) in
      let init_args_ty := "type init_args_ty = " ++
        match tys with
        | _::[] => "unit"
        | [] => "unit"
        | _::_ => tl tys |> map (print_box_type TT)
                         |> concat " * "
      end in
      let init_wrapper_args_printed tys :=
        match tys with
        | [] => "()"
        | [ty] => " args"
        | tys => tys |> fold_right (fun _ '(i,s) => (i+1,s ++ " args." ++ string_of_nat i)) (0, "")
                     |> snd
        end in
      let init_wrapper :=
           "let init_wrapper (args : init_args_ty) ="
        ++ nl
        ++ "  init" ++ (tl tys |> init_wrapper_args_printed) in
      ret ("let " ++ decl_outer ++ " = "
                      ++ nl
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

  Definition print_cst
             (TT : MyEnv.env string) (* translation table *)
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
      Some <| print_decl TT env kn id cst.(ExAst.cst_type).2 cst_body annot
    | None => fun _ => None
    end.

  (* A wrapper type to separate declarations into type declarations ("type ... = ...")
     and constant declarations ("let x = ...") *)
  Inductive Decl a : Type :=
    | TyDecl : a -> Decl a
    | ConstDecl : a -> Decl a.
  Global Arguments TyDecl {_}.
  Global Arguments ConstDecl {_}.

  Definition print_global_decl (TT : MyEnv.env string)
             (nm : kername)
             (env : ExAst.global_env)
             (d : ExAst.global_decl) :
             (global_decl_annots box_type d) -> Decl (kername * string) :=
    match d return (global_decl_annots box_type d) -> Decl (kername * string) with
    | ExAst.ConstantDecl cst => fun annot =>
      match print_cst TT env nm cst annot with
      | Some r => ConstDecl (nm, r)
      | None =>  ConstDecl (nm, "print_global_decl ConstantDecl ERROR: " ++ string_of_kername nm)
      end
    | ExAst.InductiveDecl mib as d => fun annot =>
      match mib.(ExAst.ind_bodies) with
      | [oib] => TyDecl (nm, print_inductive nm TT oib)
      | _ => TyDecl (nm,"Only non-mutual inductives are supported; " ++ string_of_kername nm)
      end
    | TypeAliasDecl (Some (params, ty)) => fun annot =>
      let ta_nm := from_option (lookup TT (string_of_kername nm)) (print_type_name nm) in
      TyDecl (nm, print_type_declaration ta_nm params (print_box_type TT ty))
    | TypeAliasDecl None => fun _ => TyDecl (nm, "")
  end.

  Fixpoint print_global_env (TT : MyEnv.env string)
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

  (** We un-overload operations and add definitions that are more convenient to use during the pretty-printing phase. These part should be included when printing contracts that use the corresponding operations. *)

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
    "[@inline] let subTez (n : tez) (m : tez) = n - m" ;
    "[@inline] let leTez (a : tez ) (b : tez ) = a <= b" ;
    "[@inline] let ltTez (a : tez ) (b : tez ) =  a < b" ;
    "[@inline] let gtbTez (a : tez ) (b : tez ) =  a > b" ;
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
    "let get_contract_unit (a : address) : unit contract  =" ;
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
  ; "{ ctx_origin_ = Tezos.source;"
  ; "  ctx_from_ = Tezos.sender;"
  ; "  ctx_contract_address_ = Tezos.self_address;"
  ; "  ctx_contract_balance_ = Tezos.balance;"
  ; "  ctx_amount_ = Tezos.amount"
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
  <$ (* ConCert's Chain type and its instance. Currently we map all fields to Tezos.level *)
  "type chain = {"
  ; "  chain_height_     : nat;"
  ; "  current_slot_     : nat;"
  ; "  finalized_height_ : nat;"
  ; "}"
  ; ""
  ; "let dummy_chain : chain = {"
  ; "chain_height_     = Tezos.level;"
  ; "current_slot_     = Tezos.level;"
  ; "finalized_height_ = Tezos.level;"
  ; "}"
  ; ""
  ; "(* chain projections as functions *)"
  ; "let chain_height (c : chain ) = c.chain_height_"
  ; "let current_slot (c : chain ) = c.current_slot_"
  ; "let finalized_height (c : chain) = c.finalized_height_"
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
                get_contract_def; CameLIGO_Chain_CallContext].

  Definition printWrapper (contract parameter_name storage_name : string): string :=
    <$
    "type return = (operation) list * (" ++ storage_name ++ " option)" ;
    "type parameter_wrapper =" ;
    "  Init of init_args_ty" ;
    "| Call of " ++ parameter_name ++ " option" ;
    "";
    "let wrapper (param, st : parameter_wrapper * (" ++ storage_name ++ ") option) : return =" ;
    "  match param with  " ;
    "    Init init_args -> (([]: operation list), Some (init init_args))" ;
    "  | Call p -> (" ;
    "    match st with" ;
    "      Some st -> (match (" ++ contract ++ " dummy_chain cctx_instance " ++ " st p) with   " ;
    "                    Some v -> (v.0, Some v.1)" ;
    "                  | None -> (failwith ("""") : return))" ;
    "    | None -> (failwith (""cannot call this endpoint before Init has been called""): return))"
    $>.

  Definition printMain (storage_name : string) :=
    "let main (action, st : parameter_wrapper * " ++ storage_name ++ " option) : return = wrapper (action, st)".

    Definition print_default_entry_point (state_nm : kername) (receive_nm : kername) (msg_nm : kername) :=
  let st := print_type_name state_nm in
  let rec := print_const_name receive_nm in
  let msg := print_type_name msg_nm in
  <$ printWrapper rec msg st;
     "";
     printMain st $>.

End PPLigo.
