From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import PCUICtoTemplate.
From ConCert.Utils Require Import Env.
From MetaCoq.Template Require Import All.

From Coq Require Import String.
From Coq Require Import Basics.
From Coq Require Import List.


Import MCMonadNotation.

Import ListNotations.

Module TCString := bytestring.String.

Open Scope string.


Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.

Fixpoint build_prefix_table_ty (ty : type) (deps : env string) (p : string) : env string :=
  match ty with
  | tyInd nm => match lookup deps nm with
               | Some _ => []
               | None => [(nm, p)]
               end
  | tyForall _ ty1 => build_prefix_table_ty ty1 deps p
  | tyApp ty1 ty2 => (build_prefix_table_ty ty1 deps p
                      ++ build_prefix_table_ty ty2 deps p)%list
  | tyVar _ => []
  | tyRel _ => []
  | tyArr ty1 ty2 => (build_prefix_table_ty ty1 deps p
                      ++ build_prefix_table_ty ty2 deps p)%list
  end.

Open Scope list.

Definition build_prefix_table_gd (gd : global_dec) (deps : env string) (p : string): env string :=
  match gd with
  | gdInd nm i ctors b =>
    concat (map (fun '(_,tys) => concat (map (fun '(_,ty) => build_prefix_table_ty ty deps p) tys)) ctors)
  end.

Program Definition dec_pair_string (p1 p2 : string × string) :
  {p1 = p2} + {p1 <> p2} :=
  _. Next Obligation.
       specialize (String.string_dec s1 s) as H1.
       specialize (String.string_dec s2 s0) as H2.
       destruct H1; subst. destruct H2; subst; auto.
       right. intro HH. inversion HH. contradiction.
       right. intro HH. inversion HH. contradiction.
       Defined.


Definition prefixes_gds (gds : list global_dec) (deps : env string) (p : string)
  : env string :=
  nodup dec_pair_string (concat (map (fun gd => build_prefix_table_gd gd deps p) gds)).


Fixpoint build_prefix_table (e : expr) (deps : env string) (p : string) : env string :=
  match e with
  | eRel _ | eVar _ => []
  | eLambda nm ty e1 =>
    build_prefix_table_ty ty deps p ++ build_prefix_table e1 deps p
  | eTyLam nm e1 => build_prefix_table e1 deps p
  | eLetIn nm e1 ty e2 =>
    build_prefix_table e1 deps p
    ++ build_prefix_table_ty ty deps p
    ++ build_prefix_table e2 deps p
  | eApp e1 e2 =>
    build_prefix_table e1 deps p
    ++ build_prefix_table e2 deps p
  | eConstr ind_nm ctor_nm =>
    match lookup deps ind_nm with
    | Some _ => []
    | None => [(ind_nm, p)]
    end
  | eConst nm =>
    match lookup deps nm with
    | Some _ => []
    | None => [(nm, p)]
    end
  | eCase (ind_nm, tys) ty e1 brs =>
    let ps := match lookup deps ind_nm with
              | Some _ => []
              | None => [(ind_nm, p)]
              end in
    ps ++ concat (map (fun ty => build_prefix_table_ty ty deps p) tys)
       ++ build_prefix_table_ty ty deps p
       ++ build_prefix_table e1 deps p
       ++ concat (map (fun e => build_prefix_table e.2 deps p) brs)
  | eFix fix_nm nm ty1 ty2 e1 =>
    build_prefix_table_ty ty1 deps p
    ++ build_prefix_table_ty ty2 deps p
    ++ build_prefix_table e1 deps p
  | eTy ty => build_prefix_table_ty ty deps p
  end.

Definition prefixes (defs : list (string × expr)) (deps : env string) (p : string) :=
  nodup dec_pair_string (concat (map (fun def => build_prefix_table def.2 deps p) defs)).

Definition stdlib_prefixes : env string :=
  fold_left
    (fun l gd => match gd with
              | gdInd ty_name _ _ _ =>
                  let (mp,nm) := kername_of_string ty_name
                  in ( TCString.to_string nm, (PCUICTranslate.string_of_modpath mp ++ "@")%string) :: l
              end) StdLib.Σ [].

(** We translate and unquote a list of data type declarations in the TemplateMonad *)
Fixpoint translateData_ (ps : env string) (es : list global_dec) : TemplateMonad unit :=
  match es with
  | [] => tmPrint "Done."
  | e :: es' =>
    let e' := add_prefix_gd e ps in
    coq_data <- tmEval lazy (global_to_tc e') ;;
    (* tmPrint coq_data *)
    tmMkInductive false coq_data;;
    translateData_ ps es'
  end.

(** [deps] is a list of dependencies for which prefixes are already defined
    (they come from a different module, not from the one where [es] is defined) *)
Definition translateData (deps : env string) (es : list global_dec) :=
  mp_ <- tmCurrentModPath tt ;;
  let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
  let ps := prefixes_gds es (stdlib_prefixes ++ deps) mp in
 (* NOTE: it is important that we first put [stdlib_prefixes]
    otherwise they might be shadowed by some definitions from [ps] *)
  translateData_ (stdlib_prefixes ++ deps ++ ps) es.


(** This function translates and unquotes a list of function definitions *)
Fixpoint translateDefs_ (ps : env string) (Σ : Ast.global_env) (es : list (string * expr)) :=
  match es with
  | [] => tmPrint "Done."
  | (name, e) :: es' =>
    coq_expr <- tmEval lazy
                      (expr_to_tc Σ (reindexify 0 (add_prefix e ps))) ;;
    (* tmPrint coq_expr;; *)
    print_nf ((add_prefix e ps));;
    tmMkDefinition (TCString.of_string name) coq_expr;;
    print_nf ("Unquoted: " ++ name)% string;;
    translateDefs_ ps Σ es'
  end.

Definition translateDefs (deps : env string) (Σ : Ast.global_env) (es : list (string * expr)) :=
  mp_ <- tmCurrentModPath tt ;;
  let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
  let ps := prefixes es deps mp in
  print_nf ("Exported definitions: " ++ Strings.String.concat ", " (map fst ps))%string;;
  tmDefinition "exported"%bs ps ;;
  (* NOTE: it is important that we first put [stdlib_prefixes]
     otherwise they might be shadowed by some definitions from [ps] *)
  let Σ := (StdLib.Σ ++ add_prefix_genv Σ (stdlib_prefixes ++ deps ++ ps))%list in
  translateDefs_ (stdlib_prefixes ++ deps ++ ps) Σ es.

Definition define_mod_prefix :=
  mp_ <- tmCurrentModPath tt ;;
  let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
  tmDefinition "mod_prefix"%bs mp.
