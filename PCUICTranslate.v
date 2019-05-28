Require Import String List.
From PCUIC Require Import PCUICAst.
From Template Require Import BasicAst utils.
Require Import Ast.

Import ListNotations.

Module P := PCUICAst.


Fixpoint type_to_term (ty : type) : term :=
  match ty with
  | tyInd i => tInd (mkInd i 0) []
  | tyArr t1 t2 => tProd nAnon (type_to_term t1) (type_to_term t2)
  end.


Fixpoint pat_to_lam (tys : list (name * type)) (body : term) : term :=
  match tys with
    [] => body
  | (n,ty) :: tys' => tLambda (nNamed n) (type_to_term ty) (pat_to_lam tys' body)
  end.

Fixpoint pat_to_elam (tys : list (name * type)) (body : expr) : expr :=
  match tys with
    [] => body
  | (n,ty) :: tys' => eLambda n ty (pat_to_elam tys' body)
  end.


(* Resolves a pattern by looking up in the global environment
   and returns an index of the consrutor in the list of contrutors for the given iductive and
   a list of pairs mapping pattern variable names to the types of the constructor arguments *)
Definition resolve_pat_arity (Σ : global_env) (ind_name : name) (p : pat) : nat * list (name * type) :=
  (* NOTE: in lookup failed we return a dummy value [(0,("",[]))]
     to make the function total *)
  let o_ci := resolve_constr Σ ind_name p.(pName) in
  let (i, nm_tys) := from_option o_ci (0,[]) in
  (i, combine p.(pVars) nm_tys).

Definition trans_branch (bs : list (pat * P.term))
           (c : name * list type) :=
  let dummy := (0, tVar "error") in
  let (nm, tys) := c in
  let o_pt_e := find (fun x =>(fst x).(pName) =? nm) bs in
  match o_pt_e with
    | Some pt_e => if (Nat.eqb (#|(fst pt_e).(pVars)|) (#|tys|)) then
                    let vars_tys := combine (fst pt_e).(pVars) tys in
                    (length (fst pt_e).(pVars), pat_to_lam vars_tys (snd pt_e))
                  else dummy
    | None => dummy
  end.

Definition fun_prod {A B C D} (f : A -> C) (g : B -> D) : A * B -> C * D :=
  fun x => (f (fst x), g (snd x)).


Definition expr_to_pcuic (Σ : global_env) : expr -> P.term :=
  fix expr_to_pcuic e :=
  match e with
  | eRel i => tRel i
  | eVar nm => tVar nm
  | eLambda nm ty b => tLambda (nNamed nm) (type_to_term ty) (expr_to_pcuic b)
  | eLetIn nm e1 ty e2 => tLetIn (nNamed nm) (expr_to_pcuic e1) (type_to_term ty) (expr_to_pcuic e2)
  | eApp e1 e2 => tApp (expr_to_pcuic e1) (expr_to_pcuic e2)
  | eConstr t i => match (resolve_constr Σ t i) with
                  | Some c => tConstruct (mkInd t 0) (fst c) []
                  (* FIXME: a hack to make the function total *)
                  | None => tConstruct (mkInd (t ++ ": no declaration found.") 0) 0 []
                     end
  | eConst nm => tConst nm []
  | eCase nm_i ty e bs =>
    let (nm,i) := nm_i in
    let typeInfo := tLambda nAnon (tInd (mkInd nm 0) []) (type_to_term ty) in
    let cs := from_option (resolve_inductive Σ nm) [] in
    let tbs := map (fun_prod id expr_to_pcuic) bs in
    let branches := map (trans_branch tbs) cs in
    (* TODO: no translation for polymorphic types, the number of parameters is zero *)
    tCase (mkInd nm 0, 0) typeInfo (expr_to_pcuic e) branches
  | eFix nm nv ty1 ty2 b =>
    let tty1 := type_to_term ty1 in
    let tty2 := type_to_term ty2 in
    let ty := tProd nAnon tty1 tty2 in
    let body := tLambda (nNamed nv) tty1 (expr_to_pcuic b) in
    tFix [(mkdef _ (nNamed nm) ty body 0)] 0
  end.
