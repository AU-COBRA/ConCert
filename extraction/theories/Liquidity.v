From Coq Require Import List String Basics ZArith.
From ConCert Require Import Ast
     Notations Utils Prelude SimpleBlockchain MyEnv.

Import ListNotations.

Open Scope string.

Record LiquidityModule :=
  { datatypes : list global_dec ;
    storage : type ;
    message : type ;
    functions : list (string * expr) ;
    (* the [main] function must be of type
       message * storage -> option (list SimpleActionBody * storage) *)
    main: string ;}.

Definition newLine := String (Ascii.Ascii false true false true false false false false) EmptyString.
Definition inParens s := "(" ++ s ++ ")".
Definition inCurly s := "{" ++ s ++ "}".
Definition ofType e ty := e ++ " : " ++ ty.
Definition sep :=  concat.

Definition look (e : env string) (s : string) : option string :=
  lookup e s.

Fixpoint liquidifyTy (TT : env string) (ty : type) : string :=
  match ty with
  | tyInd nm => from_option (look TT nm) nm
  | tyForall x b => "forall " ++ "'" ++ x ++ liquidifyTy TT b
  (* is it a product? *)
  | tyApp (tyApp (tyInd "prod") A) B =>
    liquidifyTy TT A ++ " * " ++ liquidifyTy TT B
  | tyApp ty1 ty2 =>
    inParens (liquidifyTy TT ty1 ++ " " ++ liquidifyTy TT ty2)
  | tyVar x => x
  | tyRel x => "Error: indices are not supported"
  | tyArr ty1 ty2 => liquidifyTy TT ty1 ++ " -> " ++ liquidifyTy TT ty2
  end.

Definition printRecord (TT : env string) (c : constr) :=
  let '(_, args) := c in
  let tmp := map (fun '(nm, ty) => ofType (from_option nm "") (liquidifyTy TT ty)) args in
  inCurly (sep " ; " tmp).

Definition printCtorTy (TT : env string) (args : list (option ename * type)) :=
  sep " * " (map (compose (liquidifyTy TT) snd) args).

Definition liquidifyInductive (TT : env string) (gd : global_dec) : string :=
  match gd with
  | gdInd nm nparams ctors is_record =>
    "type " ++ nm ++ " = " ++
    if is_record then
      from_option (head (map (printRecord TT) ctors)) "Not a Record!"
    else
      fold_right
        (fun '(nm, ctor_info) s => "| " ++ nm ++ " of "
                                     ++ printCtorTy TT ctor_info ++ newLine ++ s) "" ctors
  end.

Definition printPat (p : pat) :=
  (* pairs don't need a constructor name *)
  let name := if String.eqb (pName p) "pair" then "" else pName p in
  name ++ " " ++ inParens (sep "," (pVars p)).

Definition printBranches (bs : list (string * string)) :=
  fold_right (fun '(p,e) s => "|" ++ p ++ " -> " ++ e ++ newLine ++ s) "" bs.

Definition eqb_opt (key : string) (o : option string) : bool :=
  match o with
  | Some s => String.eqb s key
  | None => false
  end.

(** Will be used in the future to properly handle records *)
Fixpoint isProjection (field : string) (Σ : list global_dec) : bool :=
  match Σ with
  | [] => false
  | cons entry tl =>
    match entry with
      gdInd nm _ ctors isRec =>
      if isRec then
        match head ctors with
        | Some (_, args) => existsb (compose (eqb_opt field) fst) args
        | None => isProjection field tl
        end
      else isProjection field tl
    end
  end.

Fixpoint erase (e : expr) : expr :=
  match e with
  | eRel x => e
  | eVar x => e
  | eLambda x ty b => eLambda x ty (erase b)
  | eTyLam x e => erase e
  | eLetIn x e1 ty e2 => eLetIn x (erase e1) ty (erase e2)
  | eApp e1 e2 => match e2 with
                 | eTy _ => erase e1
                 | _ => eApp (erase e1) (erase e2)
                 end
  | eConstr x x0 => e
  | eConst x => e
  | eCase ty1 ty2 d bs => eCase ty1 ty2 (erase d) (map (fun '(p,b) => (p, erase b)) bs)
  | eFix f x ty1 ty2 e => eFix f x ty1 ty2 (erase e)
  | eTy x => e
  end.

(** We assume that before printing the Liquidity code [erase] has been applied to the expression *)

Definition liquidify (TT TTty : env string ) : expr -> string :=
  fix go (e : expr) : string :=
  match e with
  | eRel _ => "Error : indices are not supported"
  | eVar v => v
  (* we ignore typing annotations *)
  | eLambda x _ b => inParens ("fun " ++ x ++ " -> " ++ newLine ++ go b)
  | eTyLam x b => go b
  | eLetIn x e1 _ e2 => "let " ++ x ++ " = " ++ go e1 ++ " in " ++ go e2
  | eApp e1 e2 =>
    match e1 with
    (* is it a pair ? *)
    | eApp (eConstr _ ctor) e1' =>
      if String.eqb ctor "pair" then inParens (go e1' ++ ", " ++ go e2)
      else go e1 ++ " " ++ inParens (go e2)
    | _ => go e1 ++ " " ++ inParens (go e2)
    end
  | eConstr _ ctor =>
    (* is is list constructor [nil]? *)
    (* TODO: add [cons] *)
    if String.eqb "nil" ctor then "[]"
    else ctor
  | eConst cst =>
    match look TT cst with
    | Some op => op
    | _ => cst
    end
  | eCase _ _ d bs =>
    let sbs := map (fun '(p,e) => (printPat p, go e)) bs in
    "match " ++ go d ++ " with " ++ printBranches sbs
  | eFix f x _ _ b => "let rec " ++ f ++ " " ++ x ++ " = " ++ go b
  | eTy x => ""
  end.

Definition LiquidityPrelude :=
       "let[@inline] fst (p : 'a * 'b) : 'a = p.(0)"
    ++ newLine
    ++ "let[@inline] snd (p : 'a * 'b) : 'b = p.(1)"
    ++ newLine
    ++ "let[@inline] addN (n : nat) (m : nat) = n + m"
    ++ newLine
    ++ "let[@inline] addTez (n : tez) (m : tez) = n + m".

Definition printWrapper (TTty: env string) (msgTy : type) (storageTy : type) (contract : string): string :=
  let mainDomainType :=
      inParens (ofType "param" (liquidifyTy TTty msgTy))
               ++ inParens (ofType "st" (liquidifyTy TTty storageTy)) in
  "let wrapper "
        ++ mainDomainType
        ++ " = "
        ++ "match " ++ contract ++ " param st" ++ " with"
        ++ "| Some v -> v"
        ++ "| None -> failwith ()".

Definition eraseLiq (TT TTty: env string) := compose (liquidify TT TTty) erase.

Definition liquidifyModule (TT TTty: env string) (module : LiquidityModule) :=
  let dt := sep newLine (map (liquidifyInductive TTty) module.(datatypes)) in
  let st := liquidifyTy TTty module.(storage) in
  let fs := sep newLine (map (fun '(defName, body) => "let " ++ defName ++ " = " ++ eraseLiq TT TTty body) module.(functions)) in
  let mainDomainType := inParens (ofType "param" (liquidifyTy TTty module.(message)))
        ++ inParens (ofType "st" (liquidifyTy TTty module.(storage))) in
  let wrapper := printWrapper TTty module.(message) module.(storage) module.(main) in
  let main := "let%entry main " ++ mainDomainType ++ " = wrapper param st" in
  newLine
    ++ LiquidityPrelude ++ newLine
    ++ dt ++ newLine
    ++ "type storage = " ++ st ++ newLine
    ++ fs ++ newLine
    ++ wrapper ++ newLine
    ++ main.