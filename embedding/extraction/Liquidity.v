From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Basics.
From Coq Require Import Bool.
From ConCert.Utils Require Extras.
From ConCert.Utils Require Import Env.
From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import Prelude.

Import ListNotations.

Open Scope string.

Module TCString := bytestring.String.

Coercion TCString.to_string : TCString.t >-> string.

(* Names for two mandatory arguments for the main function.
   Used when generating code for [wrapper] and for the entrypoint *)
Definition MSG_ARG := "msg".
Definition STORAGE_ARG := "st".

Record LiquidityModule :=
  { datatypes : list global_dec ;
    storage : type ;
    message : type ;
    functions : list (string * expr) ;
    (* the [init] function must return [storage] *)
    init : expr;
    (* the [main] function must be of type
       message * storage -> option (list SimpleActionBody * storage) *)
    main: string;
    (* extra arguments to the main function for using in the wrapper;
       note that two mandatory arguments (MSG_ARG : message) and (STORAGE_ARG : storage)
       should not be the list *)
    main_extra_args : list string;
  }.

Definition newLine :=
  String (Ascii.Ascii false true false true false false false false) EmptyString.
Definition inParens s := "(" ++ s ++ ")".
Definition inCurly s := "{" ++ s ++ "}".
Definition ofType e ty := e ++ " : " ++ ty.
Definition sep := concat.

Definition look (e : env string) (s : string) : option string :=
  lookup e s.

Fixpoint liquidifyTy (TT : env string) (ty : type) : string :=
  match ty with
  | tyInd nm =>
    (* ignore module path on printing *)
    let (_, nm') := PCUICTranslate.kername_of_string nm in
    TCString.to_string (Extras.with_default nm' (option_map TCString.of_string (look TT nm)))
  | tyForall x b => "forall " ++ "'" ++ x ++ liquidifyTy TT b
  (* is it a product? *)
  | tyApp ty1 ty2 =>
    match ty1 with
      | (tyApp (tyInd ty_nm) A) =>
        (* ignore module path on printing *)
        let (_, nm') := PCUICTranslate.kername_of_string ty_nm in
        if TCString.to_string nm' =? "prod" then
          inParens (liquidifyTy TT A ++ " * " ++ liquidifyTy TT ty2)
        else inParens (liquidifyTy TT ty2 ++ " " ++ liquidifyTy TT ty1)
      | _ => inParens (liquidifyTy TT ty2 ++ " " ++ liquidifyTy TT ty1)
    end
  | tyVar x => "'" ++ x
  | tyRel x => "Error: indices are not supported"
  | tyArr ty1 ty2 => liquidifyTy TT ty1 ++ " -> " ++ liquidifyTy TT ty2
  end.

Definition printRecord (TT : env string) (c : constr) :=
  let '(_, args) := c in
  let tmp := map (fun '(nm, ty) => ofType (Extras.with_default "" nm) (liquidifyTy TT ty)) args in
  inCurly (sep " ; " tmp).

Definition is_nil {A} (l : list A) : bool :=
  match l with
  | nil => true
  | cons _ _ => false
  end.

Definition printCtorTy (TT : env string) (args : list (option ename * type)) :=
  if is_nil args then ""
  else " of " ++ sep " * " (map (compose (liquidifyTy TT) snd) args).

Definition liquidifyInductive (TT : env string) (gd : global_dec) : string :=
  match gd with
  | gdInd nm nparams ctors is_record =>
    (* ignore module path on printing *)
    let (_, nm') := PCUICTranslate.kername_of_string nm in
    "type " ++ nm' ++ " = " ++
    if is_record then
      Extras.with_default "Not a Record!" (head (map (printRecord TT) ctors))
    else
      fold_right
        (fun '(nm, ctor_info) s => "| " ++ nm ++ printCtorTy TT ctor_info ++ newLine ++ s) "" ctors
  end.

Definition printPat (p : pat) :=
  (* pairs don't need a constructor name *)
  let name := if String.eqb (pName p) "pair" then "" else pName p in
  match (pVars p) with
  | [] => name
  | _ :: _ => name ++ " " ++ inParens (sep "," (pVars p))
  end.

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


Definition isTruePat (p : pat) :=
  let '(pConstr nm v) := p in nm =? "true".

Definition isFalsePat (p : pat) :=
  let '(pConstr nm v) := p in nm =? "false".

(** We assume that before printing the Liquidity code
    [erase] has been applied to the expression *)

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
    let default_app := go e1 ++ " " ++ inParens (go e2) in
    match e1 with
    | eApp (eConstr _ ctor) e1' =>
      (* is it a pair? *)
      if ctor =? "pair" then inParens (go e1' ++ ", " ++ go e2)
      else
      (* is it a transfer? *)
        if String.eqb "Act_transfer" ctor
        then "Contract.call " ++ go e1' ++ " " ++ go e2 ++ " "
                              ++ "default" ++ " ()"
        else default_app
    | eConst cst =>
      (* ignore module path *)
      let (_, cst') := PCUICTranslate.kername_of_string cst in
      (* is it a first projection? *)
      if cst' =? "fst" then go e2 ++ "." ++ inParens ("0")
      else
        (* is it a second projection? *)
        if cst' =? "snd" then go e2 ++ "." ++ inParens ("1")
      else default_app
    | _ => default_app
    end
  | eConstr _ ctor =>
    (* is it a list constructor [nil]? *)
    (* TODO: add [cons] *)
    if String.eqb "nil" ctor then "[]"
    else (* is it an empty map? *)
      if String.eqb "mnil" ctor then "Map []"
      else (* Is it zero amount? *)
        if String.eqb "Z0" ctor then "0DUN"
        else (* Is it unit? *)
          if String.eqb "tt" ctor then "()"
          else ctor
  | eConst cst =>
    (* ignore module path *)
    let (_, cst') := PCUICTranslate.kername_of_string cst in
    Extras.with_default cst' (option_map TCString.of_string (look TT cst))
  | eCase (ind,_) _ d bs =>
    match bs with
    | [b1; b2] => (* Handling if-then-else *)
      (* ignore module path *)
      let (_, ind') := PCUICTranslate.kername_of_string ind in
      if (ind' =? "bool") then
        if (isTruePat (fst b1)) && (isFalsePat (fst b2)) then
          "if " ++ inParens (go d)
                ++ " then " ++ (go (snd b1))
                ++ " else " ++ (go (snd b2))
        else if (isTruePat (fst b2)) && (isFalsePat (fst b1)) then
               "if " ++ inParens (go d)
                     ++ " then " ++ (go (snd b2))
                     ++ " else " ++ (go (snd b1))
             else "ERROR: wrong mathing on bool"
      else (* default case translation *)
        let sbs := map (fun '(p,e) => (printPat p, go e)) bs in
        "match " ++ go d ++ " with " ++ newLine ++ printBranches sbs
    | _ => (* default case translation *)
      let sbs := map (fun '(p,e) => (printPat p, go e)) bs in
      "match " ++ go d ++ " with " ++ newLine ++ printBranches sbs
    end
  | eFix f x _ _ b => "let rec " ++ f ++ " " ++ x ++ " = " ++ go b
  | eTy x => ""
  end.

Fixpoint to_glob_def (e : expr) : list (ename * type) * expr :=
  match e with
  | eRel _ => ([],e)
  | eVar _ => ([],e)
  | eLambda x ty b => let (vars, e') := to_glob_def b in
                     ((x,ty) :: vars, e')
  | eTyLam _ _ => ([],e)
  | eLetIn x x0 x1 x2 => ([],e)
  | eApp x x0 => ([],e)
  | eConstr x x0 => ([],e)
  | eConst x => ([],e)
  | eCase x x0 x1 x2 => ([],e)
  | eFix x x0 x1 x2 x3 => ([],e)
  | eTy x => ([],e)
  end.

Definition LiquidityPrelude :=
       "let[@inline] addN (n : nat) (m : nat) = n + m"
    ++ newLine
    ++ "let[@inline] addTez (n : tez) (m : tez) = n + m"
    ++ newLine
    ++ "let[@inline] andb (a : bool ) (b : bool ) = a & b"
    ++ newLine
    ++ "let[@inline] eqTez (a : tez ) (b : tez ) = a = b"
    ++ newLine
    ++ "let[@inline] lebN (a : nat ) (b : nat ) = a <= b"
    ++ newLine
    ++ "let[@inline] ltbN (a : nat ) (b : nat ) = a < b"
    ++ newLine
    ++ "let[@inline] lebTez (a : tez ) (b : tez ) = a<=b"
    ++ newLine
    ++ "let[@inline] ltbTez (a : tez ) (b : tez ) = a<b"
    ++ newLine
    ++ "let[@inline] eqb_addr (a1 : address) (a2 : address) = a1 = a2"
    ++ newLine
    ++ "let[@inline] eqb_time (a1 : timestamp) (a2 : timestamp) = a1 = a2"
    ++ newLine
    ++ "let[@inline] leb_time (a1 : timestamp) (a2 : timestamp) = a1 <= a2"
    ++ newLine
    ++ "let[@inline] ltb_time (a1 : timestamp) (a2 : timestamp) = a1 < a2"
    ++ newLine
    ++ "let[@inline] cons x xs = x :: xs".

Definition printWrapperBody (f_call : string) :=
  "match " ++ f_call
    ++ " with" ++ newLine
    ++ "| Some v -> v"
    ++ "| None -> failwith ()".


Definition printWrapper (TTty: env string) (msgTy : type) (storageTy : type)
           (extra_args : list string) (contract : string): string :=
  let mainDomainType :=
      inParens (ofType MSG_ARG (liquidifyTy TTty msgTy))
               ++ inParens (ofType "st" (liquidifyTy TTty storageTy)) in
  let _extra_args := sep " " extra_args in
  "let wrapper "
    ++ mainDomainType
    ++ " = "
    ++ printWrapperBody (contract ++ " " ++ sep " " [MSG_ARG; STORAGE_ARG]
                                  ++ " " ++ _extra_args).

(* NOTE: Polymorphic definitions might not behave well in Liquidity *)
Definition print_glob TT TTty (def_clause : string) (def_name : string)
                      (gd : (list (ename * type)) * expr) : string :=
  def_clause ++ " " ++ def_name ++ " "
             ++ sep " " (map (fun p => inParens (ofType (fst p) (liquidifyTy TTty (snd p)))) (fst gd))
             ++" = " ++ liquidify TT TTty (snd gd).

Definition simpleCallCtx :=
  "(Current.time (), (Current.sender (), (Current.amount (), Current.balance ())))".

Definition printLiqDef (TT TTty: env string) (def_name : string) (e : expr) :=
  print_glob TT TTty "let" def_name (to_glob_def (erase e)).


Definition printLiqInit (TT TTty: env string) (def_name : string) (e : expr) :=
  let (args, body) := to_glob_def (erase e) in
  (** We expect that the last parameter of the [init] is _always_ the simple call context [CallCtx] *)
  let init_params := firstn (List.length args - 1) args in
  "let%init" ++ " " ++ "storage "
             ++ sep " " (map (fun p => inParens (ofType (fst p) (liquidifyTy TTty (snd p)))) init_params)
             ++ " = " ++ newLine
             (* FIXME: this is currently a workaround, since [init] cannot refer to any global definition *)
             ++ "let eqTez (a : tez ) (b : tez ) = a = b in"
             ++ newLine
             ++ printLiqDef TT TTty "f" e ++ newLine
             ++ "in" ++ newLine
             ++ printWrapperBody ("f " ++ sep " " (map fst init_params) ++ " " ++ simpleCallCtx).

Definition liquidifyModule (TT TTty: env string) (module : LiquidityModule) :=
  let dt := sep newLine (map (liquidifyInductive TTty) module.(datatypes)) in
  let st := liquidifyTy TTty module.(storage) in
  let fs := sep (newLine ++ newLine) (map (fun '(defName, body) => printLiqDef TT TTty defName body) module.(functions)) in
  let mainDomainType := inParens (ofType MSG_ARG (liquidifyTy TTty module.(message)))
        ++ inParens (ofType STORAGE_ARG (liquidifyTy TTty module.(storage))) in
  let wrapper := printWrapper TTty module.(message) module.(storage) module.(main_extra_args) module.(main) in
  let init := printLiqInit TT TTty "storage" module.(init) in
  let main := "let%entry main " ++ mainDomainType ++ " = wrapper " ++ sep " " [MSG_ARG; STORAGE_ARG] in
  newLine
    ++ LiquidityPrelude ++ newLine
    ++ dt ++ newLine
    ++ "type storage = " ++ st ++ newLine
    ++ init ++ newLine
    ++ fs ++ newLine
    ++ wrapper ++ newLine
    ++ main.
