From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import String.

From MetaCoq Require Import monad_utils.
From MetaCoq Require Import MCPrelude.
From MetaCoq Require Import MCProd.
From MetaCoq Require Import MCString.
From MetaCoq Require Import MCSquash.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import SafeErasureFunction.
From MetaCoq.Erasure Require Import SafeTemplateErasure.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.SafeChecker Require Import SafeTemplateChecker.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import StringExtra.

Module T := MetaCoq.Template.Ast.
Module P := MetaCoq.PCUIC.PCUICAst.
Module E := MetaCoq.Erasure.EAst.
Module TUtil := MetaCoq.Template.AstUtils.
Module PUtil := MetaCoq.PCUIC.PCUICAstUtils.
Module PT := MetaCoq.PCUIC.PCUICTyping.
Module EF := MetaCoq.Erasure.SafeErasureFunction.
Module T2P := MetaCoq.PCUIC.TemplateToPCUIC.

Local Open Scope string.
Import ListNotations.
Import MonadNotation.

(* This is here so that we get a typing error if Chain ever changes *)
Check (fun _ => eq_refl) :
  forall chain,
    Blockchain.account_balance chain = let (_, _, _, f) := chain in f.
Local Open Scope bool.
Import E.

Definition kername_of_string (s : string) : kername :=
  let l := rev (str_split "." s) in
  (MPfile (tl l), hd "" l).

Definition ConCertChain : kername :=
  Eval compute in kername_of_string "ConCert.Execution.Blockchain.Chain".

Definition uses_account_balance (t : term) : bool :=
  (fix f (t : term) (ab_funcs : list bool) :=
     match t with
     | tBox => false
     | tRel i => nth i ab_funcs false
     | tVar _ => false
     | tEvar _ ts => fold_left (fun b t => b || f t ab_funcs) ts false
     | tLambda _ t => f t (false :: ab_funcs)
     | tLetIn _ val body => f val ab_funcs || f body (false :: ab_funcs)
     | tApp head body => f head ab_funcs || f body ab_funcs
     | tConst _ => false
     | tConstruct _ _ => false
     | tCase (ind, _) disc brs =>
       f disc ab_funcs ||
       if eq_kername (inductive_mind ind) ConCertChain then
         match brs with
         | [(4, tLambda _ (tLambda _ (tLambda _ (tLambda _ t))))] =>
           f t (true :: false :: false :: false :: ab_funcs)
         | _ => fold_left (fun b '(_, t) => b || f t ab_funcs) brs false
         end
       else
         fold_left (fun b '(_, t) => b || f t ab_funcs) brs false
     | tProj _ t => f t ab_funcs
     | tFix defs _
     | tCoFix defs _ =>
       let ab_funcs := (repeat false (List.length defs) ++ ab_funcs)%list in
       fold_left (fun b d => b || f (dbody d) ab_funcs) defs false
     end) t [].

Definition result_of_typing_result
           {A}
           (Σ : P.global_env_ext)
           (tr : typing_result A) : result A string :=
  match tr with
  | Checked a => ret a
  | TypeError err => Err (string_of_type_error Σ err)
  end.

Definition string_of_env_error Σ e :=
  match e with
  | IllFormedDecl s e =>
    "IllFormedDecl " ++ s ++ "\nType error: " ++ string_of_type_error Σ e
  | AlreadyDeclared s => "Alreadydeclared " ++ s
  end%string.

Definition result_of_EnvCheck {A} (ec : EnvCheck A) : result A string :=
  match ec with
  | CorrectDecl a => ret a
  | EnvError Σ err => Err (string_of_env_error Σ err)
  end.

Definition result_of_option {A} (o : option A) (err : string) : result A string :=
  match o with
  | Some a => ret a
  | None => Err err
  end.

(* These next functions deal with specializing globals that might
   refer to a ChainBase variable in the context. They work by
   replacing uses of it with the specified term, and by removing it
   from applications. For example:
   Inductive Foo (cb : ChainBase) := ctor (addr : Address cb).
   Definition a (cb : ChainBase) (n : nat) := n.
   Definition b (cb : ChainBase) (addr : Foo cb) (n : N) :=
     a cb (N.to_nat n).

   becomes
   Inductive Foo := ctor (addr : Address replacement_term).
   Definition a (n : nat) := n.
   Definition b (addr : Foo) (n : N) :=
     a (N.to_nat n).

   Note: Only specializes ChainBase when it is the very first abstraction.  *)
Module ChainBaseSpecialization.
  Import P.
  Definition ChainBase_kername : kername :=
    Eval compute in kername_of_string "ConCert.Execution.Blockchain.ChainBase".

  Section ChainBaseSpecialization.
    Context (replacement_term : term).

    Definition contains (n : kername) : list kername -> bool :=
      existsb (eq_kername n).

    Inductive VarInfo :=
    (* this var is a ChainBase that should be replaced by the replacement term *)
    | replace
    (* this var has type ChainBase -> ... and its first argument should be removed *)
    | specialize
    | none.

    Fixpoint specialize_term
             (specialized : list kername) : list VarInfo -> term -> result term string :=
      fix f Γ t :=
        match t with
        | tRel n =>
          vi <- result_of_option (nth_error Γ n) "Unbound tRel";;
          match vi with
          | replace => ret replacement_term
          | specialize => Err "Unapplied tRel that should be specialized appears in term"
          | none => ret t
          end
        | tVar _ => ret t
        | tEvar n ts =>
          ts <- monad_map (f Γ) ts;;
          ret (tEvar n ts)
        | tSort univ =>
          ret t
        | tProd name ty body =>
          ty <- f Γ ty;;
          body <- f (none :: Γ) body;;
          ret (tProd name ty body)
        | tLambda name ty body =>
          ty <- f Γ ty;;
          body <- f (none :: Γ) body;;
          ret (tLambda name ty body)
        | tLetIn name val val_ty body =>
          val <- f Γ val;;
          val_ty <- f (none :: Γ) val_ty;;
          body <- f (none :: Γ) body;;
          ret (tLetIn name val val_ty body)
        | tApp (tConst name _ as head) arg
        | tApp (tInd {| inductive_mind := name |} _ as head) arg
        | tApp (tConstruct {| inductive_mind := name |} _ _ as head) arg =>
          if contains name specialized then
            ret head
          else
            arg <- f Γ arg;;
            ret (tApp head arg)
        | tApp (tRel i as head) arg =>
          vi <- result_of_option (nth_error Γ i) "Unbound tRel";;
          match vi with
          | replace => Err "Unexpected application"
          | specialize => ret (tRel (i - 1)) (* removed chain base inbetween, hacky *)
          | none => arg <- f Γ arg;;
                    ret (tApp head arg)
          end
        | tApp head arg =>
          head <- f Γ head;;
          arg <- f Γ arg;;
          ret (tApp head arg)
        | tConst name _
        | tInd {| inductive_mind := name |} _
        | tConstruct {| inductive_mind := name |} _ _ =>
          if contains name specialized then
            Err ("Unapplied '"
                   ++ string_of_kername name
                   ++ "' (or constructor) appears in term; this needs to be specialized")
          else
            ret t
        | tCase ind ret_ty disc brs =>
          ret_ty <- f Γ ret_ty;;
          disc <- f Γ disc;;
          brs <- monad_map (fun '(ar, t) => t <- f Γ t;; ret (ar, t)) brs;;
          ret (tCase ind ret_ty disc brs)
        | tProj proj body =>
          body <- f Γ body;;
          ret (tProj proj body)
        | tFix defs i =>
          let Γ := (repeat none (List.length defs) ++ Γ)%list in
          defs <- monad_map (fun (d : def term) =>
                               dtype <- f Γ (dtype d);;
                               dbody <- f Γ (dbody d);;
                               ret {| dname := dname d;
                                      dtype := dtype;
                                      dbody := dbody;
                                      rarg := rarg d |}) defs;;
          ret (tFix defs i)
        | tCoFix defs i =>
          let Γ := (repeat none (List.length defs) ++ Γ)%list in
          defs <- monad_map (fun (d : def term) =>
                               dtype <- f Γ (dtype d);;
                               dbody <- f Γ (dbody d);;
                               ret {| dname := dname d;
                                      dtype := dtype;
                                      dbody := dbody;
                                      rarg := rarg d |}) defs;;
          ret (tCoFix defs i)
        end.

    Definition specialize_body
               (specialized : list kername)
               (name : kername)
               (Γ : list VarInfo)
               (remove : bool)
               (t : term) : result term string :=
      match remove, t with
      | true, tLambda _ _ body =>
        map_error (fun s => "While specializing body in " ++ string_of_kername name ++ ": " ++ s)
                  (specialize_term specialized (replace :: Γ) body)

      | true, _ => Err ("Expected lambda in " ++ string_of_kername name ++ ", got" ++ nl ++ PUtil.string_of_term t)
      | false, _ => specialize_term specialized Γ t
      end.

    Definition specialize_type
               (specialized : list kername)
               (name : kername)
               (Γ : list VarInfo)
               (remove : bool)
               (t : term) : result term string :=
      match remove, t with
      | true, tProd _ _ body =>
        map_error (fun s => "While specializing type in " ++ string_of_kername name ++ ": " ++ s)
                  (specialize_term specialized (replace :: Γ) body)

      | true, _ => Err ("Expected product in " ++ string_of_kername name ++ ", got" ++ nl ++ PUtil.string_of_term t)
      | false, _ => specialize_term specialized Γ t
      end.

    Definition specialize_decl
               (specialized : list kername)
               (kn : kername)
               (decl : global_decl) : result (list kername * global_decl) string :=
      match decl with
      | ConstantDecl cst =>
        let remove := match cst_type cst with
                      | tProd _ (tInd ind _) _ =>
                        eq_kername (inductive_mind ind) (ChainBase_kername)
                      | _ => false
                      end in

        type <- specialize_type specialized kn [] remove (cst_type cst);;
        body <- match cst_body cst with
                | Some body => body <- specialize_body specialized kn [] remove body;;
                               ret (Some body)
                | None => ret None
                end;;

        ret (if remove then kn :: specialized else specialized,
             ConstantDecl
               {| cst_type := type;
                  cst_body := body;
                  cst_universes := cst_universes cst |})

      | InductiveDecl mib =>
        let params := rev (ind_params mib) in
        let remove := match params with
                      | {| decl_type := tInd ind _ |} :: _ =>
                        eq_kername (inductive_mind ind) ChainBase_kername
                      | _ => false
                      end in
        let go '(params, Γ) cdecl :=
            body <- match decl_body cdecl with
                    | Some body =>
                      body <- map_error (fun s => "While specializing param body of "
                                                    ++ string_of_kername kn ++ ": " ++ s)
                                        (specialize_term specialized Γ body);;
                      ret (Some body)
                    | None => ret None
                    end;;
            type <- map_error (fun s => "While specializing param type of "
                                          ++ string_of_kername kn ++ ": " ++ s)
                              (specialize_term specialized Γ (decl_type cdecl));;
            let cdecl :=
                {| decl_name := decl_name cdecl;
                   decl_body := body;
                   decl_type := type |} in
            ret (params ++ [cdecl], none :: Γ)%list in
        '(params, _) <- monad_fold_left
                          go
                          (if remove then tl params else params)
                          ([], if remove then [replace] else []);;
        let params := rev params in
        let go oib :=
            type <- specialize_type specialized (kn.1, ind_name oib) [] remove (ind_type oib);;
            (* Context with all mutually inductive types added,
             specializing them if we removed an abstraction.
             Ctors themselves will be abstracted over parameters. *)
            let ctorΓ := repeat (if remove then specialize else none)
                                (List.length (ind_bodies mib)) in
            ctors <- monad_map
                       (fun '(name, t, n) =>
                          t <- specialize_type specialized (kn.1, name) ctorΓ remove t;;
                          ret (name, t, n))
                       (ind_ctors oib);;
            (* Projections are just the type of the data value and
             checked in a context with parameters and the record value
             itself *)
            let projΓ := none :: repeat none (List.length params) in
            projs <- monad_map
                       (fun '(name, t) =>
                          t <- map_error (fun s => "While specializing projection "
                                                     ++ name ++ ": " ++ s)
                                         (specialize_term specialized projΓ t);;
                          ret (name, t))
                       (ind_projs oib);;
            ret
              {| ind_name := ind_name oib;
                 ind_type := type;
                 ind_kelim := ind_kelim oib;
                 ind_ctors := ctors;
                 ind_projs := projs; |} in
        bodies <- monad_map go (ind_bodies mib);;
        ret (if remove then kn :: specialized else specialized,
             InductiveDecl
               {| ind_finite := ind_finite mib;
                  ind_npars := List.length params;
                  ind_params := params;
                  ind_bodies := bodies;
                  ind_universes := ind_universes mib;
                  ind_variance := ind_variance mib; |})
      end.
  End ChainBaseSpecialization.

  Definition axiomatized_ChainBase_kername : kername :=
    Eval compute in kername_of_string "ConCert.Extraction.Common.axiomatized_ChainBase".

  Definition axiomatized_ChainBase_decl : global_decl :=
    ConstantDecl
      {| cst_type :=
           tInd
             {| inductive_mind := ChainBase_kername;
                inductive_ind := 0; |}
             [];
         cst_body := None;
         cst_universes := Monomorphic_ctx ContextSet.empty |}.

  (* Specialize ChainBase away in all definitions in an environment.
     Note: this will also add an axiomatized chain base to the environment. *)
  Fixpoint specialize_env_rev (Σ : global_env) : result global_env string :=
    match Σ with
    | [] => ret []
    | (name, decl) :: Σ =>
      if eq_kername name ChainBase_kername then
        let rep_term := tConst axiomatized_ChainBase_kername [] in
        let go '(specialized, newΣ) '(name, decl) :=
            '(specialized, decl) <- specialize_decl rep_term specialized name decl;;
            ret (specialized, (name, decl) :: newΣ) in
        '(_, newΣ_rev) <- monad_fold_left go Σ ([], []);;
        ret ((name, decl)
               :: (axiomatized_ChainBase_kername, axiomatized_ChainBase_decl)
               :: rev newΣ_rev)
      else
        Σ <- specialize_env_rev Σ;;
        ret ((name, decl) :: Σ)
    end.

  (* TODO: There are many reverses here, we should improve this. *)
  Definition specialize_env (Σ : global_env) : result global_env string :=
    Σrev <- specialize_env_rev (List.rev Σ);;
    ret (List.rev Σrev).
End ChainBaseSpecialization.

Axiom assume_env_wellformed : forall Σ, ∥PT.wf Σ∥.
Definition specialize_ChainBase_and_check
           (Σ : T.global_env) :
  result { Σ : P.global_env & ∥PT.wf Σ∥ } string :=
  let Σ := fix_global_env_universes Σ in
  let Σ := T2P.trans_global_decls Σ in
  Σ <- ChainBaseSpecialization.specialize_env Σ;;
  ret (Σ; assume_env_wellformed Σ).
  (*G <- result_of_EnvCheck (check_wf_env_only_univs Σ);;
  ret (Σ; G.π2.p2).*)

(* Specialize, erase and debox the specified template environment.
   Generalization over ChainBase is first specialized away, turning
   things like

   Inductive Foo (cb : ChainBase) := ctor (addr : Address cb).
   Definition a (cb : ChainBase) (n : nat) := n.
   Definition b (cb : ChainBase) (addr : Foo cb) (n : N) :=
     a cb (N.to_nat n).

   into

   Inductive Foo := ctor (addr : Address axiomatized_ChainBase).
   Definition a (n : nat) := n.
   Definition b (addr : Foo) (n : N) :=
     a (N.to_nat n).

   After the environment has been specialized the dependencies of the
   specified seeds are recursively erased and deboxed, except for
   names in the 'ignored' list, whose decls are ignored. The result is
   returned in proper topological order. Assumption: the global
   environment type checks. *)
Definition specialize_erase_debox_template_env
           (Σ : T.global_env)
           (seeds : list kername)
           (ignored : list kername) : result ExAst.global_env string :=
  '(Σ; wfΣ) <- specialize_ChainBase_and_check Σ;;
  map_error string_of_erase_global_decl_error
            (erase_global_decls_deps_recursive ignored Σ wfΣ seeds).

(*
(* Like above, but get the dependencies from the term of a template
   program. *)
Definition specialize_erase_debox_template_program
           (p : T.program)
           (ignored : list kername) : result global_env string :=
  '(Σ; wfΣext) <- specialize_ChainBase_and_check p.1;;
  let deps := PDeps.term_deps [] (T2P.trans p.2) in
  env <- erase_and_debox_graph Σext wfΣext deps axioms;;
  ret env.
*)

(*
Section ExampleTypes.
  Context `{ChainBase}.
  Inductive Ind1 : nat -> Address -> nat -> Type :=
  | ctor1 : forall x, Ind1 0 x 0
  with Ind2 : Type :=
  | ctor2 : forall x, Ind1 0 x 0 -> Ind2.

  Record Rec1 : Type :=
    { rec1_addr : Address;
      rec1_rec2 : nat }
    with Rec2 : Type :=
      { rec2_addr : Address;
        rec2_rec1 : nat }.

  Set Primitive Projections.
  Record Rec3 : Type := { rec3_addr : Address;
                          rec3_addr2 : Address;
                          rec3_eq : rec3_addr = rec3_addr2; }.
End ExampleTypes.

  Quote Recursively Definition example_program := (Rec1, Ind1, Rec3).
  Definition pcuic_example_program := Eval compute in T2P.trans_global_decls example_program.1.
  Definition foo : result P.global_env string :=
    Eval compute in
      ChainBaseSpecialization.specialize_env (P.tConst "ConCert.ExtractionChainBase" [])
                                             (T2P.trans_global_decls example_program.1).
*)

Definition ignored_concert_types :=
  Eval compute in
    map kername_of_string
        ["ConCert.Execution.Blockchain.ActionBody";
        "ConCert.Execution.Blockchain.Address";
        "ConCert.Execution.Blockchain.Amount";
        "ConCert.Execution.Blockchain.ChainBase";
        "ConCert.Execution.Blockchain.Chain";
        "ConCert.Execution.Blockchain.ContractCallContext";
        "ConCert.Execution.Serializable.SerializedValue"].

Import T.
Definition extract_def_name {A : Type} (a : A) : TemplateMonad kername :=
  a <- tmEval cbn a;;
  quoted <- tmQuote a;;
  let (head, args) := TUtil.decompose_app quoted in
  match head with
  | tConst name _ => ret name
  | _ => tmFail ("Expected constant at head, got " ++ TUtil.string_of_term head)
  end.

Record ContractExtractionSet :=
  { env : ExAst.global_env;
    init_name : kername;
    receive_name : kername; }.

(*Definition preprocess_for_extraction '(name, decl) : result (kername * Ex.global_decl) string :=
  match decl with
  | Ex.ConstantDecl body =>
    let (ty_params, ty, body) := body in
    match body with
    | None => ret (name, Ex.ConstantDecl
                           {| Ex.cst_type_parameters := ty_params;
                              Ex.cst_type := ty;
                              Ex.cst_body := None |})
    | Some body =>
      if uses_account_balance body then
        Err ("'" ++ name ++ "' uses account_balance")
      else
        '(type, body) <- ungeneralize_ChainBase ty body;;
        ret (name, Ex.ConstantDecl
                     {| Ex.cst_type_parameters := ty_params;
                        Ex.cst_type := type;
                        Ex.cst_body := Some body |})
    end
  | _ => ret (name, decl)
  end.*)

Definition get_contract_extraction_set
           `{ChainBase}
           {Setup Msg State}
           `{Serializable Setup}
           `{Serializable Msg}
           `{Serializable State}
           (contract : Contract Setup Msg State) : TemplateMonad ContractExtractionSet :=
  init_name <- extract_def_name (Blockchain.init contract);;
  receive_name <- extract_def_name (Blockchain.receive contract);;
  p <- tmQuoteRec contract;;
  let seeds := [init_name; receive_name] in
  match specialize_erase_debox_template_env p.1 seeds ignored_concert_types with
  | Ok Σ => ret {| env := Σ; init_name := init_name; receive_name := receive_name; |}
  | Err err => tmFail err
  end.
