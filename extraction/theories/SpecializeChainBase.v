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

   Note: Only specializes ChainBase when it is the very first abstraction. *)
(* From Coq Require Import String. *)
From ConCert.Execution Require Import Blockchain.
From ConCert.Extraction Require Import Common.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.Utils Require Import monad_utils.
From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Utils Require Import MCList.
From MetaCoq.Utils Require Import MCProd.
From Coq Require Import List.

Import ListNotations.
Import MCMonadNotation.

Local Open Scope bs_scope.

Definition ChainBase_kername : kername :=
  <%% ChainBase %%>.

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

  Definition result_string A := result A string.

  Definition specialize_type
              (specialize_term : (list VarInfo -> term -> result term string))
              (name : string)
              (Γ : list VarInfo)
              (remove : bool)
              (t : term) : result term string :=
    match remove, t with
    | true, tProd _ _ body =>
      map_error (fun s => "While specializing type in " ++ name ++ ": " ++ s)
                (specialize_term (replace :: Γ) body)

    | true, _ => Err ("Expected product in " ++ name ++ ", got" ++ nl ++ string_of_term t)
    | false, _ => specialize_term Γ t
    end.

  Definition specialize_term
            (specialized : list kername) : list VarInfo -> term -> result_string term :=
    fix f Γ t :=
      match t with
      | tRel n =>
        vi <- result_of_option (nth_error Γ n) ("Unbound tRel(" ++ string_of_nat n ++ ")");;
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
        vi <- result_of_option (nth_error Γ i) "Unbound applied tRel";;
        match vi with
        | replace => Err "Unexpected application"
        | specialize => ret (tRel (i - 1)) (* removed chain base in between, hacky *)
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
          Err ("'"
              ++ string_of_kername name
              ++ "' (or constructor of this) appears unapplied"
              ++ "in term; this needs to be specialized")
        else
          ret t
      | tCase (mk_case_info ind npars relevance) pr disc brs =>
        remove <-
            match pr.(pparams) with
            | tRel n :: _ =>
                vi <- result_of_option (nth_error Γ n) "Unbound tRel in case parameters";;
                match vi with
                | replace => Ok true
                | _ => Ok false
                end
            | _ => Ok false
            end ;;
        pp <- (if (remove : bool)
              then (match pr.(pparams) with
                    | [] => Ok []
                    | _ :: tl0 => monad_map (f Γ) tl0
                    end)
             else monad_map (f Γ) pr.(pparams)) ;;
        let Γ0 := if (remove : bool)
                  then replace :: repeat none (#|pp|)
                  else repeat none #|pp| in
        pctx <- monad_map (fun cd => c <- f (Γ0 ++ Γ)%list cd.(decl_type);;
                                 ret (mkdecl cd.(decl_name) cd.(decl_body) c))
                         pr.(pcontext);;
        ret_ty <- f (repeat none #|pctx| ++ Γ)%list pr.(preturn);;
        let pr' := {| pparams := pp;
                      puinst := pr.(puinst);
                      pcontext := pctx;
                      preturn := ret_ty |} in
        disc <- f Γ disc;;
        brs <- monad_map (fun '(mk_branch ctx t) =>
                           '(s_ctx, _) <- monad_fold_right
                                     (fun '(l0, Γ1) decl =>
                                        let decl_ty := decl.(decl_type) in
                                        let Γty := Γ1 ++ Γ0 in
                                        remove <-
                                          match decl_ty with
                                          | tProd _ (tInd ind _) _ =>
                                              Ok (eq_kername (inductive_mind ind) (ChainBase_kername))
                                          | tProd _ (tRel n) _ => match nth_error Γty n with
                                                     | Some vi => match vi with
                                                                 | replace => Ok true
                                                                 | _ => Ok false
                                                                 end
                                                     | None => Err "Unbound tRel in case parameters"
                                                     end
                                          | _ => Ok false
                                          end;;
                                        ty <- specialize_type f "branch context" Γty remove decl_ty;;
                                        ret (l0 ++ [mkdecl decl.(decl_name) decl.(decl_body) ty], none :: Γ1))%list
                                     ctx ([],Γ);;
                           let s_ctx := rev s_ctx in
                           t <- f (repeat none #|s_ctx| ++ Γ)%list t;; ret (mk_branch s_ctx t)) brs;;
        let npars := if contains (inductive_mind ind) specialized then npars - 1 else npars in
        ret (tCase (mk_case_info ind npars relevance) pr' disc brs)
       | tProj (mkProjection ind npars arg) body =>
        body <- f Γ body;;
        let npars := if contains (inductive_mind ind) specialized then npars - 1 else npars in
        ret (tProj (mkProjection ind npars arg) body)
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
      | tPrim _ => ret t
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

    | true, _ => Err ("Expected lambda in " ++ string_of_kername name ++ ", got" ++ nl ++ string_of_term t)
    | false, _ => specialize_term specialized Γ t
    end.

  Definition specialize_decl
              (Σ : global_env_ext)
              (specialized : list kername)
              (kn : kername)
              (decl : global_decl) : result_string (list kername * global_decl) :=
    match decl with
    | ConstantDecl cst =>
      let remove := match cst_type cst with
                    | tProd _ (tInd ind _) _ =>
                      eq_kername (inductive_mind ind) (ChainBase_kername)
                    | _ => false
                    end in

      type <- map_error
                (fun s => "While specializing decl " ++ string_of_kername kn ++ " type: " ++ s)
                (specialize_type (specialize_term specialized) (string_of_kername kn) [] remove (cst_type cst));;
      body <- match cst_body cst with
              | Some body =>
                body <- map_error
                          (fun s => "While specializing decl " ++
                                    string_of_kername kn ++
                                    " body: " ++ s ++ nl ++
                                    PCUICErrors.print_term Σ [] body)
                          (specialize_body specialized kn [] remove body);;
                ret (Some body)
              | None => ret None
              end;;

      Ok (if remove then kn :: specialized else specialized,
            ConstantDecl
              {| cst_type := type;
                 cst_body := body;
                 cst_universes := cst_universes cst;
                 cst_relevance := cst_relevance cst|})

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
          type <- specialize_type (specialize_term specialized) (string_of_kername (kn.1, ind_name oib)) [] remove (ind_type oib);;
          (* Context with all mutually inductive types added,
            specializing them if we removed an abstraction.
            Ctors themselves will be abstracted over parameters. *)
          let ctorΓ := repeat (if remove then specialize else none)
                              (List.length (ind_bodies mib)) in
          ctors <- monad_map
                       (fun '(Build_constructor_body name args indices ty ar) =>
                          (* TODO: shoule we also specialise args, indices? *)
                        ty <- specialize_type (specialize_term specialized) (string_of_kername (kn.1, name)) ctorΓ remove ty;;
                        ret (Build_constructor_body name args indices ty ar))
                      (ind_ctors oib);;
          (* Projections are just the type of the data value and
            checked in a context with parameters and the record value
            itself *)
          let projΓ := none :: repeat none (List.length params) in
          projs <- monad_map
                      (fun '(Build_projection_body name relevance t) =>
                        t <- map_error (fun s => "While specializing projection "
                                                    ++ name ++ ": " ++ s)
                                        (specialize_term specialized projΓ t);;
                        ret (Build_projection_body name relevance t))
                      (ind_projs oib);;
          ret
            {| ind_name := ind_name oib;
               ind_indices := ind_indices oib;
               ind_sort := ind_sort oib;
               ind_type := type;
               ind_kelim := ind_kelim oib;
               ind_ctors := ctors;
               ind_projs := projs;
               ind_relevance := ind_relevance oib |} in
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

Definition axiomatized_ChainBase := 0.

Definition axiomatized_ChainBase_kername : kername :=
  <%% axiomatized_ChainBase %%>.

Definition axiomatized_ChainBase_decl : global_decl :=
  ConstantDecl
    {| cst_type :=
          tInd
            {| inductive_mind := ChainBase_kername;
              inductive_ind := 0; |}
            [];
        cst_body := None;
        cst_universes := Monomorphic_ctx;
      cst_relevance := Relevant |}.

(* Specialize ChainBase away in all definitions in an environment.
    Note: this will also add an axiomatized chain base to the environment. *)
Fixpoint specialize_env_rev (Σ : global_declarations)
                            (Σprint : global_env_ext)
                            : result_string global_declarations :=
  match Σ with
  | [] => ret []
  | (name, decl) :: Σ =>
    if eq_kername name ChainBase_kername then
      let rep_term := tConst axiomatized_ChainBase_kername [] in
      let go '(specialized, newΣ) '(name, decl) :=
          '(specialized, decl) <- specialize_decl rep_term Σprint specialized name decl;;
          ret (specialized, (name, decl) :: newΣ) in
      '(_, newΣ_rev) <- monad_fold_left go Σ ([], []);;
      ret ((name, decl)
              :: (axiomatized_ChainBase_kername, axiomatized_ChainBase_decl)
              :: rev newΣ_rev)
    else
      Σ <- specialize_env_rev Σ Σprint;;
      ret ((name, decl) :: Σ)
  end.

(* TODO: There are many reverses here, we should improve this. *)
Definition specialize_ChainBase_env (Σ : global_env) : result global_env string :=
  Σrev <- specialize_env_rev (List.rev (declarations Σ)) (empty_ext Σ);;
  ret (mk_global_env (universes Σ) (List.rev Σrev) (retroknowledge Σ)).
