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

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Transform.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.

Import MonadNotation.
Local Open Scope string.

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
      | tCase (ind, npars) ret_ty disc brs =>
        ret_ty <- f Γ ret_ty;;
        disc <- f Γ disc;;
        brs <- monad_map (fun '(ar, t) => t <- f Γ t;; ret (ar, t)) brs;;
        let npars := if contains (inductive_mind ind) specialized then npars - 1 else npars in
        ret (tCase (ind, npars) ret_ty disc brs)
      | tProj ((ind, npars), arg) body =>
        body <- f Γ body;;
        let npars := if contains (inductive_mind ind) specialized then npars - 1 else npars in
        ret (tProj ((ind, npars), arg) body)
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

    | true, _ => Err ("Expected product in " ++ string_of_kername name ++ ", got" ++ nl ++ string_of_term t)
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
Definition specialize_ChainBase_env (Σ : global_env) : result global_env string :=
  Σrev <- specialize_env_rev (List.rev Σ);;
  ret (List.rev Σrev).
