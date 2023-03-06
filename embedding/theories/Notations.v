From Coq Require Import String.
From Coq Require Import List.
From ConCert.Embedding Require Import Ast.

(** * Notations for the deep embedding *)

(** Here we use "custom entries" - a new feature of
    Coq allowing to define autonomous grammars *)

Import ListNotations.

Open Scope list.

Declare Custom Entry ctor.

Declare Custom Entry global_dec.
Declare Custom Entry expr.
Declare Custom Entry pat.
Declare Custom Entry type.
Declare Custom Entry name_type.


Notation "[! ty !]" := ty (ty custom type at level 2).
Notation "ty" := (tyInd ty) (in custom type at level 0, ty constr at level 2).

Notation "ty1 ty2" := (tyApp ty1 ty2)
                        (in custom type at level 3, left associativity,
                            ty1 custom type,
                            ty2 custom type).


Notation "ty1 -> ty2" := (tyArr ty1 ty2)
                          (in custom type at level 4, right associativity,
                              ty1 custom type,
                              ty2 custom type at level 4).

Notation "'∀' x , ty" := (tyForall x ty)
                         (in custom type at level 4, right associativity,
                             x constr at level 2,
                             ty custom type at level 4).


Notation " ' x " := (tyVar x)
                    (in custom type at level 1,
                        x constr at level 2).

Notation " ^ x " := (tyRel x)
                    (in custom type at level 1,
                        x constr at level 2).

Notation "( x )" := x (in custom type, x at level 2).
Notation "{ x }" := x (in custom type, x constr).

Definition example_arr := [! "A" -> "B" -> ^0 !].

Fixpoint ctor_type_to_list_anon (ty : type) : list (option ename * type) :=
  match ty with
  | tyInd i => [(None,tyInd i)]
  | tyArr ty1 ty2 => ctor_type_to_list_anon ty1 ++ ctor_type_to_list_anon ty2
  | _ => [(None ,ty)] (* TODO : figure out what to do here *)
  end.

Definition unnamed_constr (c : string * list type) : constr :=
  let '(cn, tys) := c in (cn, map (fun ty => (None,ty)) tys).

Declare Custom Entry ctor_args.

(** Some workarounds required for declaring recursive notations (see comments below) *)

Notation "ty" := (ty) (in custom ctor_args at level 1, ty custom type at level 2).

Notation "ty1 , tys" :=
  (ty1 :: tys)
    (in custom ctor_args at level 2, right associativity,
        ty1 custom type,
        tys custom ctor_args at level 4).

Notation "'_'" := (nil) (in custom ctor_args at level 2).

Notation " ctr [ tys ]" :=
  (ctr, tys)
    (in custom ctor at level 1,
        ctr constr at level 2,
        tys custom ctor_args at level 2).


(** Unfortunately there are some problems with recursive notations
    (might go away after the next stable release - 8.10.).
    So, there are several variants of [data], [record], [case] for different
    number of cases below. The first argument in the recursive pattern is
    parsed correctly, but the second and the next ones are not considered
    as declared [custom], so no custom rules apply. *)

(* Notation "'data' ty_nm ':=' c1 | .. | cn ;;" := *)
(*   (gdInd ty_nm (cons c1 .. (cons cn nil) ..)) *)
(*     (in custom global_dec at level 1, *)
(*         ty_nm constr at level 4, *)
(*         c1 custom ctor at level 4, *)
(*         cn custom ctor at level 4). *)


Notation "[\ gd \]" := gd (gd custom global_dec at level 2).

Declare Custom Entry data_name.

Notation "dn" := (dn,0) (in custom data_name at level 2, dn constr at level 4).
Notation "dn # n" := (dn,n) (in custom data_name at level 2,
                                n constr at level 4,
                                dn constr at level 4).

Notation "'data' ty_nm '=' c1" :=
  (let (nm, nparams) := ty_nm in
   gdInd nm nparams [unnamed_constr c1] false)
    (in custom global_dec at level 1,
        ty_nm custom data_name at level 2,
        c1 custom ctor at level 2).


Notation "'data' ty_nm '=' c1 | c2" :=
  (let (nm, nparams) := ty_nm in
   gdInd nm nparams (map unnamed_constr (c1 :: c2 :: nil)) false)
    (in custom global_dec at level 1,
        ty_nm custom data_name at level 2,
        c1 custom ctor at level 2,
        c2 custom ctor at level 2).

Notation "'data' ty_nm '=' c1 | c2 | c3" :=
  (let (nm, nparams) := ty_nm in
   gdInd nm nparams (map unnamed_constr [c1; c2; c3]) false)
    (in custom global_dec at level 1,
        ty_nm custom data_name at level 2,
        c1 custom ctor at level 2,
        c2 custom ctor at level 2,
        c3 custom ctor at level 2).

Notation "'data' ty_nm '=' c1 | c2 | c3 | c4" :=
  (let (nm, nparams) := ty_nm in
   gdInd nm nparams (map unnamed_constr [c1; c2; c3; c4]) false)
    (in custom global_dec at level 1,
        ty_nm custom data_name at level 2,
        c1 custom ctor at level 2,
        c2 custom ctor at level 2,
        c3 custom ctor at level 2,
        c4 custom ctor at level 2).

Notation "'data' ty_nm '=' c1 | c2 | c3 | c4 | c5" :=
  (let (nm, nparams) := ty_nm in
   gdInd nm 0 (map unnamed_constr [c1; c2; c3; c4; c5]) false)
    (in custom global_dec at level 1,
        ty_nm custom data_name at level 2,
        c1 custom ctor at level 2,
        c2 custom ctor at level 2,
        c3 custom ctor at level 2,
        c4 custom ctor at level 2,
        c5 custom ctor at level 2).


Definition rec_constr (rec_ctor : ename) (proj_tys : list (option ename * type))
  : string * list (option ename * type) :=
  (rec_ctor, proj_tys).

Definition rec_constrs rec_nm := map (rec_constr rec_nm).

Notation "'record' rec_nm := rec_ctor { pr1 : ty1 }" :=
  (gdInd rec_nm 0 [ rec_constr rec_ctor [(Some pr1,ty1)]] true)
    (in custom global_dec at level 1,
        pr1 constr at level 4,
        rec_ctor constr at level 4,
        rec_nm constr at level 4,
        ty1 custom type at level 4).

Notation "'record' rec_nm := rec_ctor { pr1 : ty1 ; pr2 : ty2 }" :=
  (gdInd rec_nm 0 [ rec_constr rec_ctor [(Some pr1,ty1); (Some pr2,ty2)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4).

Notation "'record' rec_nm := rec_ctor { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_ctor [(Some pr1,ty1); (Some pr2,ty2); (Some pr3,ty3)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4).

Notation "'record' rec_nm # n := rec_ctor { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 ; pr4 : ty4 }" :=
  (gdInd rec_nm n
         [ rec_constr rec_ctor [(Some pr1,ty1); (Some pr2,ty2);
                                (Some pr3,ty3); (Some pr4,ty4)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        n constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        pr4 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4,
        ty4 custom type at level 4).


Notation "'record' rec_nm := rec_ctor { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 ; pr4 : ty4 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_ctor [(Some pr1,ty1); (Some pr2,ty2);
                                (Some pr3,ty3); (Some pr4,ty4)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        pr4 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4,
        ty4 custom type at level 4).

Notation "'record' rec_nm := rec_ctor { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 ; pr4 : ty4 ; pr5 : ty5 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_ctor [(Some pr1,ty1); (Some pr2,ty2);
                                (Some pr3,ty3); (Some pr4,ty4);
                                  (Some pr5,ty5)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        pr4 constr at level 4,
        pr5 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4,
        ty4 custom type at level 4,
        ty5 custom type at level 4).

Notation "'record' rec_nm := rec_ctor { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 ; pr4 : ty4 ; pr5 : ty5 ; pr6 : ty6 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_ctor [(Some pr1,ty1); (Some pr2,ty2);
                                (Some pr3,ty3); (Some pr4,ty4);
                                  (Some pr5,ty5); (Some pr6,ty6)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        pr4 constr at level 4,
        pr5 constr at level 4,
        pr6 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4,
        ty4 custom type at level 4,
        ty5 custom type at level 4,
        ty6 custom type at level 4).


Notation "[| e |]" := e (e custom expr at level 2).
Notation "^ i " := (eRel i) (in custom expr at level 3, i constr at level 4).

Notation "\ x : ty => b" := (eLambda x ty b)
                              (in custom expr at level 1,
                                  ty custom type at level 2,
                                  b custom expr at level 4,
                                  x constr at level 4).

Notation "\\ A => b" := (eTyLam A b)
                         (in custom expr at level 1,
                             b custom expr at level 4,
                             A constr at level 4).

Notation "'let' x : ty := e1 'in' e2" := (eLetIn x e1 ty e2)
                                           (in custom expr at level 1,
                                               ty custom type at level 2,
                                               e1 custom expr at level 4,
                                               e2 custom expr at level 4,
                                               x constr at level 4).

Notation "$ Ctor $ ty" := (eConstr ty Ctor) (in custom expr at level 2,
                                              Ctor constr at level 4,
                                              ty constr at level 4).

Notation "C x .. y " := (pConstr C (cons x .. (cons y nil) .. ))
                           (in custom pat at level 0,
                               C constr at level 4,
                               x constr at level 4,
                               y constr at level 4).

Notation "C" := (pConstr C [])
                  (in custom pat at level 0,
                      C constr at level 4).

(* Notation "'case' x : ty 'of' b1 | .. | bn " := *)
(*   (eCase (ty,0) (tyInd "") x (cons b1 .. (cons bn nil) ..)) *)
(*     (in custom expr at level 1, *)
(*         b1 custom expr at level 4, *)
(*         bn custom expr at level 4, *)
(*         ty constr at level 4). *)

Definition to_ind (inds : list ename) := map tyInd inds.

Inductive case_info :=
| ciParamInd : ename -> list type -> case_info.

Declare Custom Entry case_info.

Notation "ind" := (ciParamInd ind []) (in custom case_info at level 1, ind constr at level 4).

Notation "ind ty" := (ciParamInd ind [ty]) (in custom case_info at level 1,
                                               ind constr at level 4,
                                               ty custom type at level 4).

Notation "ind ty1 , ty2" := (ciParamInd ind [ty1; ty2]) (in custom case_info at level 1,
                                                         ind constr at level 4,
                                                         ty1 custom type at level 4,
                                                         ty2 custom type at level 4).


Definition ci_to_types (ci : case_info ) :=
  match ci with
  | ciParamInd ind tys => (ind, tys)
  end.

Notation "'case' x : ci 'return' ty2 'of' | p1 -> b1 | p2 -> b2 | p3 -> b3" :=
  (eCase (ci_to_types ci) ty2 x [(p1,b1); (p2,b2); (p3,b3)])
    (in custom expr at level 2,
        p1 custom pat at level 4,
        p2 custom pat at level 4,
        p3 custom pat at level 4,
        b1 custom expr at level 4,
        b2 custom expr at level 4,
        b3 custom expr at level 4,
        ci custom case_info at level 4,
        ty2 custom type at level 4).


Notation "'case' x : ci 'return' ty2 'of' | p1 -> b1 | pn -> bn" :=
  (eCase (ci_to_types ci) ty2 x [(p1,b1); (pn,bn)])
    (in custom expr at level 2,
        p1 custom pat at level 4,
        pn custom pat at level 4,
        b1 custom expr at level 4,
        bn custom expr at level 4,
        ci custom case_info at level 4,
        ty2 custom type at level 4).

Notation "'case' x : ci 'return' ty2 'of' p1 -> b1 " :=
  (eCase (ci_to_types ci) ty2 x [(p1,b1)])
    (in custom expr at level 2,
        p1 custom pat at level 4,
        b1 custom expr at level 4,
        ci custom case_info at level 4,
        ty2 custom type at level 4).

Notation "x" := (eVar x) (in custom expr at level 0, x constr at level 4).

Notation "t1 t2" := (eApp t1 t2) (in custom expr at level 4, left associativity).

Notation "'fix' fixname ( v : ty1 ) : ty2 := b" := (eFix fixname v ty1 ty2 b)
                                  (in custom expr at level 2,
                                      fixname constr at level 4,
                                      v constr at level 4,
                                      b custom expr at level 4,
                                      ty1 custom type at level 4,
                                      ty2 custom type at level 4).

Notation "[: ty ]" := (eTy ty) (in custom expr at level 1,
                                    ty custom type).

Notation "( x )" := x (in custom expr, x at level 2).
Notation "{ x }" := x (in custom expr, x constr).
