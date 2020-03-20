open All_Forall
open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICReflect
open Universes0

(** val eqb_term_upto_univ :
    (Universe.t -> Universe.t -> bool) -> (Universe.t -> Universe.t -> bool)
    -> term -> term -> bool **)

let rec eqb_term_upto_univ equ lequ u v =
  match u with
  | Coq_tRel n ->
    (match v with
     | Coq_tRel m -> reflect_nat.eqb n m
     | _ -> false)
  | Coq_tVar id ->
    (match v with
     | Coq_tVar id' -> reflect_string.eqb id id'
     | _ -> false)
  | Coq_tEvar (e, args) ->
    (match v with
     | Coq_tEvar (e', args') ->
       (&&) (reflect_nat.eqb e e')
         (forallb2 (eqb_term_upto_univ equ equ) args args')
     | _ -> false)
  | Coq_tSort u0 -> (match v with
                     | Coq_tSort u' -> lequ u0 u'
                     | _ -> false)
  | Coq_tProd (_, a, b) ->
    (match v with
     | Coq_tProd (_, a', b') ->
       (&&) (eqb_term_upto_univ equ equ a a')
         (eqb_term_upto_univ equ lequ b b')
     | _ -> false)
  | Coq_tLambda (_, a, t0) ->
    (match v with
     | Coq_tLambda (_, a', t') ->
       (&&) (eqb_term_upto_univ equ equ a a')
         (eqb_term_upto_univ equ lequ t0 t')
     | _ -> false)
  | Coq_tLetIn (_, b, b0, u0) ->
    (match v with
     | Coq_tLetIn (_, b', b'0, u') ->
       (&&)
         ((&&) (eqb_term_upto_univ equ equ b b')
           (eqb_term_upto_univ equ equ b0 b'0))
         (eqb_term_upto_univ equ lequ u0 u')
     | _ -> false)
  | Coq_tApp (u0, v0) ->
    (match v with
     | Coq_tApp (u', v') ->
       (&&) (eqb_term_upto_univ equ lequ u0 u')
         (eqb_term_upto_univ equ equ v0 v')
     | _ -> false)
  | Coq_tConst (c, u0) ->
    (match v with
     | Coq_tConst (c', u') ->
       (&&) (reflect_string.eqb c c')
         (forallb2 equ (map Universe.make u0) (map Universe.make u'))
     | _ -> false)
  | Coq_tInd (i, u0) ->
    (match v with
     | Coq_tInd (i', u') ->
       (&&) (reflect_inductive.eqb i i')
         (forallb2 equ (map Universe.make u0) (map Universe.make u'))
     | _ -> false)
  | Coq_tConstruct (i, k, u0) ->
    (match v with
     | Coq_tConstruct (i', k', u') ->
       (&&) ((&&) (reflect_inductive.eqb i i') (reflect_nat.eqb k k'))
         (forallb2 equ (map Universe.make u0) (map Universe.make u'))
     | _ -> false)
  | Coq_tCase (indp, p, c, brs) ->
    (match v with
     | Coq_tCase (indp', p', c', brs') ->
       (&&)
         ((&&)
           ((&&)
             ((reflect_prod reflect_inductive reflect_nat).eqb indp indp')
             (eqb_term_upto_univ equ equ p p'))
           (eqb_term_upto_univ equ equ c c'))
         (forallb2 (fun x y ->
           (&&) (reflect_nat.eqb (fst x) (fst y))
             (eqb_term_upto_univ equ equ (snd x) (snd y))) brs brs')
     | _ -> false)
  | Coq_tProj (p, c) ->
    (match v with
     | Coq_tProj (p', c') ->
       (&&)
         ((reflect_prod (reflect_prod reflect_inductive reflect_nat)
            reflect_nat).eqb p p') (eqb_term_upto_univ equ equ c c')
     | _ -> false)
  | Coq_tFix (mfix, idx) ->
    (match v with
     | Coq_tFix (mfix', idx') ->
       (&&) (reflect_nat.eqb idx idx')
         (forallb2 (fun x y ->
           (&&)
             ((&&) (eqb_term_upto_univ equ equ x.dtype y.dtype)
               (eqb_term_upto_univ equ equ x.dbody y.dbody))
             (reflect_nat.eqb x.rarg y.rarg)) mfix mfix')
     | _ -> false)
  | Coq_tCoFix (mfix, idx) ->
    (match v with
     | Coq_tCoFix (mfix', idx') ->
       (&&) (reflect_nat.eqb idx idx')
         (forallb2 (fun x y ->
           (&&)
             ((&&) (eqb_term_upto_univ equ equ x.dtype y.dtype)
               (eqb_term_upto_univ equ equ x.dbody y.dbody))
             (reflect_nat.eqb x.rarg y.rarg)) mfix mfix')
     | _ -> false)
