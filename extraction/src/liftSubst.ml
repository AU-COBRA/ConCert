open Ast0
open BasicAst
open Datatypes
open List0
open MCProd
open Nat0

(** val lift : nat -> nat -> term -> term **)

let rec lift n k t = match t with
| Coq_tRel i -> if leb k i then Coq_tRel (add n i) else Coq_tRel i
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (lift n k) args))
| Coq_tCast (c, kind, t0) -> Coq_tCast ((lift n k c), kind, (lift n k t0))
| Coq_tProd (na, a, b) -> Coq_tProd (na, (lift n k a), (lift n (S k) b))
| Coq_tLambda (na, t0, m) -> Coq_tLambda (na, (lift n k t0), (lift n (S k) m))
| Coq_tLetIn (na, b, t0, b') ->
  Coq_tLetIn (na, (lift n k b), (lift n k t0), (lift n (S k) b'))
| Coq_tApp (u, v) -> Coq_tApp ((lift n k u), (map (lift n k) v))
| Coq_tCase (ind, p, c, brs) ->
  let brs' = map (on_snd (lift n k)) brs in
  Coq_tCase (ind, (lift n k p), (lift n k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (lift n k c))
| Coq_tFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (lift n k) (lift n k')) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (lift n k) (lift n k')) mfix in
  Coq_tCoFix (mfix', idx)
| _ -> t
