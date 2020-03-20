open All_Forall
open BasicAst
open Datatypes
open EqDecInstances
open List0
open MCOption
open MCString
open PCUICAst
open PCUICAstUtils
open PCUICCumulativity
open PCUICLiftSubst
open PCUICNormal
open PCUICPosition
open PCUICPretty
open PCUICReflect
open PCUICSafeConversion
open PCUICSafeReduce
open PCUICTyping
open PCUICUnivSubst
open PeanoNat
open Specif
open String0
open Universes0
open Config0
open Monad_utils
open UGraph0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val check_dec :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> 'a2 -> bool -> 'a1 **)

let check_dec m m' e = function
| true -> ret m __
| false -> raise m' e

(** val check_eq_true :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> bool -> 'a2 -> 'a1 **)

let check_eq_true m m' b e =
  if b then ret m __ else raise m' e

(** val check_eq_nat :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> nat -> nat -> 'a2 -> 'a1 **)

let check_eq_nat m m' n m0 e =
  let filtered_var = Nat.eq_dec n m0 in
  if filtered_var then ret m __ else raise m' e

type type_error =
| UnboundRel of nat
| UnboundVar of char list
| UnboundEvar of nat
| UndeclaredConstant of char list
| UndeclaredInductive of inductive
| UndeclaredConstructor of inductive * nat
| NotCumulSmaller of universes_graph * context * term * term * term * 
   term * coq_ConversionError
| NotConvertible of universes_graph * context * term * term
| NotASort of term
| NotAProduct of term * term
| NotAnInductive of term
| IllFormedFix of term mfixpoint * nat
| UnsatisfiedConstraints of ConstraintSet.t
| Msg of char list

(** val print_no_prop_level : NoPropLevel.t -> char list **)

let print_no_prop_level x =
  string_of_level (NoPropLevel.to_level x)

(** val print_edge : ((NoPropLevel.t * nat) * NoPropLevel.t) -> char list **)

let print_edge = function
| (y, l2) ->
  let (l1, n) = y in
  append ('('::[])
    (append (print_no_prop_level l1)
      (append (','::(' '::[]))
        (append (string_of_nat n)
          (append (','::(' '::[]))
            (append (print_no_prop_level l2) (')'::[]))))))

(** val print_universes_graph : universes_graph -> char list **)

let print_universes_graph g =
  let levels = Coq_wGraph.VSet.elements (fst (fst g)) in
  let edges = Coq_wGraph.EdgeSet.elements (snd (fst g)) in
  append (string_of_list print_no_prop_level levels)
    (append ('\\'::('n'::[])) (string_of_list print_edge edges))

(** val string_of_conv_pb : conv_pb -> char list **)

let string_of_conv_pb = function
| Conv ->
  'c'::('o'::('n'::('v'::('e'::('r'::('s'::('i'::('o'::('n'::[])))))))))
| Cumul ->
  'c'::('u'::('m'::('u'::('l'::('a'::('t'::('i'::('v'::('i'::('t'::('y'::[])))))))))))

(** val print_term : global_env_ext -> context -> term -> char list **)

let print_term _UU03a3_ _UU0393_ t0 =
  print_term _UU03a3_ _UU0393_ true false t0

(** val string_of_conv_error :
    global_env_ext -> coq_ConversionError -> char list **)

let rec string_of_conv_error _UU03a3_ = function
| NotFoundConstants (c1, c2) ->
  append
    ('B'::('o'::('t'::('h'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::('s'::(' '::[])))))))))))))))
    (append c1
      (append (' '::('a'::('n'::('d'::(' '::[])))))
        (append c2
          (' '::('a'::('r'::('e'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::('.'::[])))))))))))))))))))))))))))))))))))))
| NotFoundConstant c ->
  append ('C'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::(' '::[])))))))))
    (append c
      (' '::('c'::('o'::('m'::('m'::('o'::('n'::(' '::('i'::('n'::(' '::('b'::('o'::('t'::('h'::(' '::('t'::('e'::('r'::('m'::('s'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
| LambdaNotConvertibleTypes (_UU0393_1, na, a1, t1, _UU0393_2, na', a2, t2, e0) ->
  append
    ('W'::('h'::('e'::('n'::(' '::('c'::('o'::('m'::('p'::('a'::('r'::('i'::('n'::('g'::('\\'::('n'::[]))))))))))))))))
    (append (print_term _UU03a3_ _UU0393_1 (Coq_tLambda (na, a1, t1)))
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append (print_term _UU03a3_ _UU0393_2 (Coq_tLambda (na', a2, t2)))
          (append
            ('\\'::('n'::('t'::('y'::('p'::('e'::('s'::(' '::('a'::('r'::('e'::(' '::('n'::('o'::('t'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('b'::('l'::('e'::(':'::('\\'::('n'::[]))))))))))))))))))))))))))))))
            (string_of_conv_error _UU03a3_ e0)))))
| ProdNotConvertibleDomains (_UU0393_1, na, a1, b1, _UU0393_2, na', a2, b2, e0) ->
  append
    ('W'::('h'::('e'::('n'::(' '::('c'::('o'::('m'::('p'::('a'::('r'::('i'::('n'::('g'::('\\'::('n'::[]))))))))))))))))
    (append (print_term _UU03a3_ _UU0393_1 (Coq_tProd (na, a1, b1)))
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append (print_term _UU03a3_ _UU0393_2 (Coq_tProd (na', a2, b2)))
          (append
            ('\\'::('n'::('d'::('o'::('m'::('a'::('i'::('n'::('s'::(' '::('a'::('r'::('e'::(' '::('n'::('o'::('t'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('b'::('l'::('e'::(':'::('\\'::('n'::[]))))))))))))))))))))))))))))))))
            (string_of_conv_error _UU03a3_ e0)))))
| CaseOnDifferentInd (_UU0393_, ind, par, p, c, brs, _UU0393_', ind', par',
                      p', c', brs') ->
  append
    ('T'::('h'::('e'::(' '::('t'::('w'::('o'::(' '::('s'::('t'::('u'::('c'::('k'::(' '::('p'::('a'::('t'::('t'::('e'::('r'::('n'::('-'::('m'::('a'::('t'::('c'::('h'::('i'::('n'::('g'::('\\'::('n'::[]))))))))))))))))))))))))))))))))
    (append
      (print_term _UU03a3_ _UU0393_ (Coq_tCase ((ind, par), p, c, brs)))
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append
          (print_term _UU03a3_ _UU0393_' (Coq_tCase ((ind', par'), p', c',
            brs')))
          ('\\'::('n'::('a'::('r'::('e'::(' '::('d'::('o'::('n'::('e'::(' '::('o'::('n'::(' '::('d'::('i'::('s'::('t'::('i'::('n'::('c'::('t'::(' '::('i'::('n'::('d'::('u'::('c'::('t'::('i'::('v'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))
| CaseBranchNumMismatch (ind, par, _UU0393_, p, c, brs1, m, br, brs2,
                         _UU0393_', p', c', brs1', m', br', brs2') ->
  append
    ('T'::('h'::('e'::(' '::('t'::('w'::('o'::(' '::('s'::('t'::('u'::('c'::('k'::(' '::('p'::('a'::('t'::('t'::('e'::('r'::('n'::('-'::('m'::('a'::('t'::('c'::('h'::('i'::('n'::('g'::('\\'::('n'::[]))))))))))))))))))))))))))))))))
    (append
      (print_term _UU03a3_ _UU0393_ (Coq_tCase ((ind, par), p, c,
        (app brs1 ((m, br) :: brs2)))))
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append
          (print_term _UU03a3_ _UU0393_' (Coq_tCase ((ind, par), p', c',
            (app brs1' ((m', br') :: brs2')))))
          (append
            ('\\'::('n'::('h'::('a'::('v'::('e'::(' '::('a'::(' '::('m'::('i'::('s'::('t'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('b'::('r'::('a'::('n'::('c'::('h'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::[]))))))))))))))))))))))))))))))))))))))))
            (append (string_of_nat (Datatypes.length brs1))
              (append
                ('\\'::('n'::('t'::('h'::('e'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('p'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::('s'::(' '::('d'::('o'::(' '::('n'::('o'::('t'::(' '::('c'::('o'::('i'::('n'::('c'::('i'::('d'::('e'::('\\'::('n'::[]))))))))))))))))))))))))))))))))))))))))))))
                (append (print_term _UU03a3_ _UU0393_ br)
                  (append ('\\'::('n'::('h'::('a'::('s'::(' '::[]))))))
                    (append (string_of_nat m)
                      (append
                        (' '::('p'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::('s'::(' '::('w'::('h'::('i'::('l'::('e'::('\\'::('n'::[])))))))))))))))))))
                        (append (print_term _UU03a3_ _UU0393_ br')
                          (append
                            ('\\'::('n'::('h'::('a'::('s'::(' '::[]))))))
                            (append (string_of_nat m') ('.'::[]))))))))))))))
| DistinctStuckProj (_UU0393_, p, c, _UU0393_', p', c') ->
  append
    ('T'::('h'::('e'::(' '::('t'::('w'::('o'::(' '::('s'::('t'::('u'::('c'::('k'::(' '::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('i'::('o'::('n'::('s'::('\\'::('n'::[])))))))))))))))))))))))))))
    (append (print_term _UU03a3_ _UU0393_ (Coq_tProj (p, c)))
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append (print_term _UU03a3_ _UU0393_' (Coq_tProj (p', c')))
          ('\\'::('n'::('a'::('r'::('e'::(' '::('s'::('y'::('n'::('t'::('a'::('c'::('t'::('i'::('c'::('a'::('l'::('l'::('y'::(' '::('d'::('i'::('f'::('f'::('e'::('r'::('e'::('n'::('t'::('.'::[])))))))))))))))))))))))))))))))))
| CannotUnfoldFix (_UU0393_, mfix, idx, _UU0393_', mfix', idx') ->
  append
    ('T'::('h'::('e'::(' '::('t'::('w'::('o'::(' '::('f'::('i'::('x'::('e'::('d'::('-'::('p'::('o'::('i'::('n'::('t'::('s'::('\\'::('n'::[]))))))))))))))))))))))
    (append (print_term _UU03a3_ _UU0393_ (Coq_tFix (mfix, idx)))
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append (print_term _UU03a3_ _UU0393_' (Coq_tFix (mfix', idx')))
          ('\\'::('n'::('c'::('o'::('r'::('r'::('e'::('s'::('p'::('o'::('n'::('d'::(' '::('t'::('o'::(' '::('s'::('y'::('n'::('t'::('a'::('c'::('t'::('i'::('c'::('a'::('l'::('l'::('y'::(' '::('d'::('i'::('s'::('t'::('i'::('n'::('c'::('t'::(' '::('t'::('e'::('r'::('m'::('s'::(' '::('t'::('h'::('a'::('t'::(' '::('c'::('a'::('n'::('\''::('t'::(' '::('b'::('e'::(' '::('u'::('n'::('f'::('o'::('l'::('d'::('e'::('d'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| FixRargMismatch (idx, _UU0393_, u, mfix1, mfix2, _UU0393_', v, mfix1',
                   mfix2') ->
  append
    ('T'::('h'::('e'::(' '::('t'::('w'::('o'::(' '::('f'::('i'::('x'::('e'::('d'::('-'::('p'::('o'::('i'::('n'::('t'::('s'::('\\'::('n'::[]))))))))))))))))))))))
    (append
      (print_term _UU03a3_ _UU0393_ (Coq_tFix ((app mfix1 (u :: mfix2)),
        idx)))
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append
          (print_term _UU03a3_ _UU0393_' (Coq_tFix
            ((app mfix1' (v :: mfix2')), idx)))
          (append
            ('\\'::('n'::('h'::('a'::('v'::('e'::(' '::('a'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::[])))))))))))))))))))))))))))))))))))))))))
            (append (string_of_nat (Datatypes.length mfix1))
              (append
                (':'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::[]))))))))))))
                (append (string_of_nat u.rarg)
                  (append (' '::('a'::('n'::('d'::(' '::[])))))
                    (append (string_of_nat v.rarg)
                      ('a'::('r'::('e'::(' '::('d'::('i'::('f'::('f'::('e'::('r'::('e'::('n'::('t'::('.'::[])))))))))))))))))))))))
| FixMfixMismatch (idx, _UU0393_, mfix, _UU0393_', mfix') ->
  append
    ('T'::('h'::('e'::(' '::('t'::('w'::('o'::(' '::('f'::('i'::('x'::('e'::('d'::('-'::('p'::('o'::('i'::('n'::('t'::('s'::('\\'::('n'::[]))))))))))))))))))))))
    (append (print_term _UU03a3_ _UU0393_ (Coq_tFix (mfix, idx)))
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append (print_term _UU03a3_ _UU0393_' (Coq_tFix (mfix', idx)))
          ('\\'::('n'::('h'::('a'::('v'::('e'::(' '::('a'::(' '::('d'::('i'::('f'::('f'::('e'::('r'::('e'::('n'::('t'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('m'::('u'::('t'::('u'::('a'::('l'::('l'::('y'::(' '::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::('s'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| DistinctCoFix (_UU0393_, mfix, idx, _UU0393_', mfix', idx') ->
  append
    ('T'::('h'::('e'::(' '::('t'::('w'::('o'::(' '::('c'::('o'::('f'::('i'::('x'::('e'::('d'::('-'::('p'::('o'::('i'::('n'::('t'::('s'::('\\'::('n'::[]))))))))))))))))))))))))
    (append (print_term _UU03a3_ _UU0393_ (Coq_tCoFix (mfix, idx)))
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append (print_term _UU03a3_ _UU0393_' (Coq_tCoFix (mfix', idx')))
          ('\\'::('n'::('c'::('o'::('r'::('r'::('e'::('s'::('p'::('o'::('n'::('d'::(' '::('t'::('o'::(' '::('s'::('y'::('n'::('t'::('a'::('c'::('t'::('i'::('c'::('a'::('l'::('l'::('y'::(' '::('d'::('i'::('s'::('t'::('i'::('n'::('c'::('t'::(' '::('t'::('e'::('r'::('m'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))
| StackHeadError (_, _, _, _, _, _, _, _, _, _, e0) ->
  append
    ('T'::('O'::('D'::('O'::(' '::('s'::('t'::('a'::('c'::('k'::('h'::('e'::('a'::('d'::('e'::('r'::('r'::('o'::('r'::('\\'::('n'::[])))))))))))))))))))))
    (string_of_conv_error _UU03a3_ e0)
| StackTailError (_, _, _, _, _, _, _, _, _, _, e0) ->
  append
    ('T'::('O'::('D'::('O'::(' '::('s'::('t'::('a'::('c'::('k'::('t'::('a'::('i'::('l'::('e'::('r'::('r'::('o'::('r'::('\\'::('n'::[])))))))))))))))))))))
    (string_of_conv_error _UU03a3_ e0)
| StackMismatch (_UU0393_1, t1, _, _, _UU0393_2, t2, _) ->
  append
    ('C'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('e'::('r'::('m'::('s'::('\\'::('n'::[])))))))))))))))))))
    (append (print_term _UU03a3_ _UU0393_1 t1)
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append (print_term _UU03a3_ _UU0393_2 t2)
          (append
            ('a'::('r'::('e'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('b'::('l'::('e'::('/'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('b'::('l'::('e'::(' '::('('::('T'::('O'::('D'::('O'::(')'::(' '::('b'::('u'::('t'::(' '::('a'::('p'::('p'::('l'::('i'::('e'::('d'::(' '::('t'::('o'::(' '::('a'::(' '::('d'::('i'::('f'::('f'::('e'::('r'::('e'::('n'::('t'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            (' '::('o'::('f'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::('.'::[]))))))))))))))))))
| HeadMistmatch (leq, _UU0393_1, t1, _UU0393_2, t2) ->
  append ('T'::('e'::('r'::('m'::('s'::('\\'::('n'::[])))))))
    (append (print_term _UU03a3_ _UU0393_1 t1)
      (append ('\\'::('n'::('a'::('n'::('d'::('\\'::('n'::[])))))))
        (append (print_term _UU03a3_ _UU0393_2 t2)
          (append
            ('\\'::('n'::('d'::('o'::(' '::('n'::('o'::('t'::(' '::('h'::('a'::('v'::('e'::(' '::('t'::('h'::('e'::(' '::('s'::('a'::('m'::('e'::(' '::('h'::('e'::('a'::('d'::(' '::('w'::('h'::('e'::('n'::(' '::('c'::('o'::('m'::('p'::('a'::('r'::('i'::('n'::('g'::(' '::('f'::('o'::('r'::(' '::[])))))))))))))))))))))))))))))))))))))))))))))))
            (string_of_conv_pb leq)))))

(** val string_of_type_error : global_env_ext -> type_error -> char list **)

let string_of_type_error _UU03a3_ = function
| UnboundRel n ->
  append
    ('U'::('n'::('b'::('o'::('u'::('n'::('d'::(' '::('r'::('e'::('l'::(' '::[]))))))))))))
    (string_of_nat n)
| UnboundVar id ->
  append
    ('U'::('n'::('b'::('o'::('u'::('n'::('d'::(' '::('v'::('a'::('r'::(' '::[]))))))))))))
    id
| UnboundEvar ev ->
  append
    ('U'::('n'::('b'::('o'::('u'::('n'::('d'::(' '::('e'::('v'::('a'::('r'::(' '::[])))))))))))))
    (string_of_nat ev)
| UndeclaredConstant c ->
  append
    ('U'::('n'::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::(' '::[]))))))))))))))))))))
    c
| UndeclaredInductive c ->
  append
    ('U'::('n'::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(' '::('i'::('n'::('d'::('u'::('c'::('t'::('i'::('v'::('e'::(' '::[])))))))))))))))))))))
    c.inductive_mind
| UndeclaredConstructor (c, _) ->
  append
    ('U'::('n'::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(' '::('i'::('n'::('d'::('u'::('c'::('t'::('i'::('v'::('e'::(' '::[])))))))))))))))))))))
    c.inductive_mind
| NotCumulSmaller (g, _UU0393_, t0, u, t', u', e0) ->
  append
    ('T'::('e'::('r'::('m'::('s'::(' '::('a'::('r'::('e'::(' '::('n'::('o'::('t'::(' '::('<'::('='::(' '::('f'::('o'::('r'::(' '::('c'::('u'::('m'::('u'::('l'::('a'::('t'::('i'::('v'::('i'::('t'::('y'::(':'::('\\'::('n'::[]))))))))))))))))))))))))))))))))))))
    (append (print_term _UU03a3_ _UU0393_ t0)
      (append ('\\'::('n'::('a'::('n'::('d'::(':'::('\\'::('n'::[]))))))))
        (append (print_term _UU03a3_ _UU0393_ u)
          (append
            ('\\'::('n'::('a'::('f'::('t'::('e'::('r'::(' '::('r'::('e'::('d'::('u'::('c'::('t'::('i'::('o'::('n'::(':'::('\\'::('n'::[]))))))))))))))))))))
            (append (print_term _UU03a3_ _UU0393_ t')
              (append
                ('\\'::('n'::('a'::('n'::('d'::(':'::('\\'::('n'::[]))))))))
                (append (print_term _UU03a3_ _UU0393_ u')
                  (append
                    ('\\'::('n'::('e'::('r'::('r'::('o'::('r'::(':'::('\\'::('n'::[]))))))))))
                    (append (string_of_conv_error _UU03a3_ e0)
                      (append
                        ('\\'::('n'::('i'::('n'::(' '::('u'::('n'::('i'::('v'::('e'::('r'::('s'::('e'::(' '::('g'::('r'::('a'::('p'::('h'::(':'::('\\'::('n'::[]))))))))))))))))))))))
                        (print_universes_graph g)))))))))))
| NotConvertible (g, _UU0393_, t0, u) ->
  append
    ('T'::('e'::('r'::('m'::('s'::(' '::('a'::('r'::('e'::(' '::('n'::('o'::('t'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('b'::('l'::('e'::(':'::('\\'::('n'::[]))))))))))))))))))))))))))))
    (append (print_term _UU03a3_ _UU0393_ t0)
      (append ('\\'::('n'::('a'::('n'::('d'::(':'::('\\'::('n'::[]))))))))
        (append (print_term _UU03a3_ _UU0393_ u)
          (append
            ('\\'::('n'::('i'::('n'::(' '::('u'::('n'::('i'::('v'::('e'::('r'::('s'::('e'::(' '::('g'::('r'::('a'::('p'::('h'::(':'::('\\'::('n'::[]))))))))))))))))))))))
            (print_universes_graph g)))))
| NotASort _ ->
  'N'::('o'::('t'::(' '::('a'::(' '::('s'::('o'::('r'::('t'::[])))))))))
| NotAProduct (_, _) ->
  'N'::('o'::('t'::(' '::('a'::(' '::('p'::('r'::('o'::('d'::('u'::('c'::('t'::[]))))))))))))
| NotAnInductive _ ->
  'N'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('d'::('u'::('c'::('t'::('i'::('v'::('e'::[])))))))))))))))
| IllFormedFix (_, _) ->
  'I'::('l'::('l'::('-'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('d'::('e'::('f'::('i'::('n'::('i'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))
| UnsatisfiedConstraints _ ->
  'U'::('n'::('s'::('a'::('t'::('i'::('s'::('f'::('i'::('e'::('d'::(' '::('c'::('o'::('n'::('s'::('t'::('r'::('a'::('i'::('n'::('t'::('s'::[]))))))))))))))))))))))
| Msg s -> append ('M'::('s'::('g'::(':'::(' '::[]))))) s

type 'a typing_result =
| Checked of 'a
| TypeError of type_error

(** val typing_monad : __ typing_result coq_Monad **)

let typing_monad =
  { ret = (fun _ a -> Checked a); bind = (fun _ _ m f ->
    match m with
    | Checked a -> f a
    | TypeError t0 -> TypeError t0) }

(** val monad_exc : (type_error, __ typing_result) coq_MonadExc **)

let monad_exc =
  { raise = (fun _ e -> TypeError e); catch = (fun _ m f ->
    match m with
    | Checked _ -> m
    | TypeError t0 -> f t0) }

(** val wf_ext_gc_of_uctx :
    checker_flags -> global_env_ext ->
    (Coq_wGraph.VSet.t * GoodConstraintSet.t, __) sigT **)

let wf_ext_gc_of_uctx cf _UU03a3_ =
  let o = gc_of_constraints cf (global_ext_constraints _UU03a3_) in
  (match o with
   | Some t0 ->
     Coq_existT (((no_prop_levels (global_ext_levels _UU03a3_)), t0), __)
   | None -> assert false (* absurd case *))

(** val wf_ext_is_graph :
    checker_flags -> global_env_ext -> (Coq_wGraph.t, __) sigT **)

let wf_ext_is_graph cf _UU03a3_ =
  let s = wf_ext_gc_of_uctx cf _UU03a3_ in
  let Coq_existT (uctx, _) = s in Coq_existT ((make_graph uctx), __)

(** val hnf : checker_flags -> global_env_ext -> context -> term -> term **)

let hnf cf _UU03a3_ _UU0393_ t0 =
  reduce_term cf RedFlags.default _UU03a3_ _UU0393_ t0

(** val reduce_to_sort :
    checker_flags -> global_env_ext -> context -> term -> (Universe.t, __)
    sigT typing_result **)

let reduce_to_sort cf _UU03a3_ _UU0393_ t0 = match t0 with
| Coq_tSort s ->
  let s0 = Obj.magic s in Obj.magic ret typing_monad (Coq_existT (s0, __))
| _ ->
  let filtered_var = hnf cf _UU03a3_ _UU0393_ t0 in
  (match filtered_var with
   | Coq_tSort s -> Obj.magic ret typing_monad (Coq_existT (s, __))
   | _ -> Obj.magic raise monad_exc (NotASort t0))

(** val reduce_to_prod :
    checker_flags -> global_env_ext -> context -> term -> (name, (term,
    (term, __) sigT) sigT) sigT typing_result **)

let reduce_to_prod cf _UU03a3_ _UU0393_ t0 = match t0 with
| Coq_tProd (na, a, b) ->
  let na0 = Obj.magic na in
  let a0 = Obj.magic a in
  let b0 = Obj.magic b in
  Obj.magic ret typing_monad (Coq_existT (na0, (Coq_existT (a0, (Coq_existT
    (b0, __))))))
| _ ->
  let filtered_var = hnf cf _UU03a3_ _UU0393_ t0 in
  (match filtered_var with
   | Coq_tProd (na, a, b) ->
     Obj.magic ret typing_monad (Coq_existT (na, (Coq_existT (a, (Coq_existT
       (b, __))))))
   | x -> Obj.magic raise monad_exc (NotAProduct (t0, x)))

(** val stack_to_apps : stack -> term list typing_result **)

let rec stack_to_apps = function
| Empty -> ret (Obj.magic typing_monad) []
| App (t0, _UU03c0_0) ->
  bind (Obj.magic typing_monad) (stack_to_apps _UU03c0_0) (fun l ->
    ret (Obj.magic typing_monad) (t0 :: l))
| _ ->
  raise (Obj.magic monad_exc) (Msg
    ('n'::('o'::('t'::(' '::('s'::('o'::('m'::('e'::(' '::('a'::('p'::('p'::('l'::('i'::('c'::('a'::('t'::('i'::('o'::('n'::('s'::[]))))))))))))))))))))))

(** val reduce_to_ind :
    checker_flags -> global_env_ext -> context -> term -> (inductive,
    (Instance.t, (term list, __) sigT) sigT) sigT typing_result **)

let reduce_to_ind cf _UU03a3_ _UU0393_ t0 =
  let filtered_var = decompose_app t0 in
  let (t1, l) = filtered_var in
  (match t1 with
   | Coq_tInd (i, u) ->
     let i0 = Obj.magic i in
     let u0 = Obj.magic u in
     let l0 = Obj.magic l in
     Obj.magic ret typing_monad (Coq_existT (i0, (Coq_existT (u0, (Coq_existT
       (l0, __))))))
   | _ ->
     let filtered_var0 =
       reduce_stack cf RedFlags.default _UU03a3_ _UU0393_ t0 Empty
     in
     let (t2, _UU03c0_) = filtered_var0 in
     (match t2 with
      | Coq_tInd (i, u) ->
        let filtered_var1 = stack_to_apps _UU03c0_ in
        (match filtered_var1 with
         | Checked l0 ->
           Obj.magic ret typing_monad (Coq_existT (i, (Coq_existT (u,
             (Coq_existT (l0, __))))))
         | TypeError e -> Obj.magic raise monad_exc e)
      | _ -> Obj.magic raise monad_exc (NotAnInductive t0)))

(** val iscumul :
    checker_flags -> global_env_ext -> universes_graph -> context -> term ->
    term -> coq_ConversionResult **)

let iscumul cf _UU03a3_ g _UU0393_ t1 t2 =
  isconv_term cf RedFlags.default _UU03a3_ g _UU0393_ Cumul t1 t2

(** val convert_leq :
    checker_flags -> global_env_ext -> universes_graph -> context -> term ->
    term -> __ typing_result **)

let convert_leq cf _UU03a3_ g _UU0393_ t0 u =
  let filtered_var = leqb_term cf g t0 u in
  if filtered_var
  then Obj.magic ret typing_monad __
  else let filtered_var0 = iscumul cf _UU03a3_ g _UU0393_ t0 u in
       (match filtered_var0 with
        | Success -> Obj.magic ret typing_monad __
        | Error e ->
          let t' = hnf cf _UU03a3_ _UU0393_ t0 in
          let u' = hnf cf _UU03a3_ _UU0393_ u in
          Obj.magic raise monad_exc (NotCumulSmaller (g, _UU0393_, t0, u, t',
            u', e)))

(** val infer_type :
    checker_flags -> global_env_ext -> (PCUICEnvironment.context -> __ ->
    term -> (term, __) sigT typing_result) -> context -> term -> (Universe.t,
    __) sigT typing_result **)

let infer_type cf _UU03a3_ infer0 _UU0393_ t0 =
  bind (Obj.magic typing_monad) (Obj.magic infer0 _UU0393_ __ t0) (fun tx ->
    bind (Obj.magic typing_monad)
      (reduce_to_sort cf _UU03a3_ _UU0393_ (projT1 tx)) (fun u ->
      ret (Obj.magic typing_monad) (Coq_existT ((projT1 u), __))))

(** val infer_cumul :
    checker_flags -> global_env_ext -> universes_graph ->
    (PCUICEnvironment.context -> __ -> term -> (term, __) sigT typing_result)
    -> context -> term -> term -> __ typing_result **)

let infer_cumul cf _UU03a3_ g infer0 _UU0393_ t0 a =
  bind (Obj.magic typing_monad) (Obj.magic infer0 _UU0393_ __ t0) (fun a' ->
    bind (Obj.magic typing_monad)
      (convert_leq cf _UU03a3_ g _UU0393_ (projT1 a') a) (fun _ ->
      ret (Obj.magic typing_monad) __))

(** val lookup_ind_decl :
    global_env_ext -> inductive -> (PCUICEnvironment.mutual_inductive_body,
    (PCUICEnvironment.one_inductive_body, __) sigT) sigT typing_result **)

let lookup_ind_decl _UU03a3_ ind =
  let filtered_var = lookup_env (fst _UU03a3_) ind.inductive_mind in
  (match filtered_var with
   | Some g ->
     (match g with
      | PCUICEnvironment.ConstantDecl _ ->
        Obj.magic raise monad_exc (UndeclaredInductive ind)
      | PCUICEnvironment.InductiveDecl decl ->
        let decl0 = Obj.magic decl in
        let filtered_var0 = nth_error (ind_bodies decl0) ind.inductive_ind in
        (match filtered_var0 with
         | Some body ->
           Obj.magic ret typing_monad (Coq_existT (decl0, (Coq_existT (body,
             __))))
         | None -> Obj.magic raise monad_exc (UndeclaredInductive ind)))
   | None -> Obj.magic raise monad_exc (UndeclaredInductive ind))

(** val check_consistent_instance :
    checker_flags -> global_env_ext -> universes_graph -> universes_decl ->
    Instance.t -> __ typing_result **)

let check_consistent_instance cf _ g uctx u =
  match uctx with
  | Monomorphic_ctx _ ->
    Obj.magic check_eq_nat typing_monad monad_exc (Datatypes.length u) O (Msg
      ('m'::('o'::('n'::('o'::('m'::('o'::('r'::('p'::('h'::('i'::('c'::(' '::('i'::('n'::('s'::('t'::('a'::('n'::('c'::('e'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('l'::('e'::('n'::('g'::('t'::('h'::(' '::('0'::[])))))))))))))))))))))))))))))))))))))))))))
  | Polymorphic_ctx cst ->
    let (inst, cstrs) = cst in
    let inst0 = Obj.magic inst in
    let cstrs0 = Obj.magic cstrs in
    let filtered_var = AUContext.repr (inst0, cstrs0) in
    let (inst1, cstrs1) = filtered_var in
    Obj.magic bind typing_monad
      (check_eq_true typing_monad monad_exc
        (forallb (fun l ->
          let filtered_var0 = NoPropLevel.of_level l in
          (match filtered_var0 with
           | Some l0 -> Coq_wGraph.VSet.mem l0 (Coq_wGraph.coq_V g)
           | None -> false)) u) (Msg
        ('i'::('n'::('s'::('t'::('a'::('n'::('c'::('e'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('h'::('a'::('v'::('e'::(' '::('t'::('h'::('e'::(' '::('r'::('i'::('g'::('h'::('t'::(' '::('l'::('e'::('n'::('g'::('t'::('h'::[])))))))))))))))))))))))))))))))))))))))))
      (fun _ ->
      bind typing_monad
        (check_eq_nat typing_monad monad_exc (Datatypes.length u)
          (Datatypes.length inst1) (Msg
          ('i'::('n'::('s'::('t'::('a'::('n'::('c'::('e'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('h'::('a'::('v'::('e'::(' '::('t'::('h'::('e'::(' '::('r'::('i'::('g'::('h'::('t'::(' '::('l'::('e'::('n'::('g'::('t'::('h'::[])))))))))))))))))))))))))))))))))))))))))
        (fun _ ->
        let filtered_var0 =
          check_constraints cf g (subst_instance_cstrs u cstrs1)
        in
        if filtered_var0
        then ret typing_monad __
        else raise monad_exc (Msg
               ('c'::('t'::('r'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('a'::('t'::('i'::('s'::('f'::('i'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))

(** val infer :
    checker_flags -> global_env_ext -> universes_graph -> context -> term ->
    (term, __) sigT typing_result **)

let rec infer cf _UU03a3_ g _UU0393_ = function
| Coq_tRel n ->
  let n0 = Obj.magic n in
  let filtered_var = nth_error _UU0393_ n0 in
  (match filtered_var with
   | Some c ->
     Obj.magic ret typing_monad (Coq_existT ((lift (S n0) O (decl_type c)),
       __))
   | None -> Obj.magic raise monad_exc (UnboundRel n0))
| Coq_tVar n ->
  let n0 = Obj.magic n in Obj.magic raise monad_exc (UnboundVar n0)
| Coq_tEvar (ev, _) ->
  let ev0 = Obj.magic ev in Obj.magic raise monad_exc (UnboundEvar ev0)
| Coq_tSort u ->
  let u0 = Obj.magic u in
  let filtered_var = Universe.get_is_level u0 in
  (match filtered_var with
   | Some l ->
     Obj.magic bind typing_monad
       (check_eq_true typing_monad monad_exc
         (LevelSet.mem l (global_ext_levels _UU03a3_)) (Msg
         (append
           ('u'::('n'::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(' '::('l'::('e'::('v'::('e'::('l'::(' '::[])))))))))))))))))
           (string_of_level l)))) (fun _ ->
       ret typing_monad (Coq_existT ((Coq_tSort (Universe.super l)), __)))
   | None ->
     Obj.magic raise monad_exc (Msg
       (append (string_of_sort u0)
         (' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('l'::('e'::('v'::('e'::('l'::[]))))))))))))))))))
| Coq_tProd (na, a, b) ->
  let na0 = Obj.magic na in
  let a0 = Obj.magic a in
  let b0 = Obj.magic b in
  Obj.magic bind typing_monad
    (Obj.magic infer_type cf _UU03a3_ (fun _UU0393_0 _ t1 ->
      infer cf _UU03a3_ g _UU0393_0 t1) _UU0393_ a0) (fun s1 ->
    bind typing_monad
      (Obj.magic infer_type cf _UU03a3_ (fun _UU0393_0 _ t1 ->
        infer cf _UU03a3_ g _UU0393_0 t1) (snoc _UU0393_ (vass na0 a0)) b0)
      (fun s2 ->
      ret typing_monad (Coq_existT ((Coq_tSort
        (Universe.sort_of_product (projT1 s1) (projT1 s2))), __))))
| Coq_tLambda (na, a, t1) ->
  let na0 = Obj.magic na in
  let a0 = Obj.magic a in
  let t2 = Obj.magic t1 in
  Obj.magic bind typing_monad
    (Obj.magic infer_type cf _UU03a3_ (fun _UU0393_0 _ t3 ->
      infer cf _UU03a3_ g _UU0393_0 t3) _UU0393_ a0) (fun _ ->
    bind typing_monad
      (Obj.magic infer cf _UU03a3_ g (Obj.magic snoc _UU0393_ (vass na0 a0))
        t2) (fun b ->
      ret typing_monad (Coq_existT ((Coq_tProd (na0, a0, (projT1 b))), __))))
| Coq_tLetIn (n, b, b_ty, b') ->
  let n0 = Obj.magic n in
  let b0 = Obj.magic b in
  let b_ty0 = Obj.magic b_ty in
  let b'0 = Obj.magic b' in
  Obj.magic bind typing_monad
    (Obj.magic infer_type cf _UU03a3_ (fun _UU0393_0 _ t1 ->
      infer cf _UU03a3_ g _UU0393_0 t1) _UU0393_ b_ty0) (fun _ ->
    bind typing_monad
      (Obj.magic infer_cumul cf _UU03a3_ g (fun _UU0393_0 _ t1 ->
        infer cf _UU03a3_ g _UU0393_0 t1) _UU0393_ b0 b_ty0) (fun _ ->
      bind typing_monad
        (Obj.magic infer cf _UU03a3_ g
          (Obj.magic snoc _UU0393_ (vdef n0 b0 b_ty0)) b'0) (fun b'_ty ->
        ret typing_monad (Coq_existT ((Coq_tLetIn (n0, b0, b_ty0,
          (projT1 b'_ty))), __)))))
| Coq_tApp (t1, u) ->
  let t2 = Obj.magic t1 in
  let u0 = Obj.magic u in
  Obj.magic bind typing_monad (Obj.magic infer cf _UU03a3_ g _UU0393_ t2)
    (fun ty ->
    bind typing_monad
      (Obj.magic reduce_to_prod cf _UU03a3_ _UU0393_ (projT1 ty)) (fun pi ->
      bind typing_monad
        (Obj.magic infer_cumul cf _UU03a3_ g (fun _UU0393_0 _ t3 ->
          infer cf _UU03a3_ g _UU0393_0 t3) _UU0393_ u0 (projT1 (projT2 pi)))
        (fun _ ->
        ret typing_monad (Coq_existT
          ((subst1 u0 O (projT1 (projT2 (projT2 pi)))), __)))))
| Coq_tConst (cst, u) ->
  let cst0 = Obj.magic cst in
  let u0 = Obj.magic u in
  let filtered_var = lookup_env (fst _UU03a3_) cst0 in
  (match filtered_var with
   | Some g0 ->
     (match g0 with
      | PCUICEnvironment.ConstantDecl d ->
        Obj.magic bind typing_monad
          (Obj.magic check_consistent_instance cf _UU03a3_ g
            (cst_universes d) u0) (fun _ ->
          let ty = subst_instance_constr u0 (cst_type d) in
          ret typing_monad (Coq_existT (ty, __)))
      | PCUICEnvironment.InductiveDecl _ ->
        Obj.magic raise monad_exc (UndeclaredConstant cst0))
   | None -> Obj.magic raise monad_exc (UndeclaredConstant cst0))
| Coq_tInd (ind, u) ->
  let ind0 = Obj.magic ind in
  let u0 = Obj.magic u in
  Obj.magic bind typing_monad (Obj.magic lookup_ind_decl _UU03a3_ ind0)
    (fun d ->
    bind typing_monad
      (Obj.magic check_consistent_instance cf _UU03a3_ g
        (ind_universes (projT1 d)) u0) (fun _ ->
      let ty = subst_instance_constr u0 (ind_type (projT1 (projT2 d))) in
      ret typing_monad (Coq_existT (ty, __))))
| Coq_tConstruct (ind, k, u) ->
  let ind0 = Obj.magic ind in
  let k0 = Obj.magic k in
  let u0 = Obj.magic u in
  Obj.magic bind typing_monad (Obj.magic lookup_ind_decl _UU03a3_ ind0)
    (fun d ->
    let filtered_var = nth_error (ind_ctors (projT1 (projT2 d))) k0 in
    (match filtered_var with
     | Some cdecl ->
       bind typing_monad
         (Obj.magic check_consistent_instance cf _UU03a3_ g
           (ind_universes (projT1 d)) u0) (fun _ ->
         ret typing_monad (Coq_existT
           ((type_of_constructor (projT1 d) cdecl (ind0, k0) u0), __)))
     | None -> raise monad_exc (UndeclaredConstructor (ind0, k0))))
| Coq_tCase (indn, p, c, brs) ->
  let (ind, par) = indn in
  let ind0 = Obj.magic ind in
  let par0 = Obj.magic par in
  let p0 = Obj.magic p in
  let c0 = Obj.magic c in
  let brs0 = Obj.magic brs in
  Obj.magic bind typing_monad (Obj.magic infer cf _UU03a3_ g _UU0393_ c0)
    (fun cty ->
    bind typing_monad
      (Obj.magic reduce_to_ind cf _UU03a3_ _UU0393_ (projT1 cty)) (fun i ->
      let Coq_existT (ind', i') = i in
      let Coq_existT (u, i'') = i' in
      let Coq_existT (args, _) = i'' in
      bind typing_monad
        (check_eq_true typing_monad monad_exc
          (reflect_inductive.PCUICReflect.eqb ind0 ind') (NotConvertible (g,
          _UU0393_, (Coq_tInd (ind0, u)), (Coq_tInd (ind', u))))) (fun _ ->
        bind typing_monad (Obj.magic lookup_ind_decl _UU03a3_ ind') (fun d ->
          let Coq_existT (decl, d') = d in
          let Coq_existT (body, _) = d' in
          bind typing_monad
            (check_eq_true typing_monad monad_exc
              (Nat.eqb (ind_npars decl) par0) (Msg
              ('n'::('o'::('t'::(' '::('t'::('h'::('e'::(' '::('r'::('i'::('g'::('h'::('t'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('p'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))))))))))))))))
            (fun _ ->
            bind typing_monad (Obj.magic infer cf _UU03a3_ g _UU0393_ p0)
              (fun pty ->
              let filtered_var = destArity [] (projT1 pty) in
              (match filtered_var with
               | Some p1 ->
                 let (_, ps) = p1 in
                 bind typing_monad
                   (check_eq_true typing_monad monad_exc
                     (leb_sort_family (universe_family ps) (ind_kelim body))
                     (Msg
                     ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('e'::('l'::('i'::('m'::('i'::('n'::('a'::('t'::('e'::(' '::('o'::('v'::('e'::('r'::(' '::('t'::('h'::('i'::('s'::(' '::('s'::('o'::('r'::('t'::[])))))))))))))))))))))))))))))))))
                   (fun _ ->
                   let params = firstn par0 args in
                   let filtered_var0 =
                     build_case_predicate_type ind0 decl body params u ps
                   in
                   (match filtered_var0 with
                    | Some pty' ->
                      let filtered_var1 =
                        iscumul cf _UU03a3_ g _UU0393_ (projT1 pty) pty'
                      in
                      (match filtered_var1 with
                       | Success ->
                         let filtered_var2 =
                           map_option_out
                             (build_branches_type ind0 decl body params u p0)
                         in
                         (match filtered_var2 with
                          | Some btys ->
                            bind typing_monad
                              (let rec check_branches brs1 btys0 =
                                 match brs1 with
                                 | [] ->
                                   (match btys0 with
                                    | [] -> ret typing_monad All2_nil
                                    | _ :: _ ->
                                      raise monad_exc (Msg
                                        ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('b'::('r'::('a'::('n'::('c'::('h'::('e'::('s'::[]))))))))))))))))))))))))))
                                 | wildcard' :: wildcard'0 ->
                                   let (n, t1) = wildcard' in
                                   (match btys0 with
                                    | [] ->
                                      raise monad_exc (Msg
                                        ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('b'::('r'::('a'::('n'::('c'::('h'::('e'::('s'::[])))))))))))))))))))))))))
                                    | p2 :: btys1 ->
                                      let (m, a) = p2 in
                                      bind typing_monad
                                        (check_dec typing_monad monad_exc
                                          (Msg
                                          ('n'::('o'::('t'::(' '::('n'::('a'::('t'::(' '::('e'::('q'::[])))))))))))
                                          (nat_eqdec n m)) (fun _ ->
                                        bind typing_monad
                                          (Obj.magic infer_cumul cf _UU03a3_
                                            g (fun _UU0393_0 _ t2 ->
                                            infer cf _UU03a3_ g _UU0393_0 t2)
                                            _UU0393_ t1 a) (fun _ ->
                                          bind typing_monad
                                            (check_branches wildcard'0 btys1)
                                            (fun x ->
                                            ret typing_monad (All2_cons ((n,
                                              t1), (m, a), wildcard'0, btys1,
                                              __, x))))))
                               in check_branches brs0 btys) (fun _ ->
                              ret typing_monad (Coq_existT
                                ((mkApps p0
                                   (app (skipn par0 args) (c0 :: []))), __)))
                          | None ->
                            raise monad_exc (Msg
                              ('f'::('a'::('i'::('l'::('u'::('r'::('e'::(' '::('i'::('n'::(' '::('b'::('u'::('i'::('l'::('d'::('_'::('b'::('r'::('a'::('n'::('c'::('h'::('e'::('s'::('_'::('t'::('y'::('p'::('e'::[]))))))))))))))))))))))))))))))))
                       | Error e ->
                         raise monad_exc (NotCumulSmaller (g, _UU0393_,
                           (projT1 pty), pty', (projT1 pty), pty', e)))
                    | None ->
                      raise monad_exc (Msg
                        ('f'::('a'::('i'::('l'::('u'::('r'::('e'::(' '::('i'::('n'::(' '::('b'::('u'::('i'::('l'::('d'::('_'::('c'::('a'::('s'::('e'::('_'::('p'::('r'::('e'::('d'::('i'::('c'::('a'::('t'::('e'::('_'::('t'::('y'::('p'::('e'::[])))))))))))))))))))))))))))))))))))))))
               | None ->
                 raise monad_exc (Msg
                   ('t'::('h'::('e'::(' '::('t'::('y'::('p'::('e'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('p'::('r'::('e'::('d'::('i'::('c'::('a'::('t'::('e'::(' '::('o'::('f'::(' '::('a'::(' '::('C'::('a'::('s'::('e'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('a'::('r'::('i'::('t'::('y'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| Coq_tProj (p, c) ->
  let (p0, k) = p in
  let (ind, n) = p0 in
  let ind0 = Obj.magic ind in
  let n0 = Obj.magic n in
  let k0 = Obj.magic k in
  let c0 = Obj.magic c in
  Obj.magic bind typing_monad (Obj.magic lookup_ind_decl _UU03a3_ ind0)
    (fun d ->
    let filtered_var = nth_error (ind_projs (projT1 (projT2 d))) k0 in
    (match filtered_var with
     | Some pdecl ->
       bind typing_monad (Obj.magic infer cf _UU03a3_ g _UU0393_ c0)
         (fun c_ty ->
         bind typing_monad
           (Obj.magic reduce_to_ind cf _UU03a3_ _UU0393_ (projT1 c_ty))
           (fun i ->
           let Coq_existT (ind', i') = i in
           let Coq_existT (u, i'') = i' in
           let Coq_existT (args, _) = i'' in
           bind typing_monad
             (check_eq_true typing_monad monad_exc
               (reflect_inductive.PCUICReflect.eqb ind0 ind') (NotConvertible
               (g, _UU0393_, (Coq_tInd (ind0, u)), (Coq_tInd (ind', u)))))
             (fun _ ->
             bind typing_monad
               (check_eq_true typing_monad monad_exc
                 (Nat.eqb (ind_npars (projT1 d)) n0) (Msg
                 ('n'::('o'::('t'::(' '::('t'::('h'::('e'::(' '::('r'::('i'::('g'::('h'::('t'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('p'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))))))))))))))))
               (fun _ ->
               bind typing_monad
                 (check_eq_true typing_monad monad_exc
                   (Nat.eqb (Datatypes.length args) (ind_npars (projT1 d)))
                   (Msg
                   ('n'::('o'::('t'::(' '::('t'::('h'::('e'::(' '::('r'::('i'::('g'::('h'::('t'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('p'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))))))))))))))))
                 (fun _ ->
                 let ty = snd pdecl in
                 ret typing_monad (Coq_existT
                   ((subst (c0 :: (rev args)) O (subst_instance_constr u ty)),
                   __)))))))
     | None ->
       raise monad_exc (Msg
         ('p'::('r'::('o'::('j'::('e'::('c'::('t'::('i'::('o'::('n'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::[])))))))))))))))))))))))
| Coq_tFix (mfix, n) ->
  let mfix0 = Obj.magic mfix in
  let n0 = Obj.magic n in
  let filtered_var = nth_error mfix0 n0 in
  (match filtered_var with
   | Some decl ->
     Obj.magic bind typing_monad
       (let rec check_types mfix1 acc =
          match mfix1 with
          | [] -> ret typing_monad __
          | def :: mfix2 ->
            bind typing_monad
              (Obj.magic infer_type cf _UU03a3_ (fun _UU0393_0 _ t1 ->
                infer cf _UU03a3_ g _UU0393_0 t1) _UU0393_ def.dtype)
              (fun _ ->
              bind typing_monad
                (check_types mfix2
                  (snoc acc
                    (vass def.dname (lift (Datatypes.length acc) O def.dtype))))
                (fun _ -> ret typing_monad __))
        in check_types mfix0 []) (fun _ ->
       bind typing_monad
         (let rec check_bodies = function
          | [] -> ret typing_monad All_nil
          | def :: mfix'0 ->
            bind typing_monad
              (Obj.magic infer_cumul cf _UU03a3_ g (fun _UU0393_0 _ t1 ->
                infer cf _UU03a3_ g _UU0393_0 t1)
                (app_context _UU0393_ (fix_context mfix0)) def.dbody
                (lift (Datatypes.length (fix_context mfix0)) O def.dtype))
              (fun _ ->
              bind typing_monad
                (check_eq_true typing_monad monad_exc (isLambda def.dbody)
                  (Msg
                  ('n'::('o'::('t'::(' '::('a'::(' '::('l'::('a'::('m'::('b'::('d'::('a'::[]))))))))))))))
                (fun _ ->
                bind typing_monad (check_bodies mfix'0) (fun z ->
                  ret typing_monad (All_cons (def, mfix'0, __, z)))))
          in check_bodies mfix0) (fun _ ->
         bind typing_monad
           (check_eq_true typing_monad monad_exc (fix_guard mfix0) (Msg
             ('U'::('n'::('g'::('u'::('a'::('r'::('d'::('e'::('d'::(' '::('f'::('i'::('x'::('p'::('o'::('i'::('n'::('t'::[]))))))))))))))))))))
           (fun _ -> ret typing_monad (Coq_existT (decl.dtype, __)))))
   | None -> Obj.magic raise monad_exc (IllFormedFix (mfix0, n0)))
| Coq_tCoFix (mfix, n) ->
  let mfix0 = Obj.magic mfix in
  let n0 = Obj.magic n in
  Obj.magic bind typing_monad
    (check_eq_true typing_monad monad_exc cf.allow_cofix (Msg
      ('c'::('o'::('f'::('i'::('x'::(' '::('n'::('o'::('t'::(' '::('a'::('l'::('l'::('o'::('w'::('e'::('d'::[])))))))))))))))))))
    (fun _ ->
    let filtered_var = nth_error mfix0 n0 in
    (match filtered_var with
     | Some decl ->
       bind typing_monad
         (let rec check_types mfix1 acc =
            match mfix1 with
            | [] -> ret typing_monad __
            | def :: mfix2 ->
              bind typing_monad
                (Obj.magic infer_type cf _UU03a3_ (fun _UU0393_0 _ t1 ->
                  infer cf _UU03a3_ g _UU0393_0 t1) _UU0393_ def.dtype)
                (fun _ ->
                bind typing_monad
                  (check_types mfix2
                    (snoc acc
                      (vass def.dname
                        (lift (Datatypes.length acc) O def.dtype))))
                  (fun _ -> ret typing_monad __))
          in check_types mfix0 []) (fun _ ->
         bind typing_monad
           (let rec check_bodies = function
            | [] -> ret typing_monad All_nil
            | def :: mfix'0 ->
              bind typing_monad
                (Obj.magic infer_cumul cf _UU03a3_ g (fun _UU0393_0 _ t1 ->
                  infer cf _UU03a3_ g _UU0393_0 t1)
                  (app_context _UU0393_ (fix_context mfix0)) def.dbody
                  (lift (Datatypes.length (fix_context mfix0)) O def.dtype))
                (fun _ ->
                bind typing_monad (check_bodies mfix'0) (fun z ->
                  ret typing_monad (All_cons (def, mfix'0, __, z))))
            in check_bodies mfix0) (fun _ ->
           ret typing_monad (Coq_existT (decl.dtype, __))))
     | None -> raise monad_exc (IllFormedFix (mfix0, n0))))

(** val check_context :
    checker_flags -> global_env_ext -> universes_graph ->
    PCUICEnvironment.context -> __ typing_result **)

let rec check_context cf _UU03a3_ g = function
| [] -> Obj.magic ret typing_monad __
| c :: _UU0393_0 ->
  let { PCUICEnvironment.decl_name = _; PCUICEnvironment.decl_body =
    decl_body0; PCUICEnvironment.decl_type = a } = c
  in
  (match decl_body0 with
   | Some t0 ->
     let t1 = Obj.magic t0 in
     let a0 = Obj.magic a in
     let _UU0393_1 = Obj.magic _UU0393_0 in
     Obj.magic bind typing_monad
       (Obj.magic check_context cf _UU03a3_ g _UU0393_1) (fun _ ->
       bind typing_monad
         (Obj.magic infer_type cf _UU03a3_ (fun x _ -> infer cf _UU03a3_ g x)
           _UU0393_1 a0) (fun _ ->
         bind typing_monad
           (Obj.magic infer_cumul cf _UU03a3_ g (fun x _ ->
             infer cf _UU03a3_ g x) _UU0393_1 t1 a0) (fun _ ->
           ret typing_monad __)))
   | None ->
     let a0 = Obj.magic a in
     let _UU0393_1 = Obj.magic _UU0393_0 in
     Obj.magic bind typing_monad
       (Obj.magic check_context cf _UU03a3_ g _UU0393_1) (fun _ ->
       bind typing_monad
         (Obj.magic infer_type cf _UU03a3_ (fun x _ -> infer cf _UU03a3_ g x)
           _UU0393_1 a0) (fun _ -> ret typing_monad __)))

(** val check_isType :
    checker_flags -> global_env_ext -> universes_graph ->
    PCUICEnvironment.context -> PCUICTerm.term -> __ typing_result **)

let check_isType cf _UU03a3_ g _UU0393_ a =
  bind (Obj.magic typing_monad) (Obj.magic infer cf _UU03a3_ g _UU0393_ a)
    (fun s ->
    bind (Obj.magic typing_monad)
      (Obj.magic reduce_to_sort cf _UU03a3_ _UU0393_ (projT1 s)) (fun _ ->
      ret (Obj.magic typing_monad) __))

(** val check_isWAT :
    checker_flags -> global_env_ext -> universes_graph ->
    PCUICEnvironment.context -> term -> __ typing_result **)

let rec check_isWAT cf _UU03a3_ g _UU0393_ = function
| Coq_tSort _ -> ret (Obj.magic typing_monad) __
| Coq_tProd (na, a0, b) ->
  bind (Obj.magic typing_monad)
    (Obj.magic infer_type cf _UU03a3_ (fun x _ -> infer cf _UU03a3_ g x)
      _UU0393_ a0) (fun _ ->
    bind (Obj.magic typing_monad)
      (check_isWAT cf _UU03a3_ g (snoc _UU0393_ (vass na a0)) b) (fun _ ->
      ret (Obj.magic typing_monad) __))
| Coq_tLetIn (na, b, b0, t0) ->
  bind (Obj.magic typing_monad)
    (Obj.magic infer_type cf _UU03a3_ (fun x _ -> infer cf _UU03a3_ g x)
      _UU0393_ b0) (fun _ ->
    bind (Obj.magic typing_monad)
      (infer_cumul cf _UU03a3_ g (fun x _ -> infer cf _UU03a3_ g x) _UU0393_
        b b0) (fun _ ->
      bind (Obj.magic typing_monad)
        (check_isWAT cf _UU03a3_ g (snoc _UU0393_ (vdef na b b0)) t0)
        (fun _ -> ret (Obj.magic typing_monad) __)))
| x ->
  bind (Obj.magic typing_monad) (check_isType cf _UU03a3_ g _UU0393_ x)
    (fun _ -> ret (Obj.magic typing_monad) __)

(** val check :
    checker_flags -> global_env_ext -> universes_graph ->
    PCUICEnvironment.context -> term -> term -> __ typing_result **)

let check cf _UU03a3_ g _UU0393_ t0 a =
  bind (Obj.magic typing_monad) (check_isWAT cf _UU03a3_ g _UU0393_ a)
    (fun _ ->
    infer_cumul cf _UU03a3_ g (fun x _ -> infer cf _UU03a3_ g x) _UU0393_ t0 a)

(** val infer' :
    checker_flags -> PCUICEnvironment.global_env_ext -> universes_graph ->
    context -> term -> (term, __) sigT typing_result **)

let infer' =
  infer

(** val make_graph_and_infer :
    checker_flags -> PCUICEnvironment.global_env_ext -> context -> term ->
    (term, __) sigT typing_result **)

let make_graph_and_infer cf _UU03a3_ _UU0393_ t0 =
  let Coq_existT (g, _) = wf_ext_is_graph cf _UU03a3_ in
  infer' cf _UU03a3_ g _UU0393_ t0

type env_error =
| IllFormedDecl of char list * type_error
| AlreadyDeclared of char list

type 'a coq_EnvCheck =
| CorrectDecl of 'a
| EnvError of global_env_ext * env_error

(** val envcheck_monad : __ coq_EnvCheck coq_Monad **)

let envcheck_monad =
  { ret = (fun _ a -> CorrectDecl a); bind = (fun _ _ m f ->
    match m with
    | CorrectDecl a -> f a
    | EnvError (g, e) -> EnvError (g, e)) }

(** val envcheck_monad_exc :
    (global_env_ext * env_error, __ coq_EnvCheck) coq_MonadExc **)

let envcheck_monad_exc =
  { raise = (fun _ pat -> let (g, e) = pat in EnvError (g, e)); catch =
    (fun _ m f ->
    match m with
    | CorrectDecl _ -> m
    | EnvError (g, t0) -> f (g, t0)) }

(** val wrap_error :
    global_env_ext -> char list -> 'a1 typing_result -> 'a1 coq_EnvCheck **)

let wrap_error _UU03a3_ id = function
| Checked a -> CorrectDecl a
| TypeError e -> EnvError (_UU03a3_, (IllFormedDecl (id, e)))

(** val check_wf_type :
    checker_flags -> char list -> global_env_ext -> universes_graph -> term
    -> (Universe.t, __) sigT coq_EnvCheck **)

let check_wf_type cf id _UU03a3_ g t0 =
  wrap_error _UU03a3_ id
    (infer_type cf _UU03a3_ (fun x _ -> infer cf _UU03a3_ g x) [] t0)

(** val check_wf_judgement :
    checker_flags -> char list -> global_env_ext -> universes_graph -> term
    -> term -> __ coq_EnvCheck **)

let check_wf_judgement cf id _UU03a3_ g t0 ty =
  wrap_error _UU03a3_ id (check cf _UU03a3_ g [] t0 ty)

(** val check_fresh :
    char list -> PCUICEnvironment.global_env -> __ coq_EnvCheck **)

let rec check_fresh id = function
| [] -> Obj.magic ret envcheck_monad __
| g :: env0 ->
  let g0 = Obj.magic g in
  let env1 = Obj.magic env0 in
  Obj.magic bind envcheck_monad (Obj.magic check_fresh id env1) (fun _ ->
    let filtered_var = eq_constant id (fst g0) in
    if filtered_var
    then EnvError ((empty_ext env1), (AlreadyDeclared id))
    else ret envcheck_monad __)

(** val coq_VariableLevel_get_noprop :
    NoPropLevel.t -> VariableLevel.t option **)

let coq_VariableLevel_get_noprop = function
| NoPropLevel.Coq_lSet -> None
| NoPropLevel.Level s -> Some (VariableLevel.Level s)
| NoPropLevel.Var n -> Some (VariableLevel.Var n)

(** val add_uctx :
    (Coq_wGraph.VSet.t * GoodConstraintSet.t) -> universes_graph ->
    universes_graph **)

let add_uctx uctx g =
  let levels = Coq_wGraph.VSet.union (fst uctx) (fst (fst g)) in
  let edges =
    Coq_wGraph.VSet.fold (fun l e ->
      match coq_VariableLevel_get_noprop l with
      | Some ll -> Coq_wGraph.EdgeSet.add (edge_of_level ll) e
      | None -> e) (fst uctx) (snd (fst g))
  in
  let edges0 =
    GoodConstraintSet.fold (fun ctr ->
      Coq_wGraph.EdgeSet.add (edge_of_constraint ctr)) (snd uctx) edges
  in
  ((levels, edges0), (snd g))

(** val monad_Alli :
    'a1 coq_Monad -> (nat -> 'a2 -> 'a1) -> 'a2 list -> nat -> 'a1 **)

let rec monad_Alli m f l n =
  match l with
  | [] -> ret m __
  | a :: l0 ->
    bind m (f n a) (fun _ ->
      bind m (monad_Alli m f l0 (S n)) (fun _ -> ret m __))

(** val check_one_ind_body :
    checker_flags -> global_env_ext -> universes_graph -> kername ->
    mutual_inductive_body -> nat -> one_inductive_body -> __ coq_EnvCheck **)

let check_one_ind_body = (fun _ _ _ _ _ _ _ -> ret envcheck_monad __)

(** val check_wf_decl :
    checker_flags -> global_env_ext -> universes_graph -> kername ->
    global_decl -> __ coq_EnvCheck **)

let check_wf_decl cf _UU03a3_ g id = function
| ConstantDecl cst ->
  let cst0 = Obj.magic cst in
  let filtered_var = cst_body cst0 in
  (match filtered_var with
   | Some term0 ->
     Obj.magic bind envcheck_monad
       (Obj.magic check_wf_judgement cf id _UU03a3_ g term0 (cst_type cst0))
       (fun _ -> ret envcheck_monad __)
   | None ->
     Obj.magic bind envcheck_monad
       (Obj.magic check_wf_type cf id _UU03a3_ g (cst_type cst0)) (fun _ ->
       ret envcheck_monad __))
| InductiveDecl mdecl ->
  let mdecl0 = Obj.magic mdecl in
  Obj.magic bind envcheck_monad
    (monad_Alli envcheck_monad
      (Obj.magic check_one_ind_body cf _UU03a3_ g id mdecl0)
      (ind_bodies mdecl0) O) (fun _ ->
    bind envcheck_monad
      (wrap_error _UU03a3_ id
        (Obj.magic check_context cf _UU03a3_ g (ind_params mdecl0)))
      (fun _ ->
      bind envcheck_monad
        (wrap_error _UU03a3_ id
          (check_eq_nat typing_monad monad_exc
            (context_assumptions (ind_params mdecl0)) (ind_npars mdecl0) (Msg
            ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('p'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::('s'::[])))))))))))))))))))))))))))))
        (fun _ ->
        bind envcheck_monad
          (wrap_error _UU03a3_ id
            (check_eq_true typing_monad monad_exc (ind_guard mdecl0) (Msg
              ('g'::('u'::('a'::('r'::('d'::[])))))))) (fun _ ->
          ret envcheck_monad __))))

(** val uctx_of_udecl : universes_decl -> ContextSet.t **)

let uctx_of_udecl u =
  ((levels_of_udecl u), (constraints_of_udecl u))

(** val check_udecl :
    checker_flags -> char list -> global_env -> Coq_wGraph.t ->
    universes_decl -> (Coq_wGraph.VSet.t * GoodConstraintSet.t, __) sigT
    coq_EnvCheck **)

let check_udecl cf id _UU03a3_ g udecl =
  let levels = levels_of_udecl udecl in
  let global_levels0 = global_levels _UU03a3_ in
  let all_levels = LevelSet.union levels global_levels0 in
  bind (Obj.magic envcheck_monad)
    (check_eq_true (Obj.magic envcheck_monad) (Obj.magic envcheck_monad_exc)
      (LevelSet.for_all (fun l -> negb (LevelSet.mem l global_levels0))
        levels) ((empty_ext _UU03a3_), (IllFormedDecl (id, (Msg
      (append
        ('n'::('o'::('n'::(' '::('f'::('r'::('e'::('s'::('h'::(' '::('l'::('e'::('v'::('e'::('l'::(' '::('i'::('n'::(' '::[])))))))))))))))))))
        (print_lset levels))))))) (fun _ ->
    bind (Obj.magic envcheck_monad)
      (check_eq_true (Obj.magic envcheck_monad)
        (Obj.magic envcheck_monad_exc)
        (ConstraintSet.for_all (fun pat ->
          let (p, l2) = pat in
          let (l1, _) = p in
          (&&) (LevelSet.mem l1 all_levels) (LevelSet.mem l2 all_levels))
          (constraints_of_udecl udecl)) ((empty_ext _UU03a3_), (IllFormedDecl
        (id, (Msg
        (append
          ('n'::('o'::('n'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(' '::('l'::('e'::('v'::('e'::('l'::(' '::('i'::('n'::(' '::[]))))))))))))))))))))))
          (append (print_lset levels)
            (append (' '::('|'::('='::(' '::[]))))
              (print_constraint_set (constraints_of_udecl udecl))))))))))
      (fun _ ->
      bind (Obj.magic envcheck_monad)
        (check_eq_true (Obj.magic envcheck_monad)
          (Obj.magic envcheck_monad_exc)
          (match udecl with
           | Monomorphic_ctx ctx ->
             LevelSet.for_all (fun x -> negb (Level.is_var x)) (fst ctx)
           | Polymorphic_ctx _ -> true) ((empty_ext _UU03a3_), (IllFormedDecl
          (id, (Msg
          ('V'::('a'::('r'::(' '::('l'::('e'::('v'::('e'::('l'::(' '::('i'::('n'::(' '::('m'::('o'::('n'::('o'::('m'::('o'::('r'::('p'::('h'::('i'::('c'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))))))))))
        (fun _ ->
        match gc_of_uctx cf (uctx_of_udecl udecl) with
        | Some uctx' ->
          bind (Obj.magic envcheck_monad)
            (check_eq_true (Obj.magic envcheck_monad)
              (Obj.magic envcheck_monad_exc)
              (Coq_wGraph.is_acyclic (add_uctx uctx' g))
              ((empty_ext _UU03a3_), (IllFormedDecl (id, (Msg
              ('c'::('o'::('n'::('s'::('t'::('r'::('a'::('i'::('n'::('t'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('a'::('t'::('i'::('s'::('f'::('i'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))))))))))
            (fun _ -> ret (Obj.magic envcheck_monad) (Coq_existT (uctx', __)))
        | None ->
          raise (Obj.magic envcheck_monad_exc) ((empty_ext _UU03a3_),
            (IllFormedDecl (id, (Msg
            ('c'::('o'::('n'::('s'::('t'::('r'::('a'::('i'::('n'::('t'::('s'::(' '::('t'::('r'::('i'::('v'::('i'::('a'::('l'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('a'::('t'::('i'::('s'::('f'::('i'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))

(** val check_wf_env :
    checker_flags -> global_env -> (Coq_wGraph.t, __) sigT coq_EnvCheck **)

let rec check_wf_env cf = function
| [] -> Obj.magic ret envcheck_monad (Coq_existT (init_graph, __))
| d :: _UU03a3_0 ->
  let d0 = Obj.magic d in
  let _UU03a3_1 = Obj.magic _UU03a3_0 in
  Obj.magic bind envcheck_monad (Obj.magic check_wf_env cf _UU03a3_1)
    (fun g ->
    bind envcheck_monad (Obj.magic check_fresh (fst d0) _UU03a3_1) (fun _ ->
      let udecl = universes_decl_of_decl (snd d0) in
      bind envcheck_monad
        (Obj.magic check_udecl cf (fst d0) _UU03a3_1 (projT1 g) udecl)
        (fun uctx ->
        let g' = add_uctx (projT1 uctx) (projT1 g) in
        bind envcheck_monad
          (Obj.magic check_wf_decl cf (_UU03a3_1, udecl) g' (fst d0) (snd d0))
          (fun _ ->
          match udecl with
          | Monomorphic_ctx _ -> ret envcheck_monad (Coq_existT (g', __))
          | Polymorphic_ctx _ ->
            ret envcheck_monad (Coq_existT ((projT1 g), __))))))
