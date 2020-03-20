open Ast0
open BasicAst
open Datatypes
open EAst
open EPretty
open ErasureFunction
open List0
open MCString
open PCUICAst
open PCUICAstUtils
open PCUICSafeChecker
open PCUICTyping
open Pretty
open SafeErasureFunction
open SafeTemplateChecker
open Specif
open String0
open TemplateToPCUIC
open Universes0
open Config0
open Monad_utils
open UGraph0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val erase_template_program_check :
    Ast0.program -> (global_context * EAst.term) coq_EnvCheck **)

let erase_template_program_check p =
  let _UU03a3_ = rev (fst (trans_global (Ast0.empty_ext (fst p)))) in
  bind (Obj.magic envcheck_monad)
    (Obj.magic check_wf_env extraction_checker_flags _UU03a3_) (fun _ ->
    bind (Obj.magic envcheck_monad)
      (wrap_error (empty_ext _UU03a3_)
        ('e'::('r'::('a'::('s'::('u'::('r'::('e'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('g'::('l'::('o'::('b'::('a'::('l'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))
        (Obj.magic ErasureFunction.erase_global _UU03a3_)) (fun _UU03a3_' ->
      bind (Obj.magic envcheck_monad)
        (wrap_error (empty_ext _UU03a3_)
          (append
            ('D'::('u'::('r'::('i'::('n'::('g'::(' '::('e'::('r'::('a'::('s'::('u'::('r'::('e'::(' '::('o'::('f'::(' '::[]))))))))))))))))))
            (string_of_term (trans (snd p))))
          (Obj.magic ErasureFunction.erase (empty_ext _UU03a3_) []
            (trans (snd p)))) (fun t0 ->
        ret (Obj.magic envcheck_monad) (_UU03a3_', t0))))

(** val assume_wf_decl :
    checker_flags -> global_env_ext -> universes_graph -> kername ->
    global_decl -> __ coq_EnvCheck **)

let assume_wf_decl _ _ _ _ _ =
  CorrectDecl __

(** val check_wf_env_only_univs :
    global_env -> (Coq_wGraph.t, __) sigT coq_EnvCheck **)

let rec check_wf_env_only_univs = function
| [] -> Obj.magic ret envcheck_monad (Coq_existT (init_graph, __))
| d :: _UU03a3_0 ->
  let d0 = Obj.magic d in
  let _UU03a3_1 = Obj.magic _UU03a3_0 in
  Obj.magic bind envcheck_monad (Obj.magic check_wf_env_only_univs _UU03a3_1)
    (fun g ->
    bind envcheck_monad (Obj.magic check_fresh (fst d0) _UU03a3_1) (fun _ ->
      let udecl = universes_decl_of_decl (snd d0) in
      bind envcheck_monad
        (Obj.magic check_udecl extraction_checker_flags (fst d0) _UU03a3_1
          (projT1 g) udecl) (fun uctx ->
        let g' = add_uctx (projT1 uctx) (projT1 g) in
        bind envcheck_monad
          (Obj.magic assume_wf_decl extraction_checker_flags (_UU03a3_1,
            udecl) g' (fst d0) (snd d0)) (fun _ ->
          match udecl with
          | Monomorphic_ctx _ -> ret envcheck_monad (Coq_existT (g', __))
          | Polymorphic_ctx _ ->
            ret envcheck_monad (Coq_existT ((projT1 g), __))))))

(** val erase_template_program :
    Ast0.program -> (global_context * EAst.term) coq_EnvCheck **)

let erase_template_program p =
  let _UU03a3_ = rev (fst (trans_global (Ast0.empty_ext (fst p)))) in
  bind (Obj.magic envcheck_monad)
    (Obj.magic check_wf_env_only_univs _UU03a3_) (fun _ ->
    bind (Obj.magic envcheck_monad)
      (wrap_error (empty_ext _UU03a3_)
        ('e'::('r'::('a'::('s'::('u'::('r'::('e'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('g'::('l'::('o'::('b'::('a'::('l'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))
        (Obj.magic erase_global _UU03a3_)) (fun _UU03a3_' ->
      bind (Obj.magic envcheck_monad)
        (wrap_error (empty_ext _UU03a3_)
          (append
            ('D'::('u'::('r'::('i'::('n'::('g'::(' '::('e'::('r'::('a'::('s'::('u'::('r'::('e'::(' '::('o'::('f'::(' '::[]))))))))))))))))))
            (string_of_term (trans (snd p))))
          (Obj.magic erase (empty_ext _UU03a3_) [] (trans (snd p))))
        (fun t0 -> ret (Obj.magic envcheck_monad) (_UU03a3_', t0))))

(** val erase_and_print_template_program_check :
    checker_flags -> Ast0.program -> (char list, char list) sum **)

let erase_and_print_template_program_check _ p =
  let p0 = fix_program_universes p in
  (match erase_template_program_check p0 with
   | CorrectDecl a ->
     let (_UU03a3_', t0) = a in
     Coq_inl
     (append
       ('E'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(' '::('i'::('s'::(' '::('w'::('e'::('l'::('l'::('-'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('a'::('n'::('d'::(' '::[])))))))))))))))))))))))))))))))
       (append (print_term (Ast0.empty_ext (fst p0)) [] true (snd p0))
         (append
           (' '::('e'::('r'::('a'::('s'::('e'::('s'::(' '::('t'::('o'::(':'::(' '::[]))))))))))))
           (append nl (EPretty.print_term _UU03a3_' [] true false t0)))))
   | EnvError (_UU03a3_', e0) ->
     (match e0 with
      | IllFormedDecl (id, e) ->
        Coq_inr
          (append
            ('T'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::[]))))))))))))
            (append (string_of_type_error _UU03a3_' e)
              (append
                (','::(' '::('w'::('h'::('i'::('l'::('e'::(' '::('c'::('h'::('e'::('c'::('k'::('i'::('n'::('g'::(' '::[])))))))))))))))))
                id)))
      | AlreadyDeclared id ->
        Coq_inr
          (append
            ('A'::('l'::('r'::('e'::('a'::('d'::('y'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(':'::(' '::[]))))))))))))))))))
            id)))

(** val erase_and_print_template_program :
    checker_flags -> Ast0.program -> (char list, char list) sum **)

let erase_and_print_template_program _ p =
  let p0 = fix_program_universes p in
  (match erase_template_program p0 with
   | CorrectDecl a ->
     let (_UU03a3_', t0) = a in
     Coq_inl
     (append
       ('E'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(' '::('i'::('s'::(' '::('w'::('e'::('l'::('l'::('-'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('a'::('n'::('d'::(' '::[])))))))))))))))))))))))))))))))
       (append (print_term (Ast0.empty_ext (fst p0)) [] true (snd p0))
         (append
           (' '::('e'::('r'::('a'::('s'::('e'::('s'::(' '::('t'::('o'::(':'::(' '::[]))))))))))))
           (append nl (EPretty.print_term _UU03a3_' [] true false t0)))))
   | EnvError (_UU03a3_', e0) ->
     (match e0 with
      | IllFormedDecl (id, e) ->
        Coq_inr
          (append
            ('T'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::[]))))))))))))
            (append (string_of_type_error _UU03a3_' e)
              (append
                (','::(' '::('w'::('h'::('i'::('l'::('e'::(' '::('c'::('h'::('e'::('c'::('k'::('i'::('n'::('g'::(' '::[])))))))))))))))))
                id)))
      | AlreadyDeclared id ->
        Coq_inr
          (append
            ('A'::('l'::('r'::('e'::('a'::('d'::('y'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(':'::(' '::[]))))))))))))))))))
            id)))
