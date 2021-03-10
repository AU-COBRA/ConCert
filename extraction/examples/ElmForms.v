From ConCert.Embedding Require Import CustomTactics.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import MidlangExtract.
From ConCert.Extraction Require Import ElmExtractTests.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import Inlining.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Utils Require Import StringExtra.
From ConCert.Utils Require Import RecordUpdate.

From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Arith.
From Coq Require Import Lia.
From Coq Require Import ssreflect ssrbool.

From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq Require Import monad_utils.
From MetaCoq Require Import utils.

Open Scope string.

Inductive Cmd (A : Type) : Set :=
  none.

Arguments none {_}.

Record Entry :=
  { name : string;
    password : string;
    passwordAgain : string }.

Record StoredEntry :=
  { seName : string;
    sePassword : string }.

Definition validPassword (p : string) : Prop :=
  8 <=? String.length p.

Definition ValidStoredEntry := { entry : StoredEntry | validPassword entry.(sePassword)}.

Record Model :=
  { users : list ValidStoredEntry;
    errors : list string;
    currentEntry : Entry }.

MetaCoq Run (make_setters Entry).
MetaCoq Run (make_setters StoredEntry).
MetaCoq Run (make_setters Model).

(* Goal (string -> Entry -> True). *)
(*   Set Printing All. *)
(*   intros s e. set (e<| name := s |>). *)
(*   unfold SetterFromGetter,setter_from_getter_Entry_name,set_Entry_name in *. cbn in *. *)

Inductive Msg :=
  | MsgName (_ : string)
  | MsgPassword (_ : string)
  | MsgPasswordAgain (_ : string).

Definition ValidEntry :=
  {entry : Entry | validPassword entry.(password)
                   /\ entry.(password) =? entry.(passwordAgain)}.

Definition updateEntry : Msg -> Entry -> Entry :=
  fun msg model =>
  match msg with
    | MsgName newName =>
       model<| name := newName |>
    | MsgPassword newPassword =>
      model<| password := newPassword |>
    | MsgPasswordAgain newPassword =>
      model<| passwordAgain := newPassword |>
  end.

Definition emptyNameError := "Empty name!".
Definition passwordsDoNotMatchError := "Passwords do not match!".
Definition passwordIsTooShortError := "Password is too short".

Definition validateModel : Model -> list string
  := fun model =>
       let res := [ (~~ (model.(currentEntry).(name) =? ""), emptyNameError)
                  ; (model.(currentEntry).(password) =? model.(currentEntry).(passwordAgain), passwordsDoNotMatchError)
                  ; (8 <=? String.length model.(currentEntry).(password), passwordIsTooShortError)] in
       map snd (filter (fun x => ~~ x.1) res).


Inductive StorageMsg :=
   Add
 | UpdateEntry (_ : Msg).

Program Definition toStoredEntry : ValidEntry -> StoredEntry
  := fun entry =>
       {| seName := entry.(name); sePassword := entry.(password) |}.

Program Definition updateModel : StorageMsg -> Model -> Model * Cmd StorageMsg
  := fun msg model =>
       match msg with
       | Add =>
         match validateModel model with
         | [] => let newEntry := toStoredEntry model.(currentEntry) in
                (model<| users := newEntry :: model.(users) |>, none)
         | errs => (model<| errors := errs |>, none)
         end
       | UpdateEntry entryMsg =>
         (model<|currentEntry := updateEntry entryMsg model.(currentEntry) |>, none)
       end.
Next Obligation.
  cbn in *;intros.
  destruct (name (currentEntry model) =? "")
           eqn:name_empty;tryfalse.
  destruct (password (currentEntry model) =? passwordAgain (currentEntry model))
           eqn: passwords_eq;tryfalse.
  destruct (8 <=? String.length (password (currentEntry model)))
           eqn:password_long_enough;tryfalse.
  auto.
Qed.
Next Obligation.
  cbn in *;intros.
    destruct (name (currentEntry model) =? "")
           eqn:name_empty;tryfalse.
  destruct (password (currentEntry model) =? passwordAgain (currentEntry model))
           eqn: passwords_eq;tryfalse.
  destruct (8 <=? String.length (password (currentEntry model)))
           eqn:password_long_enough;tryfalse.
  auto.
Qed.
Next Obligation.
  cbn in *;intros ??????. tryfalse.
Qed.


Definition initModel : Model * Cmd StorageMsg :=
  let entry :=
      {| users := []
       ; errors := []
       ; currentEntry := Build_Entry "" "" "" |} in
  (entry, none).


Definition extract_elm_within_coq (should_inline : kername -> bool) :=
{|
check_wf_env_func := fun Σ : PCUICAst.PCUICEnvironment.global_env =>
                     Ok (assume_env_wellformed Σ);
pcuic_args := {|
              optimize_prop_discr := true;
              transforms := [dearg_transform true true true true true
                            ;Inlining.transform should_inline] |} |}.

Instance ElmBoxes : MidlangPrintConfig :=
  {| term_box_symbol := "()"; (* the inhabitant of the unit type *)
     type_box_symbol := "()"; (* unit type *)
     any_type_symbol := "()"; (* unit type *)
     print_full_names := false |}.

Definition general_wrapped (Σ : global_env) (pre post : string)
           (seeds : KernameSet.t)
           (should_inline : list kername)
           (ignore: list kername) (TT : list (kername * string)) : result string string :=
  Σ <- extract_template_env
        (extract_elm_within_coq (fun kn => existsb (eq_kername kn) should_inline))
         Σ
         seeds
         (fun k => existsb (eq_kername k) ignore);;
  let TT_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') TT) in
  '(_, s) <- finish_print (print_env Σ TT_fun);;
  ret (pre ++ nl ++ s ++ nl ++ post).

Record ElmMod :=
  { elmmd_extract : list ({T : Type & T})}.

Definition USER_FORM_APP : ElmMod :=
  {| elmmd_extract := [ existT _  updateModel; existT _ initModel] |}.

Definition header_and_imports : string :=
<$ "module Main exposing (main)"
; ""
; "import Browser"
; "import Html exposing (..)"
; "import Html.Attributes exposing (..)"
; "import Html.Events exposing (onInput, onClick)"
$>.

Definition preamble : string :=
  <$ "type alias Prod_ a b = (a,b)"
   ; ""
   ; "string_eq : String -> String -> Bool"
   ; "string_eq s1 s2 = s1 == s2"
   ; ""
   ; "succ : Int -> Int"
   ; "succ n = n + 1"
   ; ""
   ; "nat_le : Int -> Int -> Bool"
   ; "nat_le n1 n2 = n1 <= n2"
   ; ""
  $>.

Notation "'remap_ctor' c1 'of' ind 'to' c2" := ((<%% ind %%>.1, c1), c2) (at level 100).

Definition TT :=
  [ remap <%% bool %%> "Bool"
  ; remap <%% negb %%> "not"

  ; remap <%% string %%> "String"
  ; remap <%% String.eqb %%> "string_eq"
  ; remap <%% String.length %%> "String.length"
  ; remap_ctor "EmptyString" of string to """"""
  ; remap <%% emptyNameError %%> ("""" ++ emptyNameError ++ """")
  ; remap <%% passwordsDoNotMatchError %%> ("""" ++ passwordsDoNotMatchError ++ """")
  ; remap <%% passwordIsTooShortError %%> ("""" ++ passwordIsTooShortError ++ """")

  ; remap <%% nat %%> "Int"
  ; remap_ctor "O" of nat to "0"
  ; remap_ctor "S" of nat to "succ"
  ; remap <%% Nat.leb %%> "nat_le"

  ; remap <%% prod %%> "Prod_"
  ; remap_ctor "pair" of prod to "Tuple.pair"
  ; remap <%% @fst %%> "Tuple.first"
  ; remap <%% @snd %%> "Tuple.second"

  ; remap <%% list %%> "List"
  ; remap_ctor "nil" of list to "[]"
  ; remap_ctor "cons" of list to "(::)"
  ; remap <%% filter %%> "List.filter"
  ; remap <%% map %%> "List.map"

  (* Elm infrastructure*)
  ; remap <%% Cmd %%> "Cmd"
  ; remap_ctor "none" of Cmd to "Cmd.none"
  ].

Definition to_inline :=
  [<%% @setter_from_getter_Entry_name %%>
  ;<%% setter_from_getter_Model_users %%>
  ;<%%setter_from_getter_Model_errors %%>
  ;<%%setter_from_getter_Model_currentEntry%%>
  ;<%%setter_from_getter_Entry_password%%>
  ;<%%setter_from_getter_Entry_passwordAgain%%>
  ].

Definition elm_extraction (m : ElmMod) (TT : list (kername * string)) : TemplateMonad _ :=
  '(Σ,_) <- tmQuoteRecTransp m false ;;
  seeds <- monad_map extract_def_name_exists m.(elmmd_extract);;
  res <- tmEval lazy
               (general_wrapped
                  Σ
                  (header_and_imports ++ nl ++ nl ++ preamble) ""
                  (KernameSetProp.of_list seeds)
                  to_inline
                  (<%% @SetterFromGetter %%> :: map fst TT)
                  TT);;
  match res with
  | Ok prog => tmMsg prog
  | Err e => tmFail e
  end.

Redirect "examples/elm-web-extract/UserList.elm" MetaCoq Run (elm_extraction USER_FORM_APP TT).
