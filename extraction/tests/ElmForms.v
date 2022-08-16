(** * Elm web app example **)

(** We implement a simple web application allowing for adding users to
a list after validating the input data. We use the Coq version of
refinement types (a type with a predicate) to express the fact that
the list of users contains only valid data. *)

From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import ElmExtract.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import CertifyingInlining.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Utils Require Import StringExtra.
From ConCert.Utils Require Import RecordUpdate.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq Require Import utils.
From Coq Require Import ssrbool.
From Coq Require Import String.

Open Scope string.

Inductive Cmd (A : Type) : Set :=
  none.

Arguments none {_}.

(** An entry that corresponds to the user input.
    Contains "raw" data, potentially invalid *)
Record Entry :=
  { name : string;
    password : string;
    passwordAgain : string }.

Definition validPassword (p : string) : Prop :=
  8 <=? length p.

Definition nonEmptyString (s : string) : Prop :=
  s <> "".

(** An entry after validation *)
Definition ValidEntry :=
  {entry : Entry | nonEmptyString entry.(name)
                   /\ validPassword entry.(password)
                   /\ entry.(password) =? entry.(passwordAgain)}.


(** An entry with "raw" data that we are going to use for defining valid stored entries *)
Record StoredEntry :=
  { seName : string;
    sePassword : string }.

(** A valid entry that is stored in the list of users *)
Definition ValidStoredEntry :=
  { entry : StoredEntry | nonEmptyString entry.(seName)
                          /\ validPassword entry.(sePassword)}.

Definition seNames (l : list ValidStoredEntry) :=
  map (fun x => (proj1_sig x).(seName)) l.

(** The application model *)
Record Model :=
  { (** A list of valid entries such with unique user names *)
    users : {l : list ValidStoredEntry | NoDup (seNames l)};
    (** A list of errors after validation *)
    errors : list string;
    (** Current user input *)
    currentEntry : Entry }.


(** We derive setters for the records in order to use conveninet record update syntax *)
MetaCoq Run (make_setters Entry).
MetaCoq Run (make_setters StoredEntry).
MetaCoq Run (make_setters Model).

(** Messages for updating the model according to the current user input *)
Inductive Msg :=
  | MsgName (_ : string)
  | MsgPassword (_ : string)
  | MsgPasswordAgain (_ : string).

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
Definition passwordIsTooShortError := "Password is too short!".
Definition userAlreadyExistsError := "User already exists!".

Program Definition validateModel : Model -> list string
  := fun model =>
       let res :=
           [ (~~ existsb (fun nm => nm =? model.(currentEntry).(name)) (seNames model.(users)), userAlreadyExistsError)           ; (~~ (model.(currentEntry).(name) =? ""), emptyNameError)
           ; (model.(currentEntry).(password) =? model.(currentEntry).(passwordAgain), passwordsDoNotMatchError)
           ; (8 <=? length model.(currentEntry).(password), passwordIsTooShortError)] in
       map snd (filter (fun x => ~~ x.1) res).


(* Messages for updating the current entry and adding the current entry to the list of users  *)
Inductive StorageMsg :=
   Add
 | UpdateEntry (_ : Msg).


(** We translate the user input to the stored representation.
Note that the transation only works for valid entries *)
Program Definition toValidStoredEntry : ValidEntry -> ValidStoredEntry
  := fun entry =>
       {| seName := entry.(name); sePassword := entry.(password) |}.
Next Obligation.
  destruct entry as [e He];destruct He as (? & ? & ?);cbn;auto.
Qed.

Local Hint Resolve -> eqb_neq : core.
Local Hint Unfold nonEmptyString : core.

(** This tactic notation allows to extract information from the fact
that the validation succeeded *)
Tactic Notation "destruct_validation" :=
  unfold validateModel in *;
  destruct (existsb _ _) eqn:Hexists;
  destruct (name _ =? "")
           eqn:name_empty;
  destruct (password _ =? passwordAgain _)
           eqn: passwords_eq;
  destruct (8 <=? length (password _))
           eqn:password_long_enough;try discriminate.

Program Definition updateModel : StorageMsg -> Model -> Model * Cmd StorageMsg
  := fun msg model =>
       match msg with
       | Add =>
         match validateModel model with
         | [] =>
           let validEntry : ValidEntry := model.(currentEntry) in
           let newValidStoredEntry : ValidStoredEntry :=
                    toValidStoredEntry validEntry in
           let newList := newValidStoredEntry :: model.(users) in
           (model<| users := newList |>, none)
         | errs => (model<| errors := errs |>, none)
         end
       | UpdateEntry entryMsg =>
         (model<|currentEntry := updateEntry entryMsg model.(currentEntry) |>, none)
       end.
Solve Obligations with (cbn;intros;destruct_validation;auto).
Next Obligation.
  destruct_validation;auto.
  constructor.
  + intro Hin.
    remember (fun nm : string => nm =? name (currentEntry model)) as f.
    remember (seNames (proj1_sig model.(users))) as l.
    assert (Hex_in : exists x, In x l /\ f x = true).
    { exists model.(currentEntry).(name);subst;split. apply Hin. apply eqb_refl. }
    now apply existsb_exists in Hex_in.
  + destruct (model.(users)) as (l, l_nodup). cbn. auto.
Qed.

Local Hint Constructors NoDup : core.

Program Definition initModel : Model * Cmd StorageMsg :=
  let entry :=
      {| users := []
       ; errors := []
       ; currentEntry := Build_Entry "" "" "" |} in
  (entry, none).

Definition extract_elm_within_coq (should_inline : kername -> bool) :=
{| check_wf_env_func := fun Σ : PCUICAst.PCUICEnvironment.global_env =>
                          Ok (assume_env_wellformed Σ);
   template_transforms := [CertifyingInlining.template_inline should_inline ];
   pcuic_args := {| optimize_prop_discr := true;
                    extract_transforms :=
                      [dearg_transform (fun _ => None) true true true true true] |} |}.


Local Instance ElmBoxes : ElmPrintConfig :=
  {| term_box_symbol := "()"; (* the inhabitant of the unit type *)
     type_box_symbol := "()"; (* unit type *)
     any_type_symbol := "()"; (* unit type *)
     false_elim_def := "false_rec ()";
     print_full_names := false |}.

Import MCMonadNotation.

Definition general_wrapped (Σ : global_env) (pre post : string)
           (seeds : KernameSet.t)
           (to_inline : list kername)
           (ignore: list kername) (TT : list (kername * string)) : TemplateMonad _ :=
  let should_inline kn := existsb (eq_kername kn) to_inline in
  let extract_ignore kn := existsb (eq_kername kn) ignore in
  Σ <- extract_template_env_certifying_passes Ok (extract_elm_within_coq should_inline) Σ seeds extract_ignore;;
  let TT_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') TT) in
  p <- tmEval lazy (map_error (fun x => s_to_bs x) (finish_print (print_env Σ TT_fun))) ;;
  match p with
  | Ok (_,s) => tmEval lazy (pre ++ Common.nl ++ s ++ Common.nl ++ post)
  | Err s => tmFail s
  end.

Record ElmMod :=
  { elmmd_extract : list ({T : Type & T})}.

Definition USER_FORM_APP : ElmMod :=
  {| elmmd_extract := [ existT _ _ updateModel; existT _ _ initModel] |}.

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

Notation "'remap_ctor' c1 'of' ind 'to' c2" := ((<%% ind %%>.1, (s_to_bs c1)), c2) (at level 100).

Notation "'string_literal' s" :=
    (remap <%% s %%> (concat "" [""""; s; """"])) (at level 20).

Definition TT :=
  [ remap <%% bool %%> "Bool"
  ; remap <%% negb %%> "not"

  ; remap <%% string %%> "String"
  ; remap <%% eqb %%> "string_eq"
  ; remap <%% length %%> "String.length"
  ; remap_ctor "EmptyString" of string to """"""
  ; string_literal emptyNameError
  ; string_literal passwordsDoNotMatchError
  ; string_literal passwordIsTooShortError
  ; string_literal userAlreadyExistsError

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
  [<%% setter_from_getter_Entry_name %%>
  ;<%% setter_from_getter_Model_users %%>
  ;<%% setter_from_getter_Model_errors %%>
  ;<%% setter_from_getter_Model_currentEntry%%>
  ;<%% setter_from_getter_Entry_password%%>
  ;<%% setter_from_getter_Entry_passwordAgain%%>
  ].

Definition elm_extraction (m : ElmMod) (TT : list (kername * string)) : TemplateMonad _ :=
  '(Σ,_) <- tmQuoteRecTransp m false ;;
  seeds <- monad_map extract_def_name_exists m.(elmmd_extract);;
  general_wrapped Σ (header_and_imports ++ Common.nl ++ Common.nl ++ preamble ++ Common.nl ++ Common.nl ++ elm_false_rec) ""
                  (KernameSetProp.of_list seeds)
                  to_inline
                  (map fst TT)
                  TT.

Time MetaCoq Run (t <- elm_extraction USER_FORM_APP TT;;
                  tmDefinition (s_to_bs "extracted_app") t).

Redirect "tests/extracted-code/elm-web-extract/UserList.elm" MetaCoq Run (tmMsg (s_to_bs extracted_app)).
