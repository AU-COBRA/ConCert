From MetaCoq.Template Require Import All.
From Coq Require Import String.
From Coq Require Import List.
From ConCert.Utils Require StringExtra.

Import ListNotations.
Import MCMonadNotation.

Module TCString := bytestring.String.

Open Scope string.

(** Generation of string constants using MetaCoq *)
Fixpoint mkNames (prefix : string) (ns : list string) (postfix : string) :=
  match ns with
  | [] => tmPrint "Done."%bs
  | n :: ns' => n' <- tmEval all (prefix ++ n ++ postfix)%string ;;
                  str <- tmQuote n';;
                  tmMkDefinition (TCString.of_string n) str;;
                  mkNames prefix ns' postfix
  end.

Fixpoint mdots (prefix : modpath) (l : list MCString.string) :=
  match l with
  | [] => prefix
  | h :: tl => mdots (MPdot prefix h) tl
  end.

(** Parses a string containing a file path and a module path
    separated in a way that helps to recover the kername structure.
 E.g. "Path/To/File#ModuleName.NestedModuleName" *)
Definition modpath_of_string (s : string) : modpath :=
  let fpath_mod := StringExtra.str_split "#" s in
  let fpath := hd "" fpath_mod in
  let module := hd "" (tl fpath_mod) in
  let fpath_items := map TCString.of_string (rev (StringExtra.str_split "/" fpath)) in
  let mod_items := map TCString.of_string (StringExtra.str_split "." module) in
  let fp := MPfile fpath_items in
  if module =? "" then fp
  else mdots fp mod_items.

(** Parses a string containing a file path, a module path separated
    and a name in a way that helps to recover the kername structure.
    E.g. "Path/To/File#ModuleName.NestedModuleName@FunctionName" *)
Definition kername_of_string (s : string) : kername :=
  let qualified_name := StringExtra.str_split "@" s in
  if Nat.eqb (List.length qualified_name) 1
  then (* unqualified name was given*)
    (MPfile [], TCString.of_string (hd "" qualified_name))
  else let path := hd "" qualified_name in
       let name := TCString.of_string (hd "" (tl qualified_name)) in
       (modpath_of_string path, name).

(** The printing functions below are similar to the ones from MetaCoq,
    but we use different separators for different parts of the [kername] *)
Notation s_to_bs := bytestring.String.of_string.
Definition string_of_dirpath (dp : dirpath) : string :=
  TCString.to_string (TCString.concat (s_to_bs "/") (rev dp)).

Fixpoint string_of_modpath (mp : modpath) : string :=
  match mp with
  | MPfile dp => string_of_dirpath dp
  | MPbound dp id _ =>
    (* currently not supported by the parser *)
    (string_of_dirpath dp ++ "$" ++ (TCString.to_string id))%string
  | MPdot mp0 id =>
    match mp0 with
    | MPfile _ => (string_of_modpath mp0 ++ "#" ++ (TCString.to_string id))%string
    | _ => (string_of_modpath mp0 ++ "." ++ (TCString.to_string id))%string
    end
  end.

Definition string_of_kername (kn : kername) :=
  (string_of_modpath kn.1 ++ "@" ++ TCString.to_string kn.2)%string.

Definition aRelevant (n : name) :=
  {| binder_name := n; binder_relevance := Relevant |}.

(** Extracts a constant name, inductive name or returns None *)
Definition to_kername (t : Ast.term) : option kername :=
  match t with
  | Ast.tConst c _ => Some c
  | Ast.tInd c _ => Some c.(inductive_mind)
  | _ => None
  end.

Definition to_string_name (t : Ast.term) : string :=
  match to_kername t with
  | Some kn => string_of_kername kn
  | None => "Not a constant or inductive"
  end.

Example qualified_bool : to_string_name (<% bool %>) = "Coq/Init/Datatypes@bool".
Proof. reflexivity. Qed.
