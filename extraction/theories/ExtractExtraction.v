(* This file is based on erasure/theories/Extraction.v from MetaCoq *)

Require Import FSets ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt.
From MetaCoq.Template Require Import MC_ExtrOCamlInt63.
From Coq Require Import ExtrOCamlFloats.


(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction Blacklist
           Classes config uGraph Universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Logic Common Common0 Equality Classes
           Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import PluginExtract.
From ConCert.Extraction Require Import Utils.

Extraction Inline Equations.Prop.Classes.noConfusion.
Extraction Inline Equations.Prop.Logic.eq_elim.
Extraction Inline Equations.Prop.Logic.eq_elim_r.
Extraction Inline Equations.Prop.Logic.transport.
Extraction Inline Equations.Prop.Logic.transport_r.
Extraction Inline Equations.Prop.Logic.False_rect_dep.
Extraction Inline Equations.Prop.Logic.True_rect_dep.
Extraction Inline Equations.Init.pr1.
Extraction Inline Equations.Init.pr2.
Extraction Inline Equations.Init.hidebody.
Extraction Inline Equations.Prop.DepElim.solution_left.

Extract Inductive Equations.Init.sigma => "( * )" ["(,)"].
Extract Constant PCUICTyping.guard_checking => "{ fix_guard = (fun _ _ _ -> true); cofix_guard = (fun _ _ _ -> true) }".
Extract Constant PCUICSafeChecker.check_one_ind_body => "(fun _ _ _ _ _ _ _ -> ret envcheck_monad __)".
Extract Constant timed =>
"(fun c x ->
   let time = Unix.gettimeofday() in
   let temp = x () in
   let time = (Unix.gettimeofday() -. time) in
   Feedback.msg_debug (Pp.str (Printf.sprintf ""%s executed in: %fs"" ((fun s-> (String.concat """" (List.map (String.make 1) s))) c) time));
              temp)".

Cd "plugin/src".
Separate Extraction PluginExtract.extract
         (* The following directives ensure separate extraction does not produce name clashes *)
         Bool Nat Coq.Strings.String Common utils ELiftSubst ETyping.
Cd "../..".
