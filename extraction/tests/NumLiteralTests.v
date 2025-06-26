From ConCert.Extraction Require Import Common.
From MetaRocq.Erasure.Typed Require Import Extraction.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From MetaRocq.Template Require Import Ast.
From MetaRocq.Utils Require Import monad_utils.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import ZArith.




Example pos_syn_to_nat_5 :
  pos_syn_to_nat (EAst.tApp _xI (EAst.tApp _xO _xH)) = Some 5.
Proof. reflexivity. Qed.

Example N_syn_to_nat_0 :
  N_syn_to_nat _N0 = Some 0.
Proof. reflexivity. Qed.

Example N_syn_to_nat_5 :
  N_syn_to_nat (EAst.tApp _Npos (EAst.tApp _xI (EAst.tApp _xO _xH))) = Some 5.
Proof. reflexivity. Qed.

Open Scope bs_scope.

Example N_syn_to_nat_fail :
  N_syn_to_nat (EAst.tApp _Npos (EAst.tApp _xI (EAst.tVar ""))) = None.
Proof. reflexivity. Qed.

Example Z_syn_to_Z_0 :
  Z_syn_to_Z _Z0 = Some 0%Z.
Proof. reflexivity. Qed.

Example Z_syn_to_Z_5 :
  Z_syn_to_Z (EAst.tApp _Zpos (EAst.tApp _xI (EAst.tApp _xO _xH))) = Some 5%Z.
Proof. reflexivity. Qed.

Example Z_syn_to_Z_minus_5 :
  Z_syn_to_Z (EAst.tApp _Zneg (EAst.tApp _xI (EAst.tApp _xO _xH))) = Some (-5)%Z.
Proof. reflexivity. Qed.

Example Z_syn_to_Z_fail :
  Z_syn_to_Z (EAst.tApp _Zpos (EAst.tApp _xI (EAst.tVar ""))) = None.
Proof. reflexivity. Qed.

Import MRMonadNotation Core.
Open Scope monad_scope.

Definition result_err_bytestring A := result A bytestring.String.t.

(* TODO: tmp, revert once https://github.com/MetaRocq/metarocq/pull/1030 is resolved *)
Import List.
Import ListNotations.
From MetaRocq.Erasure.Typed Require Import Optimize.
Definition extract_within_rocq : extract_template_env_params :=
  {| template_transforms := [];
     check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform (fun _ => None) true false true true true] |} |}.

Definition extract_ (p : program) : result_err_bytestring _ :=
  entry <- match snd p with
           | tConst kn _ => ret kn
           | _ => Err "Expected program to be a tConst"
           end;;
  extract_template_env extract_within_rocq
         (fst p)
         (Kernames.KernameSet.singleton entry)
         (fun k => false).

Definition extract_body {A} (def : A) : TemplateMonad _ :=
  p <- tmQuoteRec def ;;
  entry <- match snd p with
           | tConst kn _ => ret kn
           | _ => tmFail "Expected program to be a tConst"
          end ;;
  res <- tmEval Common.lazy (extract_template_env extract_within_rocq
               (fst p)
               (Kernames.KernameSet.singleton entry)
               (fun k => false));;
  match res with
  | Ok env => match Erasure.Ex.lookup_env env entry with
             | Some (Erasure.Ex.ConstantDecl (Erasure.Ex.Build_constant_body _ (Some b))) =>
                 tmDefinition (snd entry ++ "_extracted")%bs b
             | Some _ => tmFail "Not a constant or body is missing"
             | None => tmFail "No constant in the extracted env"
             end
  | Err e => tmFail e
  end.

Open Scope N_scope.


(* TODO: Use QuickChick here?*)
(* NOTE: these numbers come from the Dexter contract, where the bug was discovered *)
Definition _997 : N := 997%N.

MetaRocq Run (extract_body _997).

Example N_syn_to_nat_997 :
  N_syn_to_nat _997_extracted = Some 997%nat.
Proof. reflexivity. Qed.

Definition _1000 : N := 1000%N.

MetaRocq Run (extract_body _1000).

Example N_syn_to_nat_1000 :
  N_syn_to_nat _1000_extracted = Some 1000%nat.
Proof. reflexivity. Qed.
