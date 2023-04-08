From ConCert.Extraction Require Import Common.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Utils Require Import monad_utils.
From Coq Require Import ZArith.
From Coq Require Import String.

Local Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
Local Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).
Local Coercion bytestring.String.to_string : bytestring.String.t >-> string.


Example pos_syn_to_nat_5 :
  pos_syn_to_nat (EAst.tApp _xI (EAst.tApp _xO _xH)) = Some 5.
Proof. reflexivity. Qed.

Example N_syn_to_nat_0 :
  N_syn_to_nat _N0 = Some 0.
Proof. reflexivity. Qed.

Example N_syn_to_nat_5 :
  N_syn_to_nat (EAst.tApp _Npos (EAst.tApp _xI (EAst.tApp _xO _xH))) = Some 5.
Proof. reflexivity. Qed.

Open Scope string.

Example N_syn_to_nat_fail :
  N_syn_to_nat (EAst.tApp _Npos (EAst.tApp _xI (EAst.tVar (s_to_bs "")))) = None.
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
  Z_syn_to_Z (EAst.tApp _Zpos (EAst.tApp _xI (EAst.tVar (s_to_bs "")))) = None.
Proof. reflexivity. Qed.

Import MCMonadNotation Core.
Open Scope monad_scope.

Definition result_err_bytestring A := result A bytestring.String.t.

Definition extract_ (p : program) : result_err_bytestring _ :=
  entry <- match snd p with
           | tConst kn _ => ret kn
           | _ => Err (s_to_bs "Expected program to be a tConst")
           end;;
  extract_template_env_within_coq
         (fst p)
         (Kernames.KernameSet.singleton entry)
         (fun k => false).

Definition extract_body {A} (def : A) : TemplateMonad _ :=
  p <- tmQuoteRec def ;;
  entry <- match snd p with
           | tConst kn _ => ret kn
           | _ => tmFail (s_to_bs "Expected program to be a tConst")
          end ;;
  res <- tmEval Common.lazy (extract_template_env_within_coq
               (fst p)
               (Kernames.KernameSet.singleton entry)
               (fun k => false));;
  match res with
  | Ok env => match Erasure.Ex.lookup_env env entry with
             | Some (Erasure.Ex.ConstantDecl (Erasure.Ex.Build_constant_body _ (Some b))) =>
                 tmDefinition (s_to_bs (snd entry ++ "_extracted")) b
             | Some _ => tmFail (s_to_bs "Not a constant or body is missing")
             | None => tmFail (s_to_bs "No constant in the extracted env")
             end
  | Err e => tmFail e
  end.

Open Scope N_scope.


(* TODO: Use QuickChick here?*)
(* NOTE: these numbers come from the Dexter contract, where the bug was discovered *)
Definition _997 : N := 997%N.

MetaCoq Run (extract_body _997).

Example N_syn_to_nat_997 :
  N_syn_to_nat _997_extracted = Some 997%nat.
Proof. reflexivity. Qed.

Definition _1000 : N := 1000%N.

MetaCoq Run (extract_body _1000).

Example N_syn_to_nat_1000 :
  N_syn_to_nat _1000_extracted = Some 1000%nat.
Proof. reflexivity. Qed.
