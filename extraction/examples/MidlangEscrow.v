From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import MidlangExtract.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Inlining.
From ConCert.Extraction Require Import SpecializeChainBase.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import Utils.
From ConCert.Utils Require Import StringExtra.
From ConCert.Execution.Examples Require Import Escrow.

From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import PArith.
From Coq Require Import String.
From Coq Require Import ZArith.

From MetaCoq.Template Require Import Kernames All.

Import ListNotations.
Import MonadNotation.

Open Scope string.

Instance EscrowMidlangBoxes : MidlangPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     print_full_names := true; (* full names to avoid clashes*)|}.

Definition TT_escrow : list (kername * string) :=
  [    remap <%% bool %%> "Bool"
     ; remap <%% @Address %%> "Int"].

Definition midlang_translation_map :=
  Eval compute in
        [(<%% @current_slot %%>, "current_slot");
        (<%% @account_balance %%>, "account_balance");
        (<%% @address_eqb %%>, "Order.eq");
        (<%% @ctx_amount %%>, "ctx_amount");
        (<%% @ctx_from %%>, "ctx_from");
        (<%% @Chain %%>, "ConCertChain");
        (<%% @ContractCallContext %%>, "ConCertCallContext");
        (<%% @ConCert.Execution.Blockchain.ActionBody %%>, "ConCertAction");
        (<%% @ChainBase %%>, "ChainBaseWTF");
        (<%% @ctx_contract_address %%>, "contract_address");
        (<%% @Amount %%>,"Z" )].

Definition midlang_escrow_translate (name : kername) : option string :=
  match find (fun '(key, _) => eq_kername key name) (TT_escrow ++ midlang_translation_map) with
  | Some (_, val) => Some val
  | None => None
  end.

Axiom extraction_chain_base : ChainBase.
Existing Instance extraction_chain_base.

MetaCoq Run (p <- tmQuoteRecTransp Escrow.receive false ;;
             tmDefinition "escrow_env" p.1).

Open Scope bool.
Definition should_inline kn :=
  eq_kername kn <%% @Monads.bind %%>
  || eq_kername kn <%% Monads.Monad_option %%>
  || if String.index 0 "setter_from_getter" (string_of_kername kn) then true else false.

Definition ignored_concert_types :=
  Eval compute in
        [<%% @ActionBody %%>;
         <%% @Address %%>;
         <%% @Amount %%>;
         <%% @ChainBase %%>;
         <%% @Chain %%>;
         <%% @ContractCallContext %%>;
         <%% @SerializedValue %%>;
         <%% @RecordSet.SetterFromGetter %%>].

Import ResultMonad.

Definition extract_template_env_specialize
           (params : extract_template_env_params)
           (Σ : T.global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := SafeTemplateChecker.fix_global_env_universes Σ in
  let Σ := T2P.trans_global_decls Σ in
  Σ <- specialize_ChainBase_env Σ ;;
  wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

Definition extract_params :=
  {| check_wf_env_func := check_wf_env_func extract_within_coq;
     pcuic_args :=
       {| optimize_prop_discr := true;
          transforms := [Optimize.dearg_transform true true true true true;
                         Inlining.transform should_inline] |} |}.

Definition escrow_extract :=
  Eval vm_compute in
  extract_template_env_specialize
    extract_params
    escrow_env
    (KernameSet.singleton <%% @Escrow.receive %%>)
     (fun kn => contains kn (ignored_concert_types
                           ++ map fst midlang_translation_map
                           ++ map fst TT_escrow)).

Definition midlang_prelude :=
  ["import Basics exposing (..)";
  "import Blockchain exposing (..)";
  "import Bool exposing (..)";
  "import Int exposing (..)";
  "import Maybe exposing (..)";
  "import Order exposing (..)";
  "import Transaction exposing (..)";
  "import Tuple exposing (..)";
  "";
  "-- some dummy definitions (will be remapped properly in the future)";
  "type AccountAddress = Int";
  "type ConCertAction = Act_transfer Int Z";
  "type ConCertCallContext = CCtx Unit";
  "type ConCertChain = CChain Unit";
  "ctx_from ctx = 0";
  "ctx_amount ctx = (Zpos (XO XH))";
  "contract_address _ = 0";
  "account_balance _ _ = (Zpos (XO XH))";
  "current_slot _ = O"].

Definition escrow_result :=
  Eval vm_compute in
    (env <- escrow_extract;;
     '(_, lines) <- finish_print_lines (print_env env midlang_escrow_translate);;
     ret lines).

Definition result :=
  match escrow_result with
  | Ok l => monad_map tmMsg (midlang_prelude ++ l)
  | Err err => tmFail err
  end.

Redirect "examples/midlang-extract/MidlangEscrow.midlang" MetaCoq Run result.
