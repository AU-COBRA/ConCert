From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Monad.
From ConCert.Execution Require OptionMonad.
From ElmExtraction Require Import Common.
From ElmExtraction Require Import ElmExtract.
From MetaCoq.Erasure.Typed Require Import CertifyingInlining.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From ConCert.Extraction Require Import SpecializeChainBase.
From ElmExtraction Require Import PrettyPrinterMonad.
From ConCert.Examples.Escrow Require Import Escrow.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Template Require Import All.
From Coq Require Import List.
From Coq Require Import String.

Import MCMonadNotation.
Open Scope string.

#[local]
Instance EscrowMidlangBoxes : ElmPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     false_elim_def := "false_rec ()";
     print_full_names := true; (* full names to avoid clashes *)|}.

Definition TT_escrow : list (kername * string) :=
  [ remap <%% bool %%> "Bool"
  ; remap <%% @Address %%> "Int"].

Definition midlang_translation_map :=
  Eval compute in
        [(<%% @current_slot %%>, "current_slot");
        (<%% @address_eqb %%>, "Order.eq");
        (<%% @ctx_from %%>, "ctx_from");
        (<%% @ctx_contract_address %%>, "ctx_contract_address");
        (<%% @ctx_contract_balance %%>, "ctx_contract_balance");
        (<%% @ctx_amount %%>, "ctx_amount");
        (<%% @Chain %%>, "ConCertChain");
        (<%% @ContractCallContext %%>, "ConCertCallContext");
        (<%% @ConCert.Execution.Blockchain.ActionBody %%>, "ConCertAction");
        (<%% @ChainBase %%>, "ChainBaseWTF");
        (<%% @Amount %%>,"Z" )].

Definition midlang_escrow_translate (name : kername) : option string :=
  match find (fun '(key, _) => eq_kername key name) (TT_escrow ++ midlang_translation_map) with
  | Some (_, val) => Some val
  | None => None
  end.

Open Scope bool.
Definition should_inline kn :=
  eq_kername kn <%% @Monad.bind %%>
  || eq_kername kn <%% OptionMonad.Monad_option %%>
  || eq_kername kn <%% @ConCert.Execution.ResultMonad.Monad_result %%>
  || if String.index 0 "setter_from_getter" (string_of_kername kn) then true else false.

Definition extract_params :=
  {| check_wf_env_func := check_wf_env_func extract_within_coq;
     template_transforms := [template_inline should_inline];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [Optimize.dearg_transform (fun _ => None) true true true true true] |} |}.

Axiom extraction_chain_base : ChainBase.
#[local]
Existing Instance extraction_chain_base.

MetaCoq Run (p <- tmQuoteRecTransp Escrow.receive false ;;
             Σ <- run_transforms p.1 extract_params;;
             mpath <- tmCurrentModPath tt;;
             Certifying.gen_defs_and_proofs (Ast.Env.declarations p.1) (Ast.Env.declarations Σ) mpath "_cert_pass"%bs (KernameSet.singleton <%% @Escrow.receive %%>);;
             tmDefinition (String.of_string "escrow_env") Σ).

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

Definition extract_template_env_specialize
           (params : extract_template_env_params)
           (Σ : global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result_string ExAst.global_env :=
  let Σ := T2P.trans_global_env Σ in
  Σ <- specialize_ChainBase_env (PCUICProgram.trans_env_env Σ) ;;
  wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

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
  [ "import Basics exposing (..)";
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
    "ctx_contract_address _ = 0";
    "ctx_contract_balance _ = (Zpos (XO XH))";
    "ctx_amount ctx = (Zpos (XO XH))";
    "current_slot _ = O"
  ].

MetaCoq Run
        match escrow_extract with
        | Ok l => tmDefinition "escrow_env_extracted"%bs l
        | Err err => tmFail err
        end.

Definition escrow_result :=
  Eval vm_compute in
    ('(_, lines) <- finish_print_lines (print_env escrow_env_extracted midlang_escrow_translate);;
     ret lines).

Definition result :=
  match escrow_result with
  | Ok l => monad_map tmMsg (map String.of_string (midlang_prelude ++ l))
  | Err err => tmFail (String.of_string err)
  end.

Redirect "../extraction/tests/extracted-code/midlang-extract/MidlangEscrow.midlang" MetaCoq Run result.
