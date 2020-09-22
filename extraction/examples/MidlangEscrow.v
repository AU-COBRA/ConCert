From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import MidlangExtract.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import SpecializeChainBase.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import StringExtra.

From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import PArith.
From Coq Require Import String.
From Coq Require Import ZArith.

From MetaCoq.Template Require Import All.

Import MonadNotation.

Open Scope string.

Notation "'eval_extract' x" :=
  ltac:(let x :=
            eval
              cbv
              beta
              delta [x receive RecordSet.set RecordSet.constructor Monads.bind Monads.Monad_option]
              iota in x in
       exact x) (at level 70).

From ConCert.Execution Require Import Escrow.

Definition TT_escrow : list (kername * string) :=
  [
       remap <% Z.add %> "add"
     ; remap <% Z.sub %> "sub"
     ; remap <% Z.leb %> "le"
     ; remap <% Z.ltb %> "lt"
     ; remap <% Z %> "Int"
     ; ((<%% Z %%>.1, "Z0"),"0")
     ; remap <% nat %> "AccountAddress"
     ; remap <% bool %> "Bool"
     ; remap <% @Address %> "AccountAddress"].

Definition midlang_translation_map :=
  Eval compute in
        [(<%% @current_slot %%>, "current_slot");
        (<%% @account_balance %%>, "account_balance");
        (<%% @address_eqb %%>, "address_eq");
        (<%% @ctx_amount %%>, "amount");
        (<%% @ctx_from %%>, "from");
        (<%% @Chain %%>, "ConCertChain");
        (<%% @ContractCallContext %%>, "ConCertCallContext");
        (<%% @ConCert.Execution.Blockchain.ActionBody %%>, "ConCertAction");
        (<%% @ChainBase %%>, "ChainBaseWTF");
        (<%% @act_transfer %%>, "transfer");
        (<%% @ctx_contract_address %%>, "contract_address")].

Definition midlang_escrow_translate (name : kername) : option string :=
  match find (fun '(key, _) => eq_kername key name) (TT_escrow ++ midlang_translation_map) with
  | Some (_, val) => Some val
  | None => None
  end.

Axiom extraction_chain_base : ChainBase.
Existing Instance extraction_chain_base.

Definition escrow_init :=
  eval_extract @Escrow.init.

Definition escrow_receive :=
  eval_extract @Escrow.receive.

Definition escrow_name := Eval compute in <%% escrow_receive %%>.


MetaCoq Run (p <- tmQuoteRecTransp escrow_receive false ;;
             tmDefinition "escrow_env" p.1).

Definition ignored_concert_types :=
  Eval compute in
        [<%% @ActionBody %%>;
         <%% @Address %%>;
         <%% @Amount %%>;
         <%% @ChainBase %%>;
         <%% @Chain %%>;
         <%% @ContractCallContext %%>;
         <%% @SerializedValue %%>].

Import ResultMonad.

Definition extract_template_env_specalize
           (params : extract_template_env_params)
           (Σ : T.global_env)
           (seeds : list kername)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := SafeTemplateChecker.fix_global_env_universes Σ in
  let Σ := T2P.trans_global_decls Σ in
  Σ <- specialize_ChainBase_env Σ ;;
  wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

Definition escrow_extract :=
  extract_template_env_specalize extract_within_coq
      escrow_env
      [escrow_name]
       (fun kn => contains kn (ignored_concert_types
                             ++ map fst midlang_translation_map
                             ++ map fst TT_escrow)).

Instance MidlangBoxes : BoxSymbol :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()"|}.

Definition escrow_result :=
  Eval vm_compute in
    (env <- escrow_extract ;;
     '(_, s) <- finish_print (print_env env escrow_env midlang_escrow_translate);;
     ret s).

Compute escrow_result.
