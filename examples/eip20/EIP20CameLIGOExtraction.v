(** * Extraction of various contracts to CameLIGO *)

From Coq Require Import String.
From MetaCoq.Template Require Import All.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require ContractCommon.
From ConCert.Examples.EIP20 Require EIP20Token.

Local Open Scope string_scope.

Existing Instance PrintConfShortNames.PrintWithShortNames.

Section EIP20TokenExtraction.

  Import EIP20Token.

  Definition init (setup : EIP20Token.Setup) : option EIP20Token.State :=
    Some {| total_supply := setup.(init_amount);
            balances := ContractCommon.AddressMap.add (EIP20Token.owner setup) (init_amount setup) ContractCommon.AddressMap.empty;
            allowances := ContractCommon.AddressMap.empty |}.

  Lemma EIP20Token_init_eq_init chain ctx setup :
    EIP20Token.init chain ctx setup = init setup.
  Proof. reflexivity. Qed.

  Definition receive_ (chain : Chain)
       (ctx : ContractCallContext)
       (state : EIP20Token.State)
       (maybe_msg : option EIP20Token.Msg)
    : option (list ActionBody * EIP20Token.State) :=
    match EIP20Token.receive chain ctx state maybe_msg with
    | Some x => Some (x.2, x.1)
    | None => None
    end.

  Definition LIGO_EIP20Token_MODULE : CameLIGOMod EIP20Token.Msg ContractCallContext EIP20Token.Setup EIP20Token.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameLIGO_eip20token" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := CameLIGOPrelude;

      (* initial storage *)
      lmd_init := init ;

      (* NOTE: printed as local [let]-bound definitions in the init *)
      lmd_init_prelude := "";

      (* TODO: maybe not needed, [lmd_prelude] should be enough *)
      lmd_receive_prelude := "";

      (* the main functionality *)
      lmd_receive := receive_ ;

      (* code for the entry point *)
      lmd_entry_point :=
        CameLIGOPretty.printMain "receive_" "msg" "state" |}.

  Definition TT_remap_eip20token : list (kername * string) :=
    TT_remap_default ++ [
    remap <%% @ContractCallContext %%> CameLIGO_call_ctx_type_name
  ; remap <%% @ctx_from %%> "ctx_from"
  ; remap <%% @ActionBody %%> "operation"

  ; remap <%% @FMap %%> "map"
  ; remap <%% @ContractCommon.AddressMap.add %%> "Map.add"
  ; remap <%% @ContractCommon.AddressMap.find %%> "Map.find_opt"
  ; remap <%% @ContractCommon.AddressMap.empty %%> "Map.empty"
  ].

  Definition TT_inlines_eip20token : list kername :=
    [
      <%% Monads.Monad_option %%>
    ; <%% @Monads.bind %%>
    ; <%% @Monads.ret %%>
    ; <%% bool_rect %%>
    ; <%% bool_rec %%>
    ; <%% option_map %%>
    ; <%% @Extras.with_default %%>

    ; <%% @setter_from_getter_State_balances %%>
    ; <%% @setter_from_getter_State_total_supply %%>
    ; <%% @setter_from_getter_State_allowances %%>
    ; <%% @set_State_balances %%>
    ; <%% @set_State_allowances%%>
    ].

  Time MetaCoq Run
  (CameLIGO_prepare_extraction TT_inlines_eip20token TT_remap_eip20token TT_rename_ctors_default [] "cctx_instance" LIGO_EIP20Token_MODULE).

  Time Definition cameLIGO_eip20token := Eval vm_compute in cameLIGO_eip20token_prepared.

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  (* TODO: uncomment, once this fix https://gitlab.com/ligolang/ligo/-/merge_requests/1452 makes it
     into a release version. *)
  Redirect "../extraction/tests/extracted-code/cameligo-extract/eip20tokenCertifiedExtraction.mligo"
  MetaCoq Run (tmMsg cameLIGO_eip20token).

End EIP20TokenExtraction.
