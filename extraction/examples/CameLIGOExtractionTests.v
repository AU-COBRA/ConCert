(** * Extraction of various contracts to cameLIGO *)

From Coq Require Import PeanoNat ZArith Notations.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert.Embedding Require Import MyEnv CustomTactics.
From ConCert.Embedding Require Import Notations.
From ConCert.Extraction Require Import Common Optimize.
From ConCert.Extraction Require Import CameLIGOPretty CameLIGOExtract.
From ConCert.Execution Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.

From ConCert.Extraction Require Import Common.
From ConCert.Embedding.Extraction Require Import PreludeExt.
Require Import ConCert.Embedding.Extraction.CrowdfundingData.
Require Import ConCert.Embedding.Extraction.Crowdfunding.
From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.
Import MonadNotation.
Open Scope Z.

Definition PREFIX := "".
Definition bindOptCont {A B} (a : option A) (f : A -> option B) : option B :=
  match a with
  | Some a => f a
  | None => None
  end.

Definition dummy_chain :=
      "type chain = {
        chain_height     : nat;
        current_slot     : nat;
        finalized_height : nat;
        account_balance  : address -> nat
      }"
  ++ nl
  ++ "let dummy_chain : chain = {
        chain_height     = 0n;
        current_slot     = 0n;
        finalized_height = 0n;
        account_balance  = fun (a : address) -> 0n
      }".

Module Counter.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Notation address := nat.

  Definition operation := ActionBody.
  Definition storage := Z × address.

  Definition init (ctx : SimpleCallCtx) (setup : Z * address) : option storage :=
    let ctx_ := ctx in (* prevents optimisations from removing unused [ctx]  *)
    Some setup.

  Inductive msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Definition inc_balance (st : storage) (new_balance : Z) :=
    (st.1 + new_balance, st.2).

  Definition dec_balance (st : storage) (new_balance : Z) :=
    (st.1 - new_balance, st.2).

  Definition counter_inner (msg : msg) (st : storage)
    : option (list operation * storage) :=
    match msg with
    | Inc i =>
      if (0 <=? i) then
        Some ([],inc_balance st i)
      else None
    | Dec i =>
      if (0 <=? i) then
        Some ([],dec_balance st i)
      else None
    end.

  Definition counter (c : Chain) (ctx : SimpleCallCtx) st msg :=
    (* avoid erasing c and ctx arguments *)
    let c_ := c in
    let ctx_ := ctx in
    match msg with
    | Some msg =>counter_inner msg st
    | None => None
    end.

  Definition LIGO_COUNTER_MODULE : CameLIGOMod msg _ (Z × address) storage operation :=
    {| (* a name for the definition with the extracted code *)
        lmd_module_name := "cameLIGO_counter" ;

        (* and a test address *)
        lmd_prelude := CameLIGOPrelude ++ nl
                       ++ dummy_chain ++ nl
                       ++ "let test_account : address = (""tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx"" : address)";

        (* initial storage *)
        lmd_init := init ;

        (* no extra operations in [init] are required *)
        lmd_init_prelude := "" ;

        (* the main functionality *)
        lmd_receive_prelude := "";

        lmd_receive := counter;

        (* code for the entry point *)
        lmd_entry_point := CameLIGOPretty.printWrapper (PREFIX ++ "counter") "msg" "storage" CameLIGO_call_ctx ++ nl
                          ++ CameLIGOPretty.printMain |}.

End Counter.
Section CounterExtraction.
  Import Lia.
  Import Counter.
  (* Require Coq.Numbers.BinNums. *)
  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
  Definition TT_remap_counter : list (kername * string) :=
    [
      remap <%% Amount %%> "tez"
    ; remap <%% address_coq %%> "address"
    ; remap <%% time_coq %%> "timestamp"
    ; remap <%% nat %%> "address"
    ].

  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename :=
    [ ("Some", "Some")
    ; ("None", "None")
    ; ("Z0" ,"0")
    ; ("xH" ,"1n")
    ; ("nil", "[]") ].

  (** We run the extraction procedure inside the [TemplateMonad].
      It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
      that removes application of boxes to constants and constructors. *)

  (* Time MetaCoq Run
      (t <- CameLIGO_extraction PREFIX TT_remap_counter TT_rename LIGO_COUNTER_MODULE ;;
        tmDefinition LIGO_COUNTER_MODULE.(lmd_module_name) t).

  Print cameLIGO_counter.
  Definition printed := Eval vm_compute in cameLIGO_counter.
    (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "examples/cameligo-extract/CounterCertifiedExtraction.ligo" MetaCoq Run (tmMsg printed). *)

End CounterExtraction.

Module Crowdfunding.
  From ConCert.Embedding.Extraction Require Import SimpleBlockchainExt.
  (* Import PreludeExt CrowdfundingData Crowdfunding SimpleBlockchainExt. *)
  Notation storage := ((time_coq × Z × address_coq) × Maps.addr_map_coq × bool).
  Notation params := ((time_coq × address_coq × Z × Z) × msg_coq).
  Definition crowdfunding_init (ctx : SimpleCallCtx)
            (setup : (time_coq × Z × address_coq)) : option storage :=
    if ctx.2.2.1 =? 0 then Some (setup, (Maps.mnil, false)) else None.
    (* (unfolded Init.init) setup ctx. *)
    Open Scope Z.
    Import ListNotations.
    Import AcornBlockchain.
    Import MonadNotation.
    Import CrowdfundingContract.
    Import Validate.
    Import Receive.

  Definition crowdfunding_receive_inner
            (params : params)
            (st : storage) : option (list SimpleActionBody_coq × storage) :=
    receive params.2 st params.1.

  Definition crowdfunding_receive (c : Chain) (ctx : SimpleCallCtx) st msg :=
    (* prevent them from getting erased *)
    let c_ := c in
    let ctx_ := ctx in
    match msg with
    | Some msg => crowdfunding_receive_inner msg st
    | None => None
    end.

  Open Scope string_scope.

  Definition CF_MODULE :
    CameLIGOMod params SimpleCallCtx (time_coq × Z × address_coq) storage SimpleActionBody_coq :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameLIGO_crowdfunding" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude :=
        CameLIGOPrelude
          ++ nl
          ++ dummy_chain
          ++ nl
          ++ "type storage = ((timestamp * (tez * address)) * ((address,tez) map * bool))"
          ++ nl
          ++ "let test_account : address = (""tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx"" : address)"
          ++ nl
          ++ "let init_storage :  (timestamp * (tez * address)) =
          (Tezos.now, (42tez,(""tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx"": address)))";

      (* initial storage *)
      lmd_init := crowdfunding_init ;

      (* init requires some extra operations *)
      lmd_init_prelude := "";

      lmd_receive_prelude := "";

      (* the main functionality *)
      lmd_receive := crowdfunding_receive;

      (* code for the entry point *)
      lmd_entry_point :=
        CameLIGOPretty.printWrapper (PREFIX ++ "crowdfunding_receive")
                                    "((timestamp * (address * (tez * tez))) * msg_coq)"
                                    "storage"
                                    CameLIGO_call_ctx
                                    ++ nl
                        ++ CameLIGOPretty.printMain |}.

  (** We run the extraction procedure inside the [TemplateMonad].
      It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
      that removes application of boxes to constants and constructors. *)

End Crowdfunding.

Section CrowdfundingExtraction.

  Import Crowdfunding.
  Import CrowdfundingContract.
  Import Validate.
  Import Receive.
  Import SimpleBlockchainExt.
  Import AcornBlockchain.

  Definition TT_remap_crowdfunding : list (kername * string) :=

  [  (* types *)
    remap <%% address_coq %%> "address"
  ; remap <%% time_coq %%> "timestamp"
  ; remap <%% SimpleActionBody_coq %%> "operation"
  ; remap <%% Maps.addr_map_coq %%> "(address,tez) map"

  (* operations *)
  ; remap <%% ltb_time %%> "ltb_time"
  ; remap <%% leb_time %%> "leb_time"
  ; remap <%% eqb_addr %%> "eq_addr"
  ; remap <%% Maps.add_map %%> "Map.add"
  ; remap <%% lookup_map' %%> "Map.find_opt"
  ].

  Definition TT_rename_crowdfunding :=
    [ ("Z0" ,"0tez")
    ; ("nil", "[]")
    ; ("mnil", "Map.empty")
    ; ("tt", "()") ].

  Time MetaCoq Run
  (t <- CameLIGO_extraction PREFIX TT_remap_crowdfunding TT_rename_crowdfunding CF_MODULE ;;
    tmDefinition CF_MODULE.(lmd_module_name) t
  ).

  Print cameLIGO_crowdfunding.

  Definition printed := Eval vm_compute in cameLIGO_crowdfunding.
    (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "examples/cameligo-extract/CrowdfundingCertifiedExtraction.ligo" MetaCoq Run (tmMsg printed).

End CrowdfundingExtraction.

From ConCert.Execution.Examples Require EIP20Token.

Section EIP20TokenExtraction.
  Import EIP20Token.
  From ConCert.Utils Require Import RecordUpdate.
  Import RecordSetNotations.
  Require Import Containers.
  From stdpp Require gmap.

    Definition init (ctx : ContractCallContext) (setup : EIP20Token.Setup) : option EIP20Token.State :=
    Some {| total_supply := setup.(init_amount);
            balances := FMap.add (EIP20Token.owner setup) (init_amount setup) FMap.empty;
            allowances := FMap.empty |}.
  Open Scope Z_scope.
  Definition receive_ (chain : Chain)
       (ctx : ContractCallContext)
       (state : EIP20Token.State)
       (maybe_msg : option EIP20Token.Msg)
    : option (list ActionBody * EIP20Token.State) :=
    match EIP20Token.receive chain ctx state maybe_msg with
    | Some x => Some (x.2, x.1)
    | None => None
    end.
  Close Scope Z_scope.

  (* A specialized version of FMap's partial alter, w.r.t. FMap Address N *)
  Definition partial_alter_addr_nat : string :=
       "let partial_alter_addr_nat (f : nat option -> nat option)" ++ nl
    ++ "                           (k : address)" ++ nl
    ++ "                           (m : (address,nat) map) : (address,nat) map =" ++ nl
    ++ "  match Map.find_opt k m with" ++ nl
    ++ "    Some v -> Map.update k (f v) m" ++ nl
    ++ "  | None -> Map.update k (f (None : nat option)) m" ++ nl.

  Definition option_map_state_acts : string :=
       "let option_map_state_acts (f : state -> (state * operation list)) (o : state option) =" ++ nl
    ++ "  match o with" ++ nl
    ++ "    Some a -> Some (f a)" ++ nl
    ++ "    | None -> (None : (state * operation list))".

  Definition bind_option_state : string :=
       "let bind_option_state (a, b, c : unit) (m : state option) (f : state -> state option) : state option =" ++ nl
    ++ "match m with" ++ nl
    ++ "    Some a -> f a" ++ nl
    ++ "  | None -> (None : state option)".

  Definition with_default_N : string :=
       "let with_default_N (n : nat) (m : nat option) : n =" ++ nl
    ++ "  match m with" ++ nl
    ++ "    Some m -> m" ++ nl
    ++ "  | None -> n".

  Definition LIGO_EIP20Token_MODULE : CameLIGOMod EIP20Token.Msg ContractCallContext EIP20Token.Setup EIP20Token.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameLIGO_eip20token" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := CameLIGOPrelude;

      (* initial storage *)
      lmd_init := init ;

      lmd_init_prelude := "";

      (* the main functionality *)
      lmd_receive_prelude := partial_alter_addr_nat ++ nl ++
      option_map_state_acts ++ nl ++
      bind_option_state ++ nl ++
      with_default_N;
      lmd_receive := receive_ ;

      (* code for the entry point *)
      lmd_entry_point := CameLIGOPretty.printWrapper (PREFIX ++ "eip20token") "msg" "state" CameLIGO_contractCallContext ++ nl
                        ++ CameLIGOPretty.printMain |}.

  Definition TT_remap_eip20token : list (kername * string) :=
  [
    remap <%% @ContractCallContext %%> "(adress * (address * int))"
  ; remap <%% eqb_addr %%> "eq_addr"
  ; remap <%% @Extras.with_default %%> "with_default_N"
  ; remap <%% @Monads.bind %%> "bind_option_state"
  ; remap <%% Monads.Monad_option %%> "()"

  ; remap <%% @stdpp.base.insert %%> "Map.add"
  ; remap <%% @stdpp.base.lookup %%> "Map.find_opt"
  ; remap <%% @stdpp.base.empty %%> "Map.empty"
  ; remap <%% @stdpp.base.partial_alter %%> "partial_alter_addr_nat"
  ; remap <%% @gmap.gmap_partial_alter %%> ""
  ; remap <%% @fin_maps.map_insert %%> ""
  ; remap <%% @gmap.gmap_empty %%> ""
  ; remap <%% @gmap.gmap_lookup %%> ""
  ; remap <%% @address_eqdec %%> ""
  ; remap <%% @address_countable %%> ""
  ; remap <%% option_map %%> "option_map_state_acts"
  ].

  Definition TT_rename_eip20token :=
    [ ("Z0" ,"0tez")
    ; ("N0", "0n")
    ; ("N1", "1n")
    ; ("nil", "[]")
      (* monad hack *)
    ; ("Monad_option", "()")
    ; ("tt", "()") ].

  (* Time MetaCoq Run
  (t <- CameLIGO_extraction PREFIX TT_remap_eip20token TT_rename_eip20token LIGO_EIP20Token_MODULE ;;
    tmDefinition LIGO_EIP20Token_MODULE.(lmd_module_name) t
  ).

  Print cameLIGO_eip20token.

  Definition printed := Eval vm_compute in cameLIGO_eip20token.
    (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "examples/cameligo-extract/eip20tokenCertifiedExtraction.ligo" MetaCoq Run (tmMsg printed). *)

End EIP20TokenExtraction.



Section TestExtractionPlayground.
  Import EIP20Token.
  From ConCert.Utils Require Import RecordUpdate.
  Import RecordSetNotations.
  Require Import Containers.
  From stdpp Require gmap.

  Open Scope N_scope.
  Definition test_try_transfer (from : Address)
       (to : Address)
       (amount : TokenValue)
       (state : State) : option State :=
    let from_balance := Extras.with_default 0 (FMap.find from state.(balances)) in
    if from_balance <? amount
    then None
    else let new_balances := FMap.add from (from_balance - amount) state.(balances) in
         let new_balances := FMap.partial_alter (fun balance => Some (Extras.with_default 0 balance + amount)) to new_balances in
         Some ({|
          balances := new_balances;
          total_supply := state.(total_supply);
          allowances := state.(allowances);
        |}).
  Open Scope bool_scope.
  Definition test_try_transfer_from (delegate : Address)
       (from : Address)
       (to : Address)
       (amount : TokenValue)
       (state : State) : option State :=
  match FMap.find from state.(allowances) with
  | Some from_allowances_map =>
  match FMap.find delegate from_allowances_map with
  | Some delegate_allowance =>
  let from_balance := Extras.with_default 0 (FMap.find from state.(balances)) in
  if (delegate_allowance <? amount) || (from_balance <? amount)
  then None
  else let new_allowances := FMap.add delegate (delegate_allowance - amount) from_allowances_map in
       let new_balances := FMap.add from (from_balance - amount) state.(balances) in
       let new_balances := FMap.partial_alter (fun balance => Some (Extras.with_default 0 balance + amount)) to new_balances in
       Some ({|
        balances := new_balances;
        allowances := FMap.add from new_allowances state.(allowances);
        total_supply := state.(total_supply)|})
  | _ => None
  end
  | _ => None
  end.

  Definition test_init (ctx : ContractCallContext) (setup : EIP20Token.Setup) : option EIP20Token.State :=
    Some {| total_supply := setup.(init_amount);
            balances := FMap.empty;
            allowances := FMap.empty |}.
  Open Scope Z_scope.
  Definition test_receive (chain : Chain)
       (ctx : ContractCallContext)
       (state : EIP20Token.State)
       (maybe_msg : option EIP20Token.Msg)
    : option (list ActionBody * EIP20Token.State) :=
    let chain_ := chain in
    let sender := ctx.(ctx_from) in
    let without_actions := option_map (fun new_state => ([], new_state)) in
    match maybe_msg with
    | Some (transfer to amount) => without_actions (test_try_transfer sender to amount state)
    | Some (transfer_from from to amount) => without_actions (test_try_transfer_from sender from to amount state)
    (* Other endpoints are not included in this extraction test *)
    | _ => None
    end.

  Close Scope Z_scope.
  Close Scope N_scope.

  Definition playground_module : CameLIGOMod EIP20Token.Msg ContractCallContext EIP20Token.Setup EIP20Token.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
      lmd_module_name := "playground_mod" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := CameLIGOPrelude;

      (* initial storage *)
      lmd_init := test_init;

      lmd_init_prelude := "";

      (* the main functionality *)
      lmd_receive_prelude := partial_alter_addr_nat ++ nl ++
      option_map_state_acts ++ nl ++
      bind_option_state ++ nl ++
      with_default_N;

      lmd_receive := test_receive ;

      (* code for the entry point *)
      lmd_entry_point := CameLIGOPretty.printWrapper (PREFIX ++ "eip20token") "msg" "state" CameLIGO_contractCallContext ++ nl
                        ++ CameLIGOPretty.printMain |}.


  (* Time MetaCoq Run
  (t <- CameLIGO_extraction PREFIX TT_remap_eip20token TT_rename_eip20token playground_module ;;
    tmDefinition playground_module.(lmd_module_name) t
  ).

  Print playground_mod.

  Definition printed := Eval vm_compute in playground_mod.
    (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "examples/cameligo-extract/eip20tokenCertifiedExtraction.ligo" MetaCoq Run (tmMsg printed). *)

End TestExtractionPlayground.
