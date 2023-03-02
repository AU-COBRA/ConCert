(** Extraction of Dexter 2 to CameLIGO *)

From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith_base.
From MetaCoq.Template Require Import All.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Monad.
From ConCert.Execution Require OptionMonad.
From ConCert.Execution Require ContractCommon.
From ConCert.Examples.Dexter2 Require Dexter2CPMM.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import StringExtra.

Local Open Scope string_scope.

Notation s_to_bs := bytestring.String.of_string.

(** Printing configuration *)

(** We print long names for data types and constructors to avoid clashes, but keep constants' names short (no module name added) *)
Global Instance dexter2_print_config : CameLIGOPrintConfig :=
  {| print_ctor_name := PrintConfAddModuleNames.print_ctor_name_;
     print_type_name := PrintConfAddModuleNames.print_ind_type_name_;
     print_const_name := (fun x => bs_to_s (snd x)) |}.

(** * Common extraction setup *)

Definition call_to_token_ligo : String.string :=
  <$ "let call_to_token (type msg) (addr : address) (amt : nat) (msg : msg) : operation =" ;
     "  let token_ : msg contract =";
     "  match (Tezos.get_contract_opt (addr) : msg contract option) with";
     "    Some contract -> contract";
     "  | None -> (failwith ""Contract not found."" : msg contract) in";
     "  Tezos.transaction msg (natural_to_mutez amt) token_" $>.

Definition mk_callback_ligo : String.string :=
  "[@inline] let mk_callback (type msg)(addr : address) (msg : msg) : operation = call_to_token addr 0n msg".

(** Next two definition are borrowed from the actual Dexter 2 implementation
     https://gitlab.com/dexter2tz/dexter2tz/-/blob/1cec9d9333eba756603d6cd90ea9c70d482a5d3d/dexter.mligo *)
Definition natural_to_mutez_ligo : String.string :=
  "[@inline] let natural_to_mutez (a: nat): tez = a * 1mutez".

Definition mutez_to_natural_ligo : String.string :=
  "[@inline] let mutez_to_natural (a: tez): nat = a / 1mutez".

(** We change the signature of the original definition slightly, so it takes a [nat] and converts
    in to [tez]. We also return [operation option] instead of failing *)
Definition xtz_transfer_ligo : String.string :=
  <$ "let xtz_transfer (to_ : address) (amount_ : nat) : (operation, nat) result =";
     "  match (Tezos.get_contract_opt to_ : unit contract option) with";
     "    | None -> Err 0n";
     "    | Some c -> Ok (Tezos.transaction () (natural_to_mutez amount_) c)" $>.

Definition subNatTruncated_ligo : String.string :=
  "let subNTruncated (n : nat) (m : nat) : nat = if n < m then 0n else abs (n-m)".

Definition divN_res_ligo : String.string :=
  "let divN_res (n : nat) (m : nat) : (nat, nat) result = match ediv n m with | Some (q,_) -> Ok q | None -> Err 0n".

(** Remapping arithmetic operations. *)
(** We override the default remappings of arithmetic operations since it remaps [Z] to
    [tez], and [N] to [int], which is not suitable for our purposes. *)
Definition TT_remap_dexter2_arith : list (kername * String.string) :=
  [ remap <%% Z %%> "int"
  ; remap <%% N %%> "nat"

  ; remap <%% N.add %%> "addN"
  ; remap <%% N.sub %%> "subNTruncated"
  ; remap <%% N.mul %%> "multN"
  ; remap <%% N.leb %%> "lebN"
  ; remap <%% N.ltb %%> "ltbN"
  ; remap <%% N.eqb %%> "eqN"
  ; remap <%% N.modulo %%> "moduloN"

  ; remap <%% Z.add %%> "addInt"
  ; remap <%% Z.sub %%> "subInt"
  ; remap <%% Z.mul %%> "multInt"
  ; remap <%% Z.leb %%> "leInt"
  ; remap <%% Z.ltb %%> "ltInt"
  ; remap <%% Z.eqb %%> "eqInt"
  ; remap <%% Z.gtb %%> "gtbInt"
  ; remap <%% Z.even %%> "evenInt"
  ; remap <%% Z.abs_N %%> "abs"

  ; remap <%% Z.of_N %%> "z_of_N"
  ; remap <%% Z.to_N %%> "abs"
].

(** Remapping key-value maps *)
Definition TT_remap_dexter2 : list (kername * String.string) :=
   [remap <%% @ContractCallContext %%> CameLIGO_call_ctx_type_name
  ; remap <%% @FMap %%> "map"
  ; remap <%% @ContractCommon.AddressMap.add %%> "Map.add"
  ; remap <%% @ContractCommon.AddressMap.find %%> "Map.find_opt"
  ; remap <%% @ContractCommon.AddressMap.empty %%> "Map.empty"
  ; remap <%% @ContractCommon.AddressMap.update %%> "Map.update"
  ; remap <%% @FMap.add %%> "Map.add"
  ; remap <%% @FMap.find %%> "Map.find_opt"
  ; remap <%% @FMap.empty %%> "Map.empty"
  ; remap <%% @FMap.update %%> "Map.update"
  ; remap <%% @address_eqb %%> "eq_addr"
].

(** Definitions to inline *)
Definition TT_inlines_dexter2 : list kername :=
  [ <%% OptionMonad.Monad_option %%>
  ; <%% @ConCert.Execution.ResultMonad.Monad_result %%>
  ; <%% @Monad.bind %%>
  ; <%% @Monad.ret %%>
  ; <%% @Extras.with_default %%>
  ; <%% option_map %%>

  ; <%% @SetterFromGetter %%>
  ; <%% @Dexter2CPMM.setter_from_getter_State_tokenPool %%>
  ; <%% @Dexter2CPMM.setter_from_getter_State_selfIsUpdatingTokenPool %%>
  ; <%% @Dexter2CPMM.setter_from_getter_State_xtzPool %%>
  ; <%% @Dexter2CPMM.setter_from_getter_State_lqtTotal %%>
  ; <%% @Dexter2CPMM.setter_from_getter_State_freezeBaker %%>
  ; <%% @Dexter2CPMM.setter_from_getter_State_manager %%>
  ; <%% @Dexter2CPMM.setter_from_getter_State_lqtAddress %%>
  ; <%% Dexter2CPMM.default_error %%>
  ; <%% Dexter2FA12.default_error %%>
].
