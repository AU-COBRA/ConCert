(** * Extraction of a crowdfunding contract *)

From ConCert.Extraction Require Import LiquidityExtract.
From ConCert.Extraction Require Import LiquidityPretty.
From ConCert.Examples.Crowdfunding Require Import CrowdfundingLiquidity.
From MetaRocq.Template Require Import All.

Import MonadNotation.



(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaRocq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)

Time MetaRocq Run
     (t <- liquidity_extraction PREFIX TT_remap TT_rename [] CROWDFUNDING_MODULE ;;
      tmDefinition CROWDFUNDING_MODULE.(lmd_module_name) t
     ).

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "liquidity-extract/CrowdfundingCertifiedExtraction.liq"
  Compute liquidity_crowdfunding.
