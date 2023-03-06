(** * Extraction of an interpreter for a stack based DSL *)
From MetaCoq.Template Require Import All.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require CameLIGOPretty.
From ConCert.Extraction Require CameLIGOExtract.
From ConCert.Examples.StackInterpreter Require Import StackInterpreterExtract.
From Coq Require Import String.
From Coq Require Import ZArith_base.
Local Open Scope string_scope.
Import MCMonadNotation.
Import Interpreter.



Module CameLIGOInterp.

  Import CameLIGOExtract CameLIGOPretty.
  #[local]
  Existing Instance PrintConfShortNames.PrintWithShortNames.

  Definition init (setup : unit)
                  : result storage Error :=
    (* prevents optimizations from removing unused [setup]. TODO: override masks instead *)
    let setup0 := setup in
    Ok [].

  Definition receive_ (c : Chain)
                      (ctx : ContractCallContext)
                      (s : storage)
                      (msg : option params)
                      : result (list action * storage) Error :=
    (* prevent optimizations from deleting these arguments from receive_'s type signature *)
    let c_ := c in
    let ctx_ := ctx in
    match msg with
    | Some msg => receive msg s
    | None => Err default_error
    end.

  Definition TT_remap_ligo : list (kername * string) :=
    [ (* remapping types *)
        remap <%% Z %%> "int"
      ; remap <%% bool %%> "bool"
      ; remap <%% unit %%> "unit"
      ; remap <%% option %%> "option"
      ; remap <%% Amount %%> "tez"
      ; remap <%% address_coq %%> "address"
      ; remap <%% time_coq %%> "timestamp"
      ; remap <%% list %%> "list"
      ; remap <%% string %%> "string"
      ; remap <%% ext_map %%> (print_finmap_type "string * int" "value")
      ; remap <%% action %%> "operation"
      (* remapping operations *)
      ; remap <%% Z.add %%> "addInt"
      ; remap <%% Z.mul %%> "multInt"
      ; remap <%% Z.sub %%> "subInt"
      ; remap <%% Z.eqb %%> "eqInt"
      ; remap <%% Z.leb %%> "leInt"
      ; remap <%% Z.ltb %%> "ltInt"
      ; remap <%% @lookup %%> "Map.find_opt"
      ; remap <%% @fst %%> "fst"
      ; remap <%% @snd %%> "snd"
      ; remap <%% andb %%> "andb"
      ; remap <%% one %%> "1"
    ].

  Definition LIGO_INTERP_MODULE : CameLIGOMod params ContractCallContext unit storage action Error :=
    {| (* a name for the definition with the extracted code *)
       lmd_module_name := "cameligo_interp" ;

       (* definitions of operations on ints, bools, pairs, ect. *)
       lmd_prelude := CameLIGOPrelude;

       lmd_init := init ;

       lmd_init_prelude := "";
       lmd_receive_prelude := "";

       lmd_receive := receive_ ;

       (* code for the entry point *)
       lmd_entry_point :=
         CameLIGOPretty.printMain "receive_" "params" "value list"
    |}.

  Time MetaCoq Run
    (CameLIGO_prepare_extraction [] TT_remap_ligo TT_rename_ctors_default [] "cctx_instance" LIGO_INTERP_MODULE).

  Time Definition cameligo_interp := Eval vm_compute in cameligo_interp_prepared.

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "../extraction/tests/extracted-code/cameligo-extract/StackInterpreter.mligo"
    MetaCoq Run (tmMsg (String.of_string cameligo_interp)).

End CameLIGOInterp.
