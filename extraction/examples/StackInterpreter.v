(** * Extraction of an interpreter **)

From Coq Require Import PeanoNat ZArith Notations Bool.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.
From MetaCoq.PCUIC Require Import TemplateToPCUIC PCUICTyping.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Extraction Require Import LPretty LiquidityExtract
     Erasure Common.
From ConCert.Execution Require Import Containers Blockchain.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Definition PREFIX := "".

Definition map_key_type := (string * Z).
Definition action := ActionBody.

Module Interpreter.

  Inductive op : Set :=  Add | Sub | Mult | Lt | Le | Equal.

  Inductive instruction :=
  | IPushZ : Z -> instruction
  | IPushB : bool -> instruction
  | IObs : string * Z -> instruction
  | IIf : instruction
  | IElse : instruction
  | IEndIf : instruction
  | IOp : op -> instruction.

  Inductive value : Set := BVal : bool -> value | ZVal : Z -> value.

  Definition ext_map := FMap (string * Z) value.
  Definition lookup (k : string * Z) (m : ext_map) := FMap.find k m.

  Definition storage := list value.

  Definition init (ctx : SimpleCallCtx) (setup : unit) : option storage :=
    let ctx0 := ctx in (* prevents optimisations from removing unused [ctx]  *)
    Some [].

  Definition params := list instruction * ext_map.

  Definition obs0 s := IObs (s, 0%Z).

  Definition head_true_or_empty (l : list bool ) :=
    match l with
    | [] | true :: _ => true
    | _ => false
    end.

  Open Scope Z.
  Definition continue (i : Z) := (i =? 0)%Z.
  Definition one := 1%Z.
  Definition bool_to_cond (b : bool) : Z :=
    if b then 0 else one.
  Definition flip (i : Z) : Z :=
    if (i =? 0) then one else if (i =? one) then 0 else i.
  Definition reset_decrement (i : Z) : Z :=
    if (i <=? one) then 0 else i-one.

  Fixpoint interp (ext : ext_map) (insts : list instruction) (s : list value) (cond : Z) :=
    match insts with
    | [] => Some s
    | hd :: inst0 =>
        match hd with
        | IPushZ i => if continue cond then
                       interp ext inst0 (ZVal i :: s) cond
                     else interp ext inst0 s cond
        | IPushB b => if continue cond then
                       interp ext inst0 (BVal b :: s) cond
                     else interp ext inst0 s cond
        | IIf => if (cond =? 0) then
                  match s with
                  | BVal b :: s0 => interp ext inst0 s0 (bool_to_cond b)
                  | _ => None
                  end else interp ext inst0 s (one + cond)%Z
        | IElse => interp ext inst0 s (flip cond)
        | IEndIf => interp ext inst0 s (reset_decrement cond)
        | IObs p =>
          if continue cond then
            match lookup p ext with
            | Some v => interp ext inst0 (v :: s) cond
            | None => None
            end
          else interp ext inst0 s cond
        | IOp op =>
          if continue cond then
            match op with
            | Add => match s with
                    | ZVal i :: ZVal j :: s0 => interp ext inst0 (ZVal (i+j) :: s0)%Z cond
                    | _ => None
                    end
            | Sub => match s with
                      | ZVal i :: ZVal j :: s0 => interp ext inst0 (ZVal (i-j) :: s0)%Z cond
                      | _ => None
                      end
            | Mult => match s with
                     | ZVal i :: ZVal j :: s0 => interp ext inst0 (ZVal (i*j) :: s0)%Z cond
                     | _ => None
                            end
            | Le => match s with
                   | ZVal i :: ZVal j :: s0 => interp ext inst0 (BVal (i<=?j) :: s0)%Z cond
                   | _ => None
                   end
            | Lt => match s with
                   | ZVal i :: ZVal j :: s0 => interp ext inst0 (BVal (i<?j) :: s0)%Z cond
                   | _ => None
                   end
            | Equal => match s with
                      | ZVal i :: ZVal j :: s0 => interp ext inst0 (BVal (i =? j) :: s0)%Z cond
                      | _ => None
                     end
            end
          else interp ext inst0 s cond
        end
        end.

  Definition receive (p : params) (s : list value)
    : option (list action * storage) :=
    let s0 := s in (* prevents optimisations from removing unused [s]  *)
    match interp p.2 p.1 [] 0 with
    | Some v => Some ([],v)
    | None => None
    end.

End Interpreter.

Import Interpreter.

(** Input for the interpreter in Liquidity:
    ([IPushZ 0; IObs ("blah",0); IOp Add; IPushZ 1; IOp Equal], (Map [(("blah", 0), (ZVal 1))])) *)
Example test_interp :
  let env  := FMap.of_list [(("blah", 0%Z), (ZVal 1))] in
  interp env [IPushZ 0; IObs ("blah", 0); IOp Add; IPushZ 1; IOp Equal] [] 0 =
  Some [BVal true].
Proof. reflexivity. Qed.

(** Input for the interpreter in Liquidity:
([IPushZ 1; IPushZ 1; IOp Equal; IIf; IPushZ 1;IElse; IPushZ (-1);IEndIf], (Map [])) *)
Example test_interp_if_1 :
  interp FMap.empty [IPushZ 1; IPushZ 1; IOp Equal; IIf; IPushZ 1;IElse; IPushZ (-1);IEndIf] [] 0
  = Some [ZVal 1].
Proof. reflexivity. Qed.

Example test_interp_if_2 :
  interp FMap.empty [IPushZ 1; IPushZ 0; IOp Equal; IIf; IPushZ 1;IElse; IPushZ (-1);IEndIf] [] 0
  = Some [ZVal (-1)].
Proof. reflexivity. Qed.

Example test_interp_nested_if_1 :
  interp FMap.empty [IPushZ 0;
                    IPushZ 0;
                    IOp Equal;
                    IIf;
                    IPushZ (-1)%Z;
                    IPushZ (-1)%Z;
                    IOp Equal;
                    IIf;
                    IPushZ 2;
                    IElse;
                    IPushZ (-2);
                    IEndIf;
                    IElse;
                    IPushZ 0;
                    IEndIf
                    ] [] 0
  = Some [ZVal 2].
Proof. reflexivity. Qed.

Example test_interp_nested_if_2 :
  interp FMap.empty [IPushB false;
                    IIf;
                    IPushZ 1;
                    IElse;
                    IPushZ 0;
                    IPushZ 0;
                    IOp Equal;
                    IIf;
                    IPushZ (-1);
                    IElse;
                    IPushZ 0;
                    IEndIf
                    ] [] 0
  = Some [ZVal (-1)].
Proof. reflexivity. Qed.

(*     let strike = 50.0
        nominal = 1000.0
        theobs = obs ("Carlsberg",0)
    in scale (r nominal)
             (transl maturity
                    (iff (r strike !<! theobs)
                          (scale (theobs - r strike)
                                 (transfOne EUR "you" "me"))
                         zero)) *)
Definition call_option : list instruction :=
  [IObs ("Maturity", 0);
  IPushZ 90;
  IOp Equal;
  IIf;
  IObs ("Carlsberg", 0);
  IPushZ 50;
  IOp Lt;
  IIf;
  IPushZ 50;
  IObs ("Carlsberg", 0);
  IOp Sub;
  IPushZ 1000;
  IOp Mult;
  IElse;
  IPushZ 0;
  IEndIf;
  IElse;
  IPushZ 0;
  IEndIf].

(* ([IObs ("Maturity", 0);IPushZ 90;IOp Equal;IIf; IObs ("Carlsberg",0); IPushZ 50; IOp Lt; IIf; IPushZ 50; IObs ("Carlsberg", 0); IOp Sub; IPushZ 1000; IOp Mult; IElse; IPushZ 0; IEndIf; IElse; IPushZ 0; IEndIf], (Map [(("Carlsberg", 0), (ZVal 100));(("Maturity", 0), (ZVal 90))])) *)

(* try-liquidty: estimated fee 0.054191 *)

Example run_call_option_in_the_money :
  let env := FMap.of_list [(("Carlsberg", 0%Z), (ZVal 100));(("Maturity", 0%Z), (ZVal 90))] in
  interp env call_option [] 0
  = Some [ZVal 50000].
Proof. vm_compute. reflexivity. Qed.

Example run_call_option_out_the_money :
    let env := FMap.of_list [(("Carlsberg", 0%Z), (ZVal 30));(("Maturity", 0%Z), (ZVal 90))] in
  interp env call_option [] 0
  = Some [ZVal 0].
Proof. reflexivity. Qed.

(* A bigger test program for running in try-liquidity with arithmetic operations, lookups and some [Ifs] *)

Definition blah := [IPushZ 100; IPushZ 200; IOp Add; IPushZ 200; IOp Add;IPushZ 100;IOp Add;IPushZ 100;IOp Add; IPushZ 200; IOp Add;IPushZ 100; IPushZ 200; IOp Add; IPushZ 200; IOp Add;IPushZ 100;IOp Add;IPushZ 100;IOp Add; IPushZ 200; IOp Add;IPushZ 100; IPushZ 200; IOp Add; IPushZ 200; IOp Add;IPushZ 100;IOp Add;IPushZ 100;IOp Add; IPushZ 200; IOp Add;IPushZ 100; IOp Add; IPushZ 200; IOp Add;IPushZ 100;IOp Add;IPushZ 100;IOp Add; IPushZ 200; IOp Add;IPushZ 100;IOp Mult; IPushZ 3000; IOp Sub; IPushZ 10; IOp Add; IPushZ 10; IOp Mult; IPushB true; IIf; IPushZ 10; IPushZ 10; IOp Equal; IIf; IPushZ 10; IPushZ 10; IOp Add; IPushZ 10; IOp Add;IElse; IPushB true; IEndIf;  IPushZ 10;IOp Add; IPushZ 10; IOp Add; IPushZ 10; IOp Add; IPushZ 10; IOp Mult; IObs ("blah", 0); IOp Add; IObs ("blah", 0); IOp Add; IObs ("blah", 0); IOp Add; IObs ("blah", 0); IOp Add; IObs ("blah", 0); IOp Add; IObs ("blah", 0); IOp Add; IObs ("blah", 0); IOp Add; IObs ("blah", 0); IOp Add; IObs ("blah", 0); IOp Add; IElse; IPushZ 0; IPushZ 0; IPushZ 0; IPushZ 0; IPushZ 0; IPushZ 0; IPushZ 0; IPushZ 0; IPushZ 0; IEndIf ].
(* Just add the global environment (Map [(("blah", 0), (ZVal 0))])) *)
Compute List.length blah.

Definition print_finmap_type (prefix ty_key ty_val : string) :=
  parens false (ty_key ++ "," ++ prefix ++ ty_val) ++ " map".

(** A translation table for various constants we want to rename *)
Definition TT_remap : list (kername * string) :=
  [   (* remapping types *)
       remap <%% Z %%> "int"
     ; remap <%% bool %%> "bool"
     ; remap <%% unit %%> "unit"
     ; remap <%% option %%> "option"
     ; remap <%% Amount %%> "tez"
     ; remap <%% address_coq %%> "address"
     ; remap <%% time_coq %%> "timestamp"
     ; remap <%% list %%> "list"
     ; remap <%% string %%> "string"
     ; remap <%% ext_map %%> (print_finmap_type PREFIX "string * int" "value")
     ; remap <%% action %%> "operation"
     (* remapping operations *)
     ; remap <%% Z.add %%> "addInt"
     ; remap <%% Z.mul %%> "mulInt"
     ; remap <%% Z.sub %%> "subInt"
     ; remap <%% Z.eqb %%> "eqInt"
     ; remap <%% Z.leb %%> "leInt"
     ; remap <%% Z.ltb %%> "ltInt"
     ; remap <%% @lookup %%> "Map.find"
     ; remap <%% @fst %%> "fst"
     ; remap <%% @snd %%> "snd"
     ; remap <%% andb %%> "andb"
     ; remap <%% one %%> "1"].

Definition TT_rename : MyEnv.env string :=
     (* constructors *)
     [ ("Z0" ,"0")
     ; ("nil", "[]")].

Definition INTERP_MODULE : LiquidityMod params _ _ storage action :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "liquidity_interp" ;

     (* definitions of operations on ints, bools, pairs, ect. *)
     lmd_prelude := prod_ops ++ nl ++ int_ops ++ nl ++ bool_ops;

     lmd_init := init ;

     lmd_init_prelude := "";

     lmd_receive := receive ;

     (* code for the entry point *)
     lmd_entry_point :=
           printWrapper (PREFIX ++ "receive")
                        ++ nl
                        ++ printMain |}.

(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)
(* 
Time MetaCoq Run
     (t <- liquidity_extraction PREFIX TT_remap TT_rename INTERP_MODULE ;;
      tmDefinition INTERP_MODULE.(lmd_module_name) t
     ).

(** The extracted program can be printed and copy-pasted to the online Liquidity editor *)
Print liquidity_interp.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
(* Redirect "./extraction/examples/liquidity-extract/StackInterpreter.liq" Compute liquidity_interp. *)
*)
From ConCert.Extraction Require Import CameLIGOPretty CameLIGOExtract.

Definition receive_ (c : Chain) (ctx : SimpleCallCtx) (s : storage) (msg : option params):= 
  match msg with 
  | Some msg => receive msg s
  | None => None
  end.  

Definition TT_remap_ligo : list (kername * string) :=
  [   (* remapping types *)
       remap <%% Z %%> "int"
     ; remap <%% bool %%> "bool"
     ; remap <%% unit %%> "unit"
     ; remap <%% option %%> "option"
     ; remap <%% Amount %%> "tez"
     ; remap <%% address_coq %%> "address"
     ; remap <%% time_coq %%> "timestamp"
     ; remap <%% list %%> "list"
     ; remap <%% string %%> "string"
     ; remap <%% ext_map %%> (print_finmap_type PREFIX "string * int" "value")
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
     ; remap <%% one %%> "1"].

Definition LIGO_INTERP_MODULE : CameLIGOMod params SimpleCallCtx unit storage action :=
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
            CameLIGOPretty.printWrapper (PREFIX ++ "receive_") "params" "value list"
                        ++ nl
                        ++ CameLIGOPretty.printMain |}.

                          Time MetaCoq Run
  (t <- CameLIGO_extraction PREFIX TT_remap_ligo TT_rename LIGO_INTERP_MODULE ;;
    tmDefinition LIGO_INTERP_MODULE.(lmd_module_name) t
  ).

  Print cameligo_interp.

  Definition printed := Eval vm_compute in cameligo_interp.
    (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "./extraction/examples/cameligo-extract/stackintepreter.ligo" MetaCoq Run (tmMsg printed).
