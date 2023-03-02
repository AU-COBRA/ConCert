(** * Extraction of an interpreter for a stack based DSL *)
From MetaCoq.Template Require Import All.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Extraction Require Import Common.
From Coq Require Import Notations.
From Coq Require Import String.
From Coq Require Import ZArith_base.
Local Open Scope string_scope.
Import MCMonadNotation.

Definition map_key_type := (string * Z).
Definition action := ActionBody.

(* TODO: use the interpreter defined in StackInterpreter.v to avoid duplication. *)
Module Interpreter.

  Inductive op : Set := Add | Sub | Mult | Lt | Le | Equal.

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

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Definition init (ctx : SimpleCallCtx)
                  (setup : unit)
                  : result storage Error :=
    let ctx0 := ctx in
    let setup0 := setup in (* prevents optimizations from removing unused [ctx] and [setup] *)
    Ok [].

  Definition params := list instruction * ext_map.

  Open Scope Z.
  Definition continue_ (i : Z) := (i =? 0)%Z.
  Definition one := 1%Z.
  Definition bool_to_cond (b : bool) : Z :=
    if b then 0 else one.
  Definition flip (i : Z) : Z :=
    if (i =? 0) then one else if (i =? one) then 0 else i.
  Definition reset_decrement (i : Z) : Z :=
    if (i <=? one) then 0 else i-one.

  Fixpoint interp (ext : ext_map)
                  (insts : list instruction)
                  (s : storage)
                  (cond : Z)
                  : result storage Error :=
    match insts with
    | [] => Ok s
    | hd :: inst0 =>
        match hd with
        | IPushZ i => if continue_ cond then
                       interp ext inst0 (ZVal i :: s) cond
                     else interp ext inst0 s cond
        | IPushB b => if continue_ cond then
                       interp ext inst0 (BVal b :: s) cond
                     else interp ext inst0 s cond
        | IIf => if (cond =? 0) then
                  match s with
                  | BVal b :: s0 => interp ext inst0 s0 (bool_to_cond b)
                  | _ => Err default_error
                  end else interp ext inst0 s (one + cond)%Z
        | IElse => interp ext inst0 s (flip cond)
        | IEndIf => interp ext inst0 s (reset_decrement cond)
        | IObs p =>
          if continue_ cond then
            match lookup p ext with
            | Some v => interp ext inst0 (v :: s) cond
            | None => Err default_error
            end
          else interp ext inst0 s cond
        | IOp op =>
          if continue_ cond then
            match op with
            | Add => match s with
                    | ZVal i :: ZVal j :: s0 => interp ext inst0 (ZVal (i+j) :: s0)%Z cond
                    | _ => Err default_error
                    end
            | Sub => match s with
                      | ZVal i :: ZVal j :: s0 => interp ext inst0 (ZVal (i-j) :: s0)%Z cond
                      | _ => Err default_error
                      end
            | Mult => match s with
                     | ZVal i :: ZVal j :: s0 => interp ext inst0 (ZVal (i*j) :: s0)%Z cond
                     | _ => Err default_error
                            end
            | Le => match s with
                   | ZVal i :: ZVal j :: s0 => interp ext inst0 (BVal (i<=?j) :: s0)%Z cond
                   | _ => Err default_error
                   end
            | Lt => match s with
                   | ZVal i :: ZVal j :: s0 => interp ext inst0 (BVal (i<?j) :: s0)%Z cond
                   | _ => Err default_error
                   end
            | Equal => match s with
                      | ZVal i :: ZVal j :: s0 => interp ext inst0 (BVal (i =? j) :: s0)%Z cond
                      | _ => Err default_error
                     end
            end
          else interp ext inst0 s cond
        end
        end.

  Definition receive (p : params)
                     (s : storage)
                     : result (list action * storage) Error :=
    let s0 := s in (* prevents optimizations from removing unused [s] *)
    match interp p.2 p.1 [] 0 with
    | Ok v => Ok ([],v)
    | Err e => Err e
    end.

End Interpreter.

Module TestInterpreter.
  Import Interpreter.

  (** Input for the interpreter in Liquidity:
      ([IPushZ 0; IObs ("blah",0); IOp Add; IPushZ 1; IOp Equal], (Map [(("blah", 0), (ZVal 1))])) *)
  Example test_interp :
    let env := FMap.of_list [(("blah", 0%Z), (ZVal 1))] in
    interp env [IPushZ 0; IObs ("blah", 0); IOp Add; IPushZ 1; IOp Equal] [] 0 =
    Ok [BVal true].
  Proof. vm_compute. reflexivity. Qed.

  (** Input for the interpreter in Liquidity:
  ([IPushZ 1; IPushZ 1; IOp Equal; IIf; IPushZ 1; IElse; IPushZ (-1); IEndIf], (Map [])) *)
  Example test_interp_if_1 :
    interp FMap.empty [IPushZ 1; IPushZ 1; IOp Equal; IIf; IPushZ 1; IElse; IPushZ (-1); IEndIf] [] 0
    = Ok [ZVal 1].
  Proof. vm_compute. reflexivity. Qed.

  Example test_interp_if_2 :
    interp FMap.empty [IPushZ 1; IPushZ 0; IOp Equal; IIf; IPushZ 1; IElse; IPushZ (-1); IEndIf] [] 0
    = Ok [ZVal (-1)].
  Proof. vm_compute. reflexivity. Qed.

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
    = Ok [ZVal 2].
  Proof. vm_compute. reflexivity. Qed.

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
    = Ok [ZVal (-1)].
  Proof. vm_compute. reflexivity. Qed.

  (* let strike = 50.0
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

  (* ([IObs ("Maturity", 0); IPushZ 90; IOp Equal; IIf; IObs ("Carlsberg",0); IPushZ 50; IOp Lt; IIf; IPushZ 50; IObs ("Carlsberg", 0); IOp Sub; IPushZ 1000; IOp Mult; IElse; IPushZ 0; IEndIf; IElse; IPushZ 0; IEndIf], (Map [(("Carlsberg", 0), (ZVal 100)); (("Maturity", 0), (ZVal 90))])) *)

  (* try-liquidty: estimated fee 0.054191 *)

  Example run_call_option_in_the_money :
    let env := FMap.of_list [(("Carlsberg", 0%Z), (ZVal 100)); (("Maturity", 0%Z), (ZVal 90))] in
    interp env call_option [] 0
    = Ok [ZVal 50000].
  Proof. vm_compute. reflexivity. Qed.

  Example run_call_option_out_the_money :
      let env := FMap.of_list [(("Carlsberg", 0%Z), (ZVal 30)); (("Maturity", 0%Z), (ZVal 90))] in
    interp env call_option [] 0
    = Ok [ZVal 0].
  Proof. vm_compute. reflexivity. Qed.

  (* A bigger test program for running in try-liquidity with arithmetic operations, lookups and some [Ifs] *)

  Definition blah :=
    [IPushZ 100; IPushZ 200; IOp Add;
    IPushZ 200; IOp Add;
    IPushZ 100; IOp Add;
    IPushZ 100; IOp Add;
    IPushZ 200; IOp Add;
    IPushZ 100; IPushZ 200; IOp Add;
    IPushZ 200; IOp Add;
    IPushZ 100; IOp Add;
    IPushZ 100; IOp Add;
    IPushZ 200; IOp Add;
    IPushZ 100; IPushZ 200; IOp Add;
    IPushZ 200; IOp Add;
    IPushZ 100; IOp Add;
    IPushZ 100; IOp Add;
    IPushZ 200; IOp Add;
    IPushZ 100; IOp Add;
    IPushZ 200; IOp Add;
    IPushZ 100; IOp Add;
    IPushZ 100; IOp Add;
    IPushZ 200; IOp Add;
    IPushZ 100; IOp Mult;
    IPushZ 3000; IOp Sub;
    IPushZ 10; IOp Add;
    IPushZ 10; IOp Mult;
    IPushB true; IIf;
    IPushZ 10; IPushZ 10; IOp Equal; IIf;
    IPushZ 10; IPushZ 10; IOp Add;
    IPushZ 10; IOp Add; IElse;
    IPushB true; IEndIf;
    IPushZ 10; IOp Add;
    IPushZ 10; IOp Add;
    IPushZ 10; IOp Add;
    IPushZ 10; IOp Mult;
    IObs ("blah", 0); IOp Add;
    IObs ("blah", 0); IOp Add;
    IObs ("blah", 0); IOp Add;
    IObs ("blah", 0); IOp Add;
    IObs ("blah", 0); IOp Add;
    IObs ("blah", 0); IOp Add;
    IObs ("blah", 0); IOp Add;
    IObs ("blah", 0); IOp Add;
    IObs ("blah", 0); IOp Add; IElse;
    IPushZ 0; IPushZ 0; IPushZ 0; IPushZ 0; IPushZ 0;
    IPushZ 0; IPushZ 0; IPushZ 0; IPushZ 0; IEndIf ].
  (* Just add the global environment (Map [(("blah", 0), (ZVal 0))])) *)
  (* Compute List.length blah. *)

End TestInterpreter.

Definition print_finmap_type (ty_key ty_val : String.string) :=
  parens false (ty_key ++ "," ++ ty_val) ++ " map".
