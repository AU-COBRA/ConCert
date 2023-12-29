From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Notations.
From Coq Require Import String.
From Coq Require Import ZArith.

Local Open Scope string_scope.

Section StackInterpreter.
  Context {Base : ChainBase}.

  Definition map_key_type := string * Z.

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

  Global Instance op_serializable : Serializable op :=
    Derive Serializable op_rect <Add, Sub, Mult, Lt, Le, Equal>.

  Global Instance instruction_serializable : Serializable instruction :=
    Derive Serializable instruction_rect <IPushZ, IPushB, IObs, IIf, IElse, IEndIf, IOp>.

  Global Instance value_serializable : Serializable value :=
    Derive Serializable value_rect <BVal, ZVal>.

  Definition ext_map := FMap (string * Z) value.
  Definition lookup (k : string * Z) (m : ext_map) := FMap.find k m.

  Definition storage := list value.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Definition init (chain : Chain)
                  (ctx : ContractCallContext)
                  (setup : unit)
                  : result storage Error :=
    Ok [].

  Definition msg := list instruction * ext_map.

  Open Scope Z.
  Definition continue_ (i : Z) := (i =? 0)%Z.
  Definition bool_to_cond (b : bool) : Z :=
    if b then 0 else 1.
  Definition flip (i : Z) : Z :=
    if (i =? 0) then 1 else if (i =? 1) then 0 else i.
  Definition reset_decrement (i : Z) : Z :=
    if (i <=? 1) then 0 else i-1.

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
      | IIf => if cond =? 0 then
                 match s with
                 | BVal b :: s0 => interp ext inst0 s0 (bool_to_cond b)
                 | _ => Err default_error
                 end else interp ext inst0 s (1 + cond)%Z
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

  Definition receive (chain : Chain)
                     (ctx : ContractCallContext)
                     (s : storage)
                     (msg : option msg)
                     : result (storage * list ActionBody) Error :=
    match msg with
    | None => Err default_error
    | Some (insts, ext) =>
      match interp ext insts [] 0 with
      | Ok v => Ok (v, [])
      | Err e => Err e
      end
    end.

  Definition contract : Contract unit msg storage Error :=
    build_contract init receive.

End StackInterpreter.
