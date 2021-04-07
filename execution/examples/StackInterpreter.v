From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.

From Coq Require Import Ascii.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import Notations.
From Coq Require Import PeanoNat.
From Coq Require Import String.
From Coq Require Import ZArith.

Local Open Scope string_scope.

Import ListNotations.

Section StackInterpreter.
  Context {Base: ChainBase}.

  Definition map_key_type := string * Z.

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

  Global Instance op_serializable : Serializable op :=
    Derive Serializable op_rect <Add, Sub, Mult, Lt, Le, Equal>.

  Global Instance instruction_serializable : Serializable instruction :=
    Derive Serializable instruction_rect <IPushZ, IPushB, IObs, IIf, IElse, IEndIf, IOp>.

  Global Instance value_serializable : Serializable value :=
    Derive Serializable value_rect <BVal, ZVal>.

  Definition ext_map := FMap (string * Z) value.
  Definition lookup (k : string * Z) (m : ext_map) := FMap.find k m.

  Definition storage := list value.

  Definition init
             (chain : Chain)
             (ctx : ContractCallContext)
             (setup : unit) : option storage :=
    Some [].

  Definition msg := list instruction * ext_map.

  Open Scope Z.
  Definition continue_ (i : Z) := (i =? 0)%Z.
  Definition bool_to_cond (b : bool) : Z :=
    if b then 0 else 1.
  Definition flip (i : Z) : Z :=
    if (i =? 0) then 1 else if (i =? 1) then 0 else i.
  Definition reset_decrement (i : Z) : Z :=
    if (i <=? 1) then 0 else i-1.

  Fixpoint interp (ext : ext_map) (insts : list instruction) (s : list value) (cond : Z) :=
    match insts with
    | [] => Some s
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
                 | _ => None
                 end else interp ext inst0 s (1 + cond)%Z
      | IElse => interp ext inst0 s (flip cond)
      | IEndIf => interp ext inst0 s (reset_decrement cond)
      | IObs p =>
        if continue_ cond then
          match lookup p ext with
          | Some v => interp ext inst0 (v :: s) cond
          | None => None
          end
        else interp ext inst0 s cond
      | IOp op =>
        if continue_ cond then
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

  Definition receive
             (chain : Chain)
             (ctx : ContractCallContext)
             (s : storage)
             (msg : option msg) : option (storage * list ActionBody) :=
    match msg with
    | None => None
    | Some (insts, ext) =>
      match interp ext insts [] 0 with
      | Some v => Some (v, [])
      | None => None
      end
    end.

  Definition contract : Contract unit msg storage :=
    build_contract init receive.
End StackInterpreter.
