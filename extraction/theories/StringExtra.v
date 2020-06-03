From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import PArith.
From Coq Require Import String.
From Coq Require Import ZArith.

Import ListNotations.
Local Open Scope string.

Definition str_rev (s : string) : string :=
  (fix f s acc :=
     match s with
     | EmptyString => acc
     | String c s => f s (String c acc)
     end) s EmptyString.

Local Open Scope positive.
Definition hex_of_positive (p : positive) : string :=
  (fix f p acc :=
     match p with
     | xH => String "1" acc
     | xH~0 => String "2" acc
     | xH~1 => String "3" acc
     | xH~0~0 => String "4" acc
     | xH~0~1 => String "5" acc
     | xH~1~0 => String "6" acc
     | xH~1~1 => String "7" acc
     | xH~0~0~0 => String "8" acc
     | xH~0~0~1 => String "9" acc
     | xH~0~1~0 => String "a" acc
     | xH~0~1~1 => String "b" acc
     | xH~1~0~0 => String "c" acc
     | xH~1~0~1 => String "d" acc
     | xH~1~1~0 => String "e" acc
     | xH~1~1~1 => String "f" acc
     | p~0~0~0~0 => f p (String "0" acc)
     | p~0~0~0~1 => f p (String "1" acc)
     | p~0~0~1~0 => f p (String "2" acc)
     | p~0~0~1~1 => f p (String "3" acc)
     | p~0~1~0~0 => f p (String "4" acc)
     | p~0~1~0~1 => f p (String "5" acc)
     | p~0~1~1~0 => f p (String "6" acc)
     | p~0~1~1~1 => f p (String "7" acc)
     | p~1~0~0~0 => f p (String "8" acc)
     | p~1~0~0~1 => f p (String "9" acc)
     | p~1~0~1~0 => f p (String "a" acc)
     | p~1~0~1~1 => f p (String "b" acc)
     | p~1~1~0~0 => f p (String "c" acc)
     | p~1~1~0~1 => f p (String "d" acc)
     | p~1~1~1~0 => f p (String "e" acc)
     | p~1~1~1~1 => f p (String "f" acc)
     end) p EmptyString.

Definition hex_of_N (n : N) : string :=
  match n with
  | N0 => "0"
  | Npos p => hex_of_positive p
  end.

Definition hex_of_nat (n : nat) : string :=
  hex_of_N (N.of_nat n).

Definition hex_of_Z (z : Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => hex_of_positive p
  | Zneg p => String "-" (hex_of_positive p)
  end.

Definition Nlog2up_nat (n : N) : nat :=
  match n with
  | N0 => 1
  | Npos p => Pos.size_nat p
  end.

Local Open Scope N.
Definition string_of_N (n : N) : string :=
  (fix f n num acc :=
     let (q, r) := N.div_eucl num 10 in
     let char :=
         match r with
         | 0 => "0"
         | 1 => "1"
         | 2 => "2"
         | 3 => "3"
         | 4 => "4"
         | 5 => "5"
         | 6 => "6"
         | 7 => "7"
         | 8 => "8"
         | 9 => "9"
         | _ => "x" (* unreachable *)
         end%char in
     let acc := String char acc in
     if q =? 0 then
       acc
     else
       match n with
       | 0%nat => "" (* unreachable *)
       | S n => f n q acc
       end) (Nlog2up_nat n) n EmptyString.

Definition string_of_nat (n : nat) : string :=
  string_of_N (N.of_nat n).

Definition string_of_positive (p : positive) : string :=
  string_of_N (Npos p).

Definition string_of_Z (z : Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => string_of_positive p
  | Zneg p => String "-" (string_of_positive p)
  end.

Definition replace_char (orig : ascii) (new : ascii) : string -> string :=
  fix f s :=
    match s with
    | EmptyString => EmptyString
    | String c s => if (c =? orig)%char then
                      String new (f s)
                    else
                      String c (f s)
    end.

Definition remove_char (c : ascii) : string -> string :=
  fix f s :=
    match s with
    | EmptyString => EmptyString
    | String c' s => if (c' =? c)%char then
                       f s
                     else
                       String c' (f s)
    end.

Local Open Scope char.
(* Structurally recursive starts_with with continuation from
   rest of string if it does start with *)
Definition starts_with_cont
         (with_char : ascii) (with_str : string)
         {A}
         (cont : string -> A) (s : string) : option A :=
  (fix f s c ws :=
     match s with
     | EmptyString => None
     | String sc s =>
       if sc =? c then
         match ws with
         | EmptyString => Some (cont s)
         | String wsc ws => f s wsc ws
         end
       else
         None
     end) s with_char with_str.

Definition starts_with (with_str : string) (s : string) : bool :=
  match with_str with
  | EmptyString => true
  | String wc ws => if starts_with_cont wc ws (fun _ => true) s then
                      true
                    else
                      false
  end.

Definition replace (orig : string) (new : string) : string -> string :=
  match orig with
  | EmptyString => fun s => s
  | String origc origs =>
    fix replace s :=
    match starts_with_cont origc origs replace s with
    | Some s => new ++ s
    | None => match s with
              | EmptyString => EmptyString
              | String c s => String c (replace s)
              end
    end
  end.

Fixpoint substring_from (from : nat) (s : string) : string :=
  match from, s with
  | 0%nat, _ => s
  | S n, String _ s => substring_from n s
  | S n, EmptyString => EmptyString
  end.

Fixpoint substring_count (count : nat) (s : string) : string :=
  match count, s with
  | 0%nat, _ => EmptyString
  | S n, String c s => String c (substring_count n s)
  | S n, EmptyString => EmptyString
  end.

Definition str_map (f : ascii -> ascii) : string -> string :=
  fix g s :=
    match s with
    | EmptyString => EmptyString
    | String c s => String c (g s)
    end.

Definition last_index_of (c : ascii) (s : string) : option nat :=
  (fix f (s : string) (index : nat) (result : option nat) :=
     match s with
     | EmptyString => result
     | String c' s =>
       if c' =? c then
         f s (S index) (Some index)
       else
         f s (S index) result
     end) s 0%nat None.

Definition is_letter (c : ascii) : bool :=
  let n := N_of_ascii c in
  (65 (* A *) <=? n) && (n <=? 90 (* Z *)) ||
  (97 (* a *) <=? n) && (n <=? 122 (* z *))%bool%N.

Definition char_to_upper (c : ascii) : ascii :=
  if is_letter c then
    match c with
    | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Ascii b0 b1 b2 b3 b4 false b6 b7
    end
  else
    c.

Definition char_to_lower (c : ascii) : ascii :=
  if is_letter c then
    match c with
    | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Ascii b0 b1 b2 b3 b4 true b6 b7
    end
  else
    c.

Definition to_upper : string -> string :=
  str_map char_to_upper.

Definition to_lower : string -> string :=
  str_map char_to_lower.

Definition capitalize (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s => String (char_to_upper c) s
  end.

Definition uncapitalize (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s => String (char_to_lower c) s
  end.

Definition str_split (on : string) : string -> list string :=
  match on with
  | EmptyString => fun s => [s]
  | String onc ons =>
    (fix split cur s :=
       match starts_with_cont onc ons (split EmptyString) s with
       | Some l => str_rev cur :: l
       | None => match s with
                 | EmptyString => [str_rev cur]
                 | String sc s => split (String sc cur) s
                 end
       end) EmptyString
  end.
