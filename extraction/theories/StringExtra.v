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

Example hex_256 : hex_of_positive 256 = "100".
Proof (eq_refl).
Example hex_17 : hex_of_positive 17 = "11".
Proof (eq_refl).

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
         | _ => "000" (* unreachable *)
         end%char in
     let acc := String char acc in
     if q =? 0 then
       acc
     else
       match n with
       | 0%nat => "unreachable"
       | S n => f n q acc
       end) (Nlog2up_nat n) n EmptyString.

Example num_256 : string_of_N 256 = "256".
Proof (eq_refl).
Example num_0 : string_of_N 0 = "0".
Proof (eq_refl).

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
Fixpoint starts_with (with_str : string) (s : string) : bool :=
  match with_str, s with
  | EmptyString, _ => true
  | String c with_str, String c' s =>
    if c =? c' then
      starts_with with_str s
    else
      false
  | _, EmptyString => false
  end.

Definition replace (orig : string) (new : string) : string -> string :=
  match orig with
  | EmptyString => fun s => s
  | String orig_hd orig_tl =>
    fix replace s :=
    match s with
    | EmptyString => EmptyString
    | String hd tl =>
      (* make this structurally recursive *)
      (fix f with_hd with_tl s_hd s_tl {struct s_tl} :=
         if with_hd =? s_hd then
           match with_tl, s_tl with
           | EmptyString, _ =>
             (* found full string, do replacement *)
             new ++ replace s_tl
           | _, EmptyString => (* Ran out of chars *) String hd (replace tl)
           | String with_hd with_tl, String s_hd s_tl => f with_hd with_tl s_hd s_tl
           end
         else
           String hd (replace tl)) orig_hd orig_tl hd tl
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

Definition char_to_upper (c : ascii) : ascii :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Ascii b0 b1 b2 b3 b4 false b6 b7
  end.

Definition char_to_lower (c : ascii) : ascii :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Ascii b0 b1 b2 b3 b4 true b6 b7
  end.

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
