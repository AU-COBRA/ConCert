From Coq Require Import List.
Import ListNotations.

Fixpoint find_first {A B : Type} (f : A -> option B) (l : list A)
  : option B :=
  match l with
  | hd :: tl => match f hd with
                | Some b => Some b
                | None => find_first f tl
                end
  | [] => None
  end.

Fixpoint map_option {A B : Type} (f : A -> option B) (l : list A)
  : list B :=
  match l with
  | hd :: tl => match f hd with
                  | Some b => b :: map_option f tl
                  | None => map_option f tl
                end
  | [] => []
  end.
