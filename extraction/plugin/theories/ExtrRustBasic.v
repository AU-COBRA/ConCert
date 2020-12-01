From Coq Require Import Extraction.

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive option => "Option" ["Some" "None"].
Extract Inductive unit => "()" ["()"].
Extract Inductive prod => "__pair" ["__mk_pair"] "__pair_elim!".
Extract Inlined Constant andb => "__andb!".
Extract Inlined Constant orb => "__orb!".
