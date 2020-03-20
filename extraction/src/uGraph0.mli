open Bool
open Datatypes
open List0
open MSetWeakList
open Nat0
open PeanoNat
open Specif
open String0
open Universes0
open Config0
open Monad_utils
open WGraph

type __ = Obj.t

module VariableLevel :
 sig
  type t =
  | Level of char list
  | Var of nat

  val eq_dec : t -> t -> bool

  val to_noprop : t -> NoPropLevel.t
 end

module GoodConstraint :
 sig
  type t_ =
  | Coq_gc_le of VariableLevel.t * VariableLevel.t
  | Coq_gc_lt of VariableLevel.t * VariableLevel.t
  | Coq_gc_lt_set of nat
  | Coq_gc_eq_set of nat

  val t__rect :
    (VariableLevel.t -> VariableLevel.t -> 'a1) -> (VariableLevel.t ->
    VariableLevel.t -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1

  val t__rec :
    (VariableLevel.t -> VariableLevel.t -> 'a1) -> (VariableLevel.t ->
    VariableLevel.t -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1

  type t = t_

  val eq_dec : t -> t -> bool
 end

module GoodConstraintSet :
 sig
  module Raw :
   sig
    type elt = GoodConstraint.t_

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val subset : t -> t -> bool

    val equal : t -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val isok : elt list -> bool
   end

  module E :
   sig
    type t = GoodConstraint.t_

    val eq_dec : GoodConstraint.t_ -> GoodConstraint.t_ -> bool
   end

  type elt = GoodConstraint.t_

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool
 end

val coq_GoodConstraintSet_pair :
  GoodConstraintSet.elt -> GoodConstraintSet.elt -> GoodConstraintSet.t

val gc_of_constraint :
  checker_flags -> UnivConstraint.t -> GoodConstraintSet.t option

val add_gc_of_constraint :
  checker_flags -> UnivConstraint.t -> GoodConstraintSet.t option ->
  GoodConstraintSet.t option

val gc_of_constraints :
  checker_flags -> ConstraintSet.t -> GoodConstraintSet.t option

module Coq_wGraph :
 sig
  module VSet :
   sig
    module Raw :
     sig
      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = NoPropLevel.t_

            val compare : NoPropLevel.t_ -> NoPropLevel.t_ -> comparison

            val eq_dec : NoPropLevel.t_ -> NoPropLevel.t_ -> bool
           end

          module TO :
           sig
            type t = NoPropLevel.t_

            val compare : NoPropLevel.t_ -> NoPropLevel.t_ -> comparison

            val eq_dec : NoPropLevel.t_ -> NoPropLevel.t_ -> bool
           end
         end

        val eq_dec : NoPropLevel.t_ -> NoPropLevel.t_ -> bool

        val lt_dec : NoPropLevel.t_ -> NoPropLevel.t_ -> bool

        val eqb : NoPropLevel.t_ -> NoPropLevel.t_ -> bool
       end

      module ML :
       sig
       end

      type elt = NoPropLevel.t_

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : NoPropLevel.t_ -> NoPropLevel.t_ list -> bool

      val add : NoPropLevel.t_ -> NoPropLevel.t_ list -> NoPropLevel.t_ list

      val singleton : elt -> elt list

      val remove : NoPropLevel.t_ -> NoPropLevel.t_ list -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : NoPropLevel.t_ list -> NoPropLevel.t_ list -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> t * t

      val cardinal : t -> nat

      val elements : t -> elt list

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val choose : t -> elt option

      val compare : NoPropLevel.t_ list -> NoPropLevel.t_ list -> comparison

      val inf : NoPropLevel.t_ -> NoPropLevel.t_ list -> bool

      val isok : NoPropLevel.t_ list -> bool

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = NoPropLevel.t_

              val compare : NoPropLevel.t_ -> NoPropLevel.t_ -> comparison

              val eq_dec : NoPropLevel.t_ -> NoPropLevel.t_ -> bool
             end

            module TO :
             sig
              type t = NoPropLevel.t_

              val compare : NoPropLevel.t_ -> NoPropLevel.t_ -> comparison

              val eq_dec : NoPropLevel.t_ -> NoPropLevel.t_ -> bool
             end
           end

          val eq_dec : NoPropLevel.t_ -> NoPropLevel.t_ -> bool

          val lt_dec : NoPropLevel.t_ -> NoPropLevel.t_ -> bool

          val eqb : NoPropLevel.t_ -> NoPropLevel.t_ -> bool
         end
       end
     end

    module E :
     sig
      type t = NoPropLevel.t_

      val compare : NoPropLevel.t_ -> NoPropLevel.t_ -> comparison

      val eq_dec : NoPropLevel.t_ -> NoPropLevel.t_ -> bool
     end

    type elt = NoPropLevel.t_

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> nat

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val eq_dec : t -> t -> bool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option
   end

  module VSetFact :
   sig
    val eqb : NoPropLevel.t_ -> NoPropLevel.t_ -> bool
   end

  module VSetProp :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : NoPropLevel.t_ -> NoPropLevel.t_ -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb : NoPropLevel.t_ -> NoPropLevel.t_ -> bool
     end

    val coq_In_dec : VSet.elt -> VSet.t -> bool

    val of_list : VSet.elt list -> VSet.t

    val to_list : VSet.t -> VSet.elt list

    val fold_rec :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> VSet.t -> (VSet.t -> __ -> 'a2) ->
      (VSet.elt -> 'a1 -> VSet.t -> VSet.t -> __ -> __ -> __ -> 'a2 -> 'a2)
      -> 'a2

    val fold_rec_bis :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> VSet.t -> (VSet.t -> VSet.t -> 'a1
      -> __ -> 'a2 -> 'a2) -> 'a2 -> (VSet.elt -> 'a1 -> VSet.t -> __ -> __
      -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> VSet.t -> 'a2 -> (VSet.elt -> 'a1 ->
      __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> (VSet.t -> VSet.t -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2 -> (VSet.elt -> 'a1 -> VSet.t -> __ -> 'a2 -> 'a2)
      -> VSet.t -> 'a2

    val fold_rel :
      (VSet.elt -> 'a1 -> 'a1) -> (VSet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
      VSet.t -> 'a3 -> (VSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (VSet.t -> __ -> 'a1) -> (VSet.t -> VSet.t -> 'a1 -> VSet.elt -> __ ->
      __ -> 'a1) -> VSet.t -> 'a1

    val set_induction_bis :
      (VSet.t -> VSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VSet.elt -> VSet.t ->
      __ -> 'a1 -> 'a1) -> VSet.t -> 'a1

    val cardinal_inv_2 : VSet.t -> nat -> VSet.elt

    val cardinal_inv_2b : VSet.t -> VSet.elt
   end

  module Edge :
   sig
    type t = (NoPropLevel.t_ * nat) * NoPropLevel.t_

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool

    val eqb : t -> t -> bool
   end

  module EdgeSet :
   sig
    module Raw :
     sig
      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = (NoPropLevel.t_ * nat) * NoPropLevel.t_

            val compare :
              ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
              ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> comparison

            val eq_dec :
              ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
              ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool
           end

          module TO :
           sig
            type t = (NoPropLevel.t_ * nat) * NoPropLevel.t_

            val compare :
              ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
              ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> comparison

            val eq_dec :
              ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
              ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool
           end
         end

        val eq_dec :
          ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
          ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool

        val lt_dec :
          ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
          ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool

        val eqb :
          ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
          ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool
       end

      module ML :
       sig
       end

      type elt = (NoPropLevel.t_ * nat) * NoPropLevel.t_

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem :
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) list -> bool

      val add :
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) list ->
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) list

      val singleton : elt -> elt list

      val remove :
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) list -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset :
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) list ->
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) list -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> t * t

      val cardinal : t -> nat

      val elements : t -> elt list

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val choose : t -> elt option

      val compare :
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) list ->
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) list -> comparison

      val inf :
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) list -> bool

      val isok : ((NoPropLevel.t_ * nat) * NoPropLevel.t_) list -> bool

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = (NoPropLevel.t_ * nat) * NoPropLevel.t_

              val compare :
                ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
                ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> comparison

              val eq_dec :
                ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
                ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool
             end

            module TO :
             sig
              type t = (NoPropLevel.t_ * nat) * NoPropLevel.t_

              val compare :
                ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
                ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> comparison

              val eq_dec :
                ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
                ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool
             end
           end

          val eq_dec :
            ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
            ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool

          val lt_dec :
            ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
            ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool

          val eqb :
            ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
            ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool
         end
       end
     end

    module E :
     sig
      type t = (NoPropLevel.t_ * nat) * NoPropLevel.t_

      val compare :
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> comparison

      val eq_dec :
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool
     end

    type elt = (NoPropLevel.t_ * nat) * NoPropLevel.t_

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> nat

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val eq_dec : t -> t -> bool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option
   end

  module EdgeSetFact :
   sig
    val eqb :
      ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
      ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool
   end

  module EdgeSetProp :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb :
          ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
          ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb :
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) ->
        ((NoPropLevel.t_ * nat) * NoPropLevel.t_) -> bool
     end

    val coq_In_dec : EdgeSet.elt -> EdgeSet.t -> bool

    val of_list : EdgeSet.elt list -> EdgeSet.t

    val to_list : EdgeSet.t -> EdgeSet.elt list

    val fold_rec :
      (EdgeSet.elt -> 'a1 -> 'a1) -> 'a1 -> EdgeSet.t -> (EdgeSet.t -> __ ->
      'a2) -> (EdgeSet.elt -> 'a1 -> EdgeSet.t -> EdgeSet.t -> __ -> __ -> __
      -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (EdgeSet.elt -> 'a1 -> 'a1) -> 'a1 -> EdgeSet.t -> (EdgeSet.t ->
      EdgeSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (EdgeSet.elt -> 'a1 ->
      EdgeSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (EdgeSet.elt -> 'a1 -> 'a1) -> 'a1 -> EdgeSet.t -> 'a2 -> (EdgeSet.elt
      -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (EdgeSet.elt -> 'a1 -> 'a1) -> 'a1 -> (EdgeSet.t -> EdgeSet.t -> 'a1 ->
      __ -> 'a2 -> 'a2) -> 'a2 -> (EdgeSet.elt -> 'a1 -> EdgeSet.t -> __ ->
      'a2 -> 'a2) -> EdgeSet.t -> 'a2

    val fold_rel :
      (EdgeSet.elt -> 'a1 -> 'a1) -> (EdgeSet.elt -> 'a2 -> 'a2) -> 'a1 ->
      'a2 -> EdgeSet.t -> 'a3 -> (EdgeSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
      'a3) -> 'a3

    val set_induction :
      (EdgeSet.t -> __ -> 'a1) -> (EdgeSet.t -> EdgeSet.t -> 'a1 ->
      EdgeSet.elt -> __ -> __ -> 'a1) -> EdgeSet.t -> 'a1

    val set_induction_bis :
      (EdgeSet.t -> EdgeSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (EdgeSet.elt ->
      EdgeSet.t -> __ -> 'a1 -> 'a1) -> EdgeSet.t -> 'a1

    val cardinal_inv_2 : EdgeSet.t -> nat -> EdgeSet.elt

    val cardinal_inv_2b : EdgeSet.t -> EdgeSet.elt
   end

  type t = (VSet.t * EdgeSet.t) * NoPropLevel.t_

  val coq_V : t -> VSet.t

  val coq_E : t -> EdgeSet.t

  val s : t -> NoPropLevel.t_

  val e_source : Edge.t -> NoPropLevel.t_

  val e_target : Edge.t -> NoPropLevel.t_

  val e_weight : Edge.t -> nat

  type labelling = NoPropLevel.t_ -> nat

  val add_node : t -> VSet.elt -> t

  val add_edge : t -> Edge.t -> t

  type coq_Edges = (nat, __) sigT

  type coq_Paths =
  | Coq_paths_refl of NoPropLevel.t_
  | Coq_paths_step of NoPropLevel.t_ * NoPropLevel.t_ * NoPropLevel.t_
     * coq_Edges * coq_Paths

  val coq_Paths_rect :
    t -> (NoPropLevel.t_ -> 'a1) -> (NoPropLevel.t_ -> NoPropLevel.t_ ->
    NoPropLevel.t_ -> coq_Edges -> coq_Paths -> 'a1 -> 'a1) -> NoPropLevel.t_
    -> NoPropLevel.t_ -> coq_Paths -> 'a1

  val coq_Paths_rec :
    t -> (NoPropLevel.t_ -> 'a1) -> (NoPropLevel.t_ -> NoPropLevel.t_ ->
    NoPropLevel.t_ -> coq_Edges -> coq_Paths -> 'a1 -> 'a1) -> NoPropLevel.t_
    -> NoPropLevel.t_ -> coq_Paths -> 'a1

  val weight : t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_Paths -> nat

  val nodes : t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_Paths -> VSet.t

  val concat :
    t -> NoPropLevel.t_ -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_Paths ->
    coq_Paths -> coq_Paths

  val length : t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_Paths -> nat

  type coq_SimplePaths =
  | Coq_spaths_refl of VSet.t * NoPropLevel.t_
  | Coq_spaths_step of VSet.t * VSet.t * NoPropLevel.t_ * NoPropLevel.t_
     * NoPropLevel.t_ * coq_Edges * coq_SimplePaths

  val coq_SimplePaths_rect :
    t -> (VSet.t -> NoPropLevel.t_ -> 'a1) -> (VSet.t -> VSet.t ->
    NoPropLevel.t_ -> NoPropLevel.t_ -> NoPropLevel.t_ -> __ -> coq_Edges ->
    coq_SimplePaths -> 'a1 -> 'a1) -> VSet.t -> NoPropLevel.t_ ->
    NoPropLevel.t_ -> coq_SimplePaths -> 'a1

  val coq_SimplePaths_rec :
    t -> (VSet.t -> NoPropLevel.t_ -> 'a1) -> (VSet.t -> VSet.t ->
    NoPropLevel.t_ -> NoPropLevel.t_ -> NoPropLevel.t_ -> __ -> coq_Edges ->
    coq_SimplePaths -> 'a1 -> 'a1) -> VSet.t -> NoPropLevel.t_ ->
    NoPropLevel.t_ -> coq_SimplePaths -> 'a1

  val to_paths :
    t -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_SimplePaths ->
    coq_Paths

  val sweight :
    t -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_SimplePaths -> nat

  val is_simple : t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_Paths -> bool

  val to_simple :
    t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_Paths -> coq_SimplePaths

  val add_end :
    t -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_SimplePaths ->
    NoPropLevel.t_ -> coq_Edges -> VSet.t -> coq_SimplePaths

  val coq_SimplePaths_sub :
    t -> VSet.t -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ ->
    coq_SimplePaths -> coq_SimplePaths

  val snodes :
    t -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_SimplePaths ->
    VSet.t

  val split :
    t -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_SimplePaths ->
    VSet.elt -> bool -> coq_SimplePaths * coq_SimplePaths

  val split' :
    t -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_SimplePaths ->
    coq_SimplePaths * coq_SimplePaths

  val simplify :
    t -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_Paths ->
    coq_SimplePaths -> VSet.t -> (NoPropLevel.t_, coq_SimplePaths) sigT

  val succs : t -> NoPropLevel.t_ -> (nat * NoPropLevel.t_) list

  val lsp00 : t -> nat -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ -> Nbar.t

  val lsp0 : t -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ -> Nbar.t

  val lsp : t -> NoPropLevel.t_ -> NoPropLevel.t_ -> Nbar.t

  val reduce :
    t -> VSet.t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_SimplePaths ->
    coq_SimplePaths

  val simplify2 :
    t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_Paths -> coq_SimplePaths

  val simplify2' :
    t -> NoPropLevel.t_ -> NoPropLevel.t_ -> coq_Paths -> coq_SimplePaths

  val coq_VSet_Forall_reflect :
    (VSet.elt -> bool) -> (VSet.elt -> reflect) -> VSet.t -> reflect

  val reflect_logically_equiv : bool -> reflect -> reflect

  val is_acyclic : t -> bool

  val spaths_one :
    t -> VSet.t -> VSet.elt -> NoPropLevel.t_ -> nat -> coq_SimplePaths

  val coq_G' : t -> NoPropLevel.t_ -> NoPropLevel.t_ -> nat -> t

  val to_G' :
    t -> NoPropLevel.t_ -> NoPropLevel.t_ -> nat -> NoPropLevel.t_ ->
    NoPropLevel.t_ -> coq_Paths -> coq_Paths

  val from_G' :
    t -> NoPropLevel.t_ -> NoPropLevel.t_ -> nat -> VSet.t -> NoPropLevel.t_
    -> NoPropLevel.t_ -> coq_SimplePaths -> (coq_SimplePaths,
    coq_SimplePaths * coq_SimplePaths) sum

  val sto_G' :
    t -> NoPropLevel.t_ -> NoPropLevel.t_ -> nat -> VSet.t -> NoPropLevel.t_
    -> NoPropLevel.t_ -> coq_SimplePaths -> coq_SimplePaths

  val leqb_vertices : t -> nat -> NoPropLevel.t_ -> VSet.elt -> bool
 end

type universes_graph = Coq_wGraph.t

val init_graph : universes_graph

val no_prop_levels : LevelSet.t -> Coq_wGraph.VSet.t

val gc_of_uctx :
  checker_flags -> ContextSet.t -> (Coq_wGraph.VSet.t * GoodConstraintSet.t)
  option

val edge_of_level : VariableLevel.t -> Coq_wGraph.EdgeSet.elt

val edge_of_constraint : GoodConstraint.t -> Coq_wGraph.EdgeSet.elt

val make_graph : (Coq_wGraph.VSet.t * GoodConstraintSet.t) -> Coq_wGraph.t

val leqb_no_prop_n :
  universes_graph -> nat -> NoPropLevel.t -> NoPropLevel.t -> bool

val leqb_expr_n :
  checker_flags -> universes_graph -> nat -> UnivExpr.t -> UnivExpr.t -> bool

val leqb_expr_univ_n :
  checker_flags -> universes_graph -> nat -> UnivExpr.t -> Universe.t -> bool

val leqb_universe_n :
  checker_flags -> universes_graph -> nat -> Universe.t -> Universe.t -> bool

val check_leqb_universe :
  checker_flags -> universes_graph -> Universe.t -> Universe.t -> bool

val check_eqb_universe :
  checker_flags -> universes_graph -> Universe.t -> Universe.t -> bool

val check_gc_constraint :
  checker_flags -> universes_graph -> GoodConstraint.t -> bool

val check_gc_constraints :
  checker_flags -> universes_graph -> GoodConstraintSet.t -> bool

val check_constraints :
  checker_flags -> universes_graph -> ConstraintSet.t -> bool
