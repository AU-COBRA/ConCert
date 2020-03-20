open Bool
open Compare_dec
open Datatypes
open List0
open MSetFacts
open MSetList
open MSetProperties
open Nat0
open Orders
open PeanoNat
open Specif
open Ssrbool

type __ = Obj.t

module Nbar :
 sig
  type t = nat option

  val max : t -> t -> t

  val add : t -> t -> t

  val le_dec : t -> t -> bool
 end

module WeightedGraph :
 functor (V:UsualOrderedType) ->
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
            type t = V.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> bool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> bool
           end
         end

        val eq_dec : V.t -> V.t -> bool

        val lt_dec : V.t -> V.t -> bool

        val eqb : V.t -> V.t -> bool
       end

      module ML :
       sig
       end

      type elt = V.t

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : V.t -> V.t list -> bool

      val add : V.t -> V.t list -> V.t list

      val singleton : elt -> elt list

      val remove : V.t -> V.t list -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : V.t list -> V.t list -> bool

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

      val compare : V.t list -> V.t list -> comparison

      val inf : V.t -> V.t list -> bool

      val isok : V.t list -> bool

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = V.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> bool
             end

            module TO :
             sig
              type t = OTF.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> bool
             end
           end

          val eq_dec : V.t -> V.t -> bool

          val lt_dec : V.t -> V.t -> bool

          val eqb : V.t -> V.t -> bool
         end
       end
     end

    module E :
     sig
      type t = V.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> bool
     end

    type elt = V.t

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
    val eqb : V.t -> V.t -> bool
   end

  module VSetProp :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : V.t -> V.t -> bool
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
      val eqb : V.t -> V.t -> bool
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
    type t = (V.t * nat) * V.t

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
            type t = (V.t * nat) * V.t

            val compare :
              ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> comparison

            val eq_dec : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool
           end

          module TO :
           sig
            type t = (V.t * nat) * V.t

            val compare :
              ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> comparison

            val eq_dec : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool
           end
         end

        val eq_dec : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool

        val lt_dec : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool

        val eqb : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool
       end

      module ML :
       sig
       end

      type elt = (V.t * nat) * V.t

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) list -> bool

      val add :
        ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) list ->
        ((V.t * nat) * V.t) list

      val singleton : elt -> elt list

      val remove : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) list -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset :
        ((V.t * nat) * V.t) list -> ((V.t * nat) * V.t) list -> bool

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
        ((V.t * nat) * V.t) list -> ((V.t * nat) * V.t) list -> comparison

      val inf : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) list -> bool

      val isok : ((V.t * nat) * V.t) list -> bool

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = (V.t * nat) * V.t

              val compare :
                ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> comparison

              val eq_dec : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool
             end

            module TO :
             sig
              type t = (V.t * nat) * V.t

              val compare :
                ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> comparison

              val eq_dec : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool
             end
           end

          val eq_dec : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool

          val lt_dec : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool

          val eqb : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool
         end
       end
     end

    module E :
     sig
      type t = (V.t * nat) * V.t

      val compare : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> comparison

      val eq_dec : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool
     end

    type elt = (V.t * nat) * V.t

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
    val eqb : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool
   end

  module EdgeSetProp :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool
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
      val eqb : ((V.t * nat) * V.t) -> ((V.t * nat) * V.t) -> bool
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

  type t = (VSet.t * EdgeSet.t) * V.t

  val coq_V : t -> VSet.t

  val coq_E : t -> EdgeSet.t

  val s : t -> V.t

  val e_source : Edge.t -> V.t

  val e_target : Edge.t -> V.t

  val e_weight : Edge.t -> nat

  type labelling = V.t -> nat

  val add_node : t -> VSet.elt -> t

  val add_edge : t -> Edge.t -> t

  type coq_Edges = (nat, __) sigT

  type coq_Paths =
  | Coq_paths_refl of V.t
  | Coq_paths_step of V.t * V.t * V.t * coq_Edges * coq_Paths

  val coq_Paths_rect :
    t -> (V.t -> 'a1) -> (V.t -> V.t -> V.t -> coq_Edges -> coq_Paths -> 'a1
    -> 'a1) -> V.t -> V.t -> coq_Paths -> 'a1

  val coq_Paths_rec :
    t -> (V.t -> 'a1) -> (V.t -> V.t -> V.t -> coq_Edges -> coq_Paths -> 'a1
    -> 'a1) -> V.t -> V.t -> coq_Paths -> 'a1

  val weight : t -> V.t -> V.t -> coq_Paths -> nat

  val nodes : t -> V.t -> V.t -> coq_Paths -> VSet.t

  val concat : t -> V.t -> V.t -> V.t -> coq_Paths -> coq_Paths -> coq_Paths

  val length : t -> V.t -> V.t -> coq_Paths -> nat

  type coq_SimplePaths =
  | Coq_spaths_refl of VSet.t * V.t
  | Coq_spaths_step of VSet.t * VSet.t * V.t * V.t * V.t * coq_Edges
     * coq_SimplePaths

  val coq_SimplePaths_rect :
    t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> VSet.t -> V.t -> V.t -> V.t ->
    __ -> coq_Edges -> coq_SimplePaths -> 'a1 -> 'a1) -> VSet.t -> V.t -> V.t
    -> coq_SimplePaths -> 'a1

  val coq_SimplePaths_rec :
    t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> VSet.t -> V.t -> V.t -> V.t ->
    __ -> coq_Edges -> coq_SimplePaths -> 'a1 -> 'a1) -> VSet.t -> V.t -> V.t
    -> coq_SimplePaths -> 'a1

  val to_paths : t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> coq_Paths

  val sweight : t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> nat

  val is_simple : t -> V.t -> V.t -> coq_Paths -> bool

  val to_simple : t -> V.t -> V.t -> coq_Paths -> coq_SimplePaths

  val add_end :
    t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> V.t -> coq_Edges ->
    VSet.t -> coq_SimplePaths

  val coq_SimplePaths_sub :
    t -> VSet.t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> coq_SimplePaths

  val snodes : t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> VSet.t

  val split :
    t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> VSet.elt -> bool ->
    coq_SimplePaths * coq_SimplePaths

  val split' :
    t -> VSet.t -> V.t -> V.t -> coq_SimplePaths ->
    coq_SimplePaths * coq_SimplePaths

  val simplify :
    t -> VSet.t -> V.t -> V.t -> coq_Paths -> coq_SimplePaths -> VSet.t ->
    (V.t, coq_SimplePaths) sigT

  val succs : t -> V.t -> (nat * V.t) list

  val lsp00 : t -> nat -> VSet.t -> V.t -> V.t -> Nbar.t

  val lsp0 : t -> VSet.t -> V.t -> V.t -> Nbar.t

  val lsp : t -> V.t -> V.t -> Nbar.t

  val reduce : t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> coq_SimplePaths

  val simplify2 : t -> V.t -> V.t -> coq_Paths -> coq_SimplePaths

  val simplify2' : t -> V.t -> V.t -> coq_Paths -> coq_SimplePaths

  val coq_VSet_Forall_reflect :
    (VSet.elt -> bool) -> (VSet.elt -> reflect) -> VSet.t -> reflect

  val reflect_logically_equiv : bool -> reflect -> reflect

  val is_acyclic : t -> bool

  val spaths_one : t -> VSet.t -> VSet.elt -> V.t -> nat -> coq_SimplePaths

  val coq_G' : t -> V.t -> V.t -> nat -> t

  val to_G' : t -> V.t -> V.t -> nat -> V.t -> V.t -> coq_Paths -> coq_Paths

  val from_G' :
    t -> V.t -> V.t -> nat -> VSet.t -> V.t -> V.t -> coq_SimplePaths ->
    (coq_SimplePaths, coq_SimplePaths * coq_SimplePaths) sum

  val sto_G' :
    t -> V.t -> V.t -> nat -> VSet.t -> V.t -> V.t -> coq_SimplePaths ->
    coq_SimplePaths

  val leqb_vertices : t -> nat -> V.t -> VSet.elt -> bool
 end
