open BasicAst
open BinInt
open BinPos
open Bool
open Datatypes
open List0
open MCCompare
open MCList
open MCString
open MSetList
open MSetProperties
open PeanoNat
open String0

type __ = Obj.t

type valuation = { valuation_mono : (char list -> int);
                   valuation_poly : (nat -> nat) }

type 'a coq_Evaluable = valuation -> 'a -> int

val coq_val : 'a1 coq_Evaluable -> valuation -> 'a1 -> int

module Level :
 sig
  type t_ =
  | Coq_lProp
  | Coq_lSet
  | Level of char list
  | Var of nat

  val t__rect : 'a1 -> 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1

  val t__rec : 'a1 -> 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1

  type t = t_

  val is_small : t -> bool

  val is_prop : t -> bool

  val is_set : t -> bool

  val is_var : t -> bool

  val coq_Evaluable : t coq_Evaluable

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool

  val eqb : t -> t -> bool

  val eqb_spec : t -> t -> reflect
 end

module LevelSet :
 sig
  module E :
   sig
    type t = Level.t_

    val compare : Level.t_ -> Level.t_ -> comparison

    val eq_dec : Level.t_ -> Level.t_ -> bool
   end

  module Raw :
   sig
    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = Level.t_

          val compare : Level.t_ -> Level.t_ -> comparison

          val eq_dec : Level.t_ -> Level.t_ -> bool
         end

        module TO :
         sig
          type t = Level.t_

          val compare : Level.t_ -> Level.t_ -> comparison

          val eq_dec : Level.t_ -> Level.t_ -> bool
         end
       end

      val eq_dec : Level.t_ -> Level.t_ -> bool

      val lt_dec : Level.t_ -> Level.t_ -> bool

      val eqb : Level.t_ -> Level.t_ -> bool
     end

    module ML :
     sig
     end

    type elt = Level.t_

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : Level.t_ -> Level.t_ list -> bool

    val add : Level.t_ -> Level.t_ list -> Level.t_ list

    val singleton : elt -> elt list

    val remove : Level.t_ -> Level.t_ list -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : Level.t_ list -> Level.t_ list -> bool

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

    val compare : Level.t_ list -> Level.t_ list -> comparison

    val inf : Level.t_ -> Level.t_ list -> bool

    val isok : Level.t_ list -> bool

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = Level.t_

            val compare : Level.t_ -> Level.t_ -> comparison

            val eq_dec : Level.t_ -> Level.t_ -> bool
           end

          module TO :
           sig
            type t = Level.t_

            val compare : Level.t_ -> Level.t_ -> comparison

            val eq_dec : Level.t_ -> Level.t_ -> bool
           end
         end

        val eq_dec : Level.t_ -> Level.t_ -> bool

        val lt_dec : Level.t_ -> Level.t_ -> bool

        val eqb : Level.t_ -> Level.t_ -> bool
       end
     end
   end

  type elt = Level.t_

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

module LevelSetProp :
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb : Level.t_ -> Level.t_ -> bool
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
    val eqb : Level.t_ -> Level.t_ -> bool
   end

  val coq_In_dec : LevelSet.elt -> LevelSet.t -> bool

  val of_list : LevelSet.elt list -> LevelSet.t

  val to_list : LevelSet.t -> LevelSet.elt list

  val fold_rec :
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> (LevelSet.t -> __ ->
    'a2) -> (LevelSet.elt -> 'a1 -> LevelSet.t -> LevelSet.t -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> (LevelSet.t ->
    LevelSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelSet.elt -> 'a1 ->
    LevelSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_nodep :
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> 'a2 -> (LevelSet.elt
    -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_weak :
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> (LevelSet.t -> LevelSet.t -> 'a1
    -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelSet.elt -> 'a1 -> LevelSet.t -> __
    -> 'a2 -> 'a2) -> LevelSet.t -> 'a2

  val fold_rel :
    (LevelSet.elt -> 'a1 -> 'a1) -> (LevelSet.elt -> 'a2 -> 'a2) -> 'a1 ->
    'a2 -> LevelSet.t -> 'a3 -> (LevelSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
    'a3) -> 'a3

  val set_induction :
    (LevelSet.t -> __ -> 'a1) -> (LevelSet.t -> LevelSet.t -> 'a1 ->
    LevelSet.elt -> __ -> __ -> 'a1) -> LevelSet.t -> 'a1

  val set_induction_bis :
    (LevelSet.t -> LevelSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (LevelSet.elt ->
    LevelSet.t -> __ -> 'a1 -> 'a1) -> LevelSet.t -> 'a1

  val cardinal_inv_2 : LevelSet.t -> nat -> LevelSet.elt

  val cardinal_inv_2b : LevelSet.t -> LevelSet.elt
 end

val coq_LevelSet_pair : LevelSet.elt -> LevelSet.elt -> LevelSet.t

module NoPropLevel :
 sig
  type t_ =
  | Coq_lSet
  | Level of char list
  | Var of nat

  val t__rect : 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1

  val t__rec : 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1

  type t = t_

  val coq_Level_Evaluable : t coq_Evaluable

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool

  val of_level : Level.t -> t option

  val to_level : t -> Level.t

  val is_small : t -> bool
 end

module UnivExpr :
 sig
  type t_ =
  | Coq_lProp
  | Coq_npe of (NoPropLevel.t * bool)

  val t__rect : 'a1 -> ((NoPropLevel.t * bool) -> 'a1) -> t_ -> 'a1

  val t__rec : 'a1 -> ((NoPropLevel.t * bool) -> 'a1) -> t_ -> 'a1

  type t = t_

  val coq_Evaluable : t coq_Evaluable

  val is_small : t -> bool

  val is_level : t -> bool

  val is_prop : t -> bool

  val get_level : t -> Level.t

  val get_noprop : t -> NoPropLevel.t option

  val make : Level.t -> t

  val prop : t

  val set : t

  val type1 : t

  val from_kernel_repr : (Level.t * bool) -> t

  val to_kernel_repr : t -> Level.t * bool

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module UnivExprSet :
 sig
  module E :
   sig
    type t = UnivExpr.t_

    val compare : UnivExpr.t_ -> UnivExpr.t_ -> comparison

    val eq_dec : UnivExpr.t_ -> UnivExpr.t_ -> bool
   end

  module Raw :
   sig
    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = UnivExpr.t_

          val compare : UnivExpr.t_ -> UnivExpr.t_ -> comparison

          val eq_dec : UnivExpr.t_ -> UnivExpr.t_ -> bool
         end

        module TO :
         sig
          type t = UnivExpr.t_

          val compare : UnivExpr.t_ -> UnivExpr.t_ -> comparison

          val eq_dec : UnivExpr.t_ -> UnivExpr.t_ -> bool
         end
       end

      val eq_dec : UnivExpr.t_ -> UnivExpr.t_ -> bool

      val lt_dec : UnivExpr.t_ -> UnivExpr.t_ -> bool

      val eqb : UnivExpr.t_ -> UnivExpr.t_ -> bool
     end

    module ML :
     sig
     end

    type elt = UnivExpr.t_

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : UnivExpr.t_ -> UnivExpr.t_ list -> bool

    val add : UnivExpr.t_ -> UnivExpr.t_ list -> UnivExpr.t_ list

    val singleton : elt -> elt list

    val remove : UnivExpr.t_ -> UnivExpr.t_ list -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : UnivExpr.t_ list -> UnivExpr.t_ list -> bool

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

    val compare : UnivExpr.t_ list -> UnivExpr.t_ list -> comparison

    val inf : UnivExpr.t_ -> UnivExpr.t_ list -> bool

    val isok : UnivExpr.t_ list -> bool

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = UnivExpr.t_

            val compare : UnivExpr.t_ -> UnivExpr.t_ -> comparison

            val eq_dec : UnivExpr.t_ -> UnivExpr.t_ -> bool
           end

          module TO :
           sig
            type t = UnivExpr.t_

            val compare : UnivExpr.t_ -> UnivExpr.t_ -> comparison

            val eq_dec : UnivExpr.t_ -> UnivExpr.t_ -> bool
           end
         end

        val eq_dec : UnivExpr.t_ -> UnivExpr.t_ -> bool

        val lt_dec : UnivExpr.t_ -> UnivExpr.t_ -> bool

        val eqb : UnivExpr.t_ -> UnivExpr.t_ -> bool
       end
     end
   end

  type elt = UnivExpr.t_

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

module Universe :
 sig
  type t =
    UnivExprSet.t
    (* singleton inductive, whose constructor was Build_t *)

  val t_set : t -> UnivExprSet.t

  val eqb : t -> t -> bool

  val make' : UnivExpr.t -> t

  val make : Level.t -> t

  val add : UnivExpr.t -> t -> t

  val add_list : UnivExpr.t list -> t -> t

  val is_small : t -> bool

  val is_prop : t -> bool

  val type1 : t

  val super : Level.t -> t

  val exprs : t -> UnivExpr.t * UnivExpr.t list

  val map : (UnivExpr.t -> UnivExpr.t) -> t -> t

  val try_suc : t -> t

  val sup : t -> t -> t

  val sort_of_product : t -> t -> t

  val get_is_level : t -> Level.t option
 end

type sort_family =
| InProp
| InSet
| InType

val leb_sort_family : sort_family -> sort_family -> bool

val universe_family : Universe.t -> sort_family

module ConstraintType :
 sig
  type t_ =
  | Lt
  | Le
  | Eq

  val t__rect : 'a1 -> 'a1 -> 'a1 -> t_ -> 'a1

  val t__rec : 'a1 -> 'a1 -> 'a1 -> t_ -> 'a1

  type t = t_

  val compare : t -> t -> comparison
 end

module UnivConstraint :
 sig
  type t = (Level.t * ConstraintType.t) * Level.t

  val make : Level.t -> ConstraintType.t -> Level.t -> t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module ConstraintSet :
 sig
  module E :
   sig
    type t = (Level.t * ConstraintType.t) * Level.t

    val compare :
      ((Level.t * ConstraintType.t) * Level.t) ->
      ((Level.t * ConstraintType.t) * Level.t) -> comparison

    val eq_dec :
      ((Level.t * ConstraintType.t) * Level.t) ->
      ((Level.t * ConstraintType.t) * Level.t) -> bool
   end

  module Raw :
   sig
    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = (Level.t * ConstraintType.t) * Level.t

          val compare :
            ((Level.t * ConstraintType.t) * Level.t) ->
            ((Level.t * ConstraintType.t) * Level.t) -> comparison

          val eq_dec :
            ((Level.t * ConstraintType.t) * Level.t) ->
            ((Level.t * ConstraintType.t) * Level.t) -> bool
         end

        module TO :
         sig
          type t = (Level.t * ConstraintType.t) * Level.t

          val compare :
            ((Level.t * ConstraintType.t) * Level.t) ->
            ((Level.t * ConstraintType.t) * Level.t) -> comparison

          val eq_dec :
            ((Level.t * ConstraintType.t) * Level.t) ->
            ((Level.t * ConstraintType.t) * Level.t) -> bool
         end
       end

      val eq_dec :
        ((Level.t * ConstraintType.t) * Level.t) ->
        ((Level.t * ConstraintType.t) * Level.t) -> bool

      val lt_dec :
        ((Level.t * ConstraintType.t) * Level.t) ->
        ((Level.t * ConstraintType.t) * Level.t) -> bool

      val eqb :
        ((Level.t * ConstraintType.t) * Level.t) ->
        ((Level.t * ConstraintType.t) * Level.t) -> bool
     end

    module ML :
     sig
     end

    type elt = (Level.t * ConstraintType.t) * Level.t

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem :
      ((Level.t * ConstraintType.t) * Level.t) ->
      ((Level.t * ConstraintType.t) * Level.t) list -> bool

    val add :
      ((Level.t * ConstraintType.t) * Level.t) ->
      ((Level.t * ConstraintType.t) * Level.t) list ->
      ((Level.t * ConstraintType.t) * Level.t) list

    val singleton : elt -> elt list

    val remove :
      ((Level.t * ConstraintType.t) * Level.t) ->
      ((Level.t * ConstraintType.t) * Level.t) list -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset :
      ((Level.t * ConstraintType.t) * Level.t) list ->
      ((Level.t * ConstraintType.t) * Level.t) list -> bool

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
      ((Level.t * ConstraintType.t) * Level.t) list ->
      ((Level.t * ConstraintType.t) * Level.t) list -> comparison

    val inf :
      ((Level.t * ConstraintType.t) * Level.t) ->
      ((Level.t * ConstraintType.t) * Level.t) list -> bool

    val isok : ((Level.t * ConstraintType.t) * Level.t) list -> bool

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = (Level.t * ConstraintType.t) * Level.t

            val compare :
              ((Level.t * ConstraintType.t) * Level.t) ->
              ((Level.t * ConstraintType.t) * Level.t) -> comparison

            val eq_dec :
              ((Level.t * ConstraintType.t) * Level.t) ->
              ((Level.t * ConstraintType.t) * Level.t) -> bool
           end

          module TO :
           sig
            type t = (Level.t * ConstraintType.t) * Level.t

            val compare :
              ((Level.t * ConstraintType.t) * Level.t) ->
              ((Level.t * ConstraintType.t) * Level.t) -> comparison

            val eq_dec :
              ((Level.t * ConstraintType.t) * Level.t) ->
              ((Level.t * ConstraintType.t) * Level.t) -> bool
           end
         end

        val eq_dec :
          ((Level.t * ConstraintType.t) * Level.t) ->
          ((Level.t * ConstraintType.t) * Level.t) -> bool

        val lt_dec :
          ((Level.t * ConstraintType.t) * Level.t) ->
          ((Level.t * ConstraintType.t) * Level.t) -> bool

        val eqb :
          ((Level.t * ConstraintType.t) * Level.t) ->
          ((Level.t * ConstraintType.t) * Level.t) -> bool
       end
     end
   end

  type elt = (Level.t * ConstraintType.t) * Level.t

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

module Instance :
 sig
  type t = Level.t list
 end

module UContext :
 sig
  type t = Instance.t * ConstraintSet.t
 end

module AUContext :
 sig
  type t = name list * ConstraintSet.t

  val repr : t -> UContext.t

  val levels : t -> LevelSet.t
 end

module ContextSet :
 sig
  type t = LevelSet.t * ConstraintSet.t

  val empty : t
 end

module Variance :
 sig
  type t =
  | Irrelevant
  | Covariant
  | Invariant
 end

type universes_decl =
| Monomorphic_ctx of ContextSet.t
| Polymorphic_ctx of AUContext.t

val monomorphic_udecl : universes_decl -> ContextSet.t

val levels_of_udecl : universes_decl -> LevelSet.t

val constraints_of_udecl : universes_decl -> ConstraintSet.t

type 'a coq_UnivSubst = Instance.t -> 'a -> 'a

val subst_instance_level : Level.t coq_UnivSubst

val subst_instance_cstr : UnivConstraint.t coq_UnivSubst

val subst_instance_cstrs : ConstraintSet.t coq_UnivSubst

val subst_instance_level_expr : UnivExpr.t coq_UnivSubst

val subst_instance_univ : Universe.t coq_UnivSubst

val subst_instance_instance : Instance.t coq_UnivSubst

val closedu_level : nat -> Level.t -> bool

val closedu_level_expr : nat -> UnivExpr.t -> bool

val closedu_universe : nat -> Universe.t -> bool

val closedu_instance : nat -> Instance.t -> bool

val string_of_level : Level.t -> char list

val string_of_level_expr : UnivExpr.t -> char list

val string_of_sort : Universe.t -> char list

val string_of_universe_instance : Level.t list -> char list

val print_universe_instance : Level.t list -> char list

val print_lset : LevelSet.t -> char list

val print_constraint_type : ConstraintType.t_ -> char list

val print_constraint_set : ConstraintSet.t -> char list
