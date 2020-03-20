open Basics
open Datatypes
open List0
open MSetInterface
open Orders
open OrdersFacts
open OrdersLists

module MakeRaw :
 functor (X:OrderedType) ->
 sig
  module MX :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = X.t

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

    val eq_dec : X.t -> X.t -> bool

    val lt_dec : X.t -> X.t -> bool

    val eqb : X.t -> X.t -> bool
   end

  module ML :
   sig
   end

  type elt = X.t

  type t = elt list

  val empty : t

  val is_empty : t -> bool

  val mem : X.t -> X.t list -> bool

  val add : X.t -> X.t list -> X.t list

  val singleton : elt -> elt list

  val remove : X.t -> X.t list -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : X.t list -> X.t list -> bool

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

  val compare : X.t list -> X.t list -> comparison

  val inf : X.t -> X.t list -> bool

  val isok : X.t list -> bool

  module L :
   sig
    module MO :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

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

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end
   end
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module Raw :
   sig
    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

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

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end

    module ML :
     sig
     end

    type elt = X.t

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : X.t -> X.t list -> bool

    val add : X.t -> X.t list -> X.t list

    val singleton : elt -> elt list

    val remove : X.t -> X.t list -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : X.t list -> X.t list -> bool

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

    val compare : X.t list -> X.t list -> comparison

    val inf : X.t -> X.t list -> bool

    val isok : X.t list -> bool

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

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

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end
     end
   end

  module E :
   sig
    type t = X.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  type elt = X.t

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

module type OrderedTypeWithLeibniz =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module MakeWithLeibniz :
 functor (X:OrderedTypeWithLeibniz) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  module Raw :
   sig
    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

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

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end

    module ML :
     sig
     end

    type elt = X.t

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : X.t -> X.t list -> bool

    val add : X.t -> X.t list -> X.t list

    val singleton : elt -> elt list

    val remove : X.t -> X.t list -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : X.t list -> X.t list -> bool

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

    val compare : X.t list -> X.t list -> comparison

    val inf : X.t -> X.t list -> bool

    val isok : X.t list -> bool

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

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

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end
     end
   end

  type elt = X.t

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
