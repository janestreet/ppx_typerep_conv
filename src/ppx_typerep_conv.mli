(** Pa_type_rep: Preprocessing Module for automatic type representation *)
open Parsetree

module Field_case : sig
  type t =
    { label        : string
    ; ctyp         : core_type
    ; index        : int
    ; mutable_flag : Asttypes.mutable_flag
    }
end

module Variant_case : sig
  type t =
    { label       : string
    ; ctyp        : core_type option
    ; poly        : bool
    ; arity       : int
    ; index       : int
    ; arity_index : int
    }

  (** expr and patt for the constructor *)
  val expr       : loc:Location.t -> t -> expression option -> expression
  val patt       : loc:Location.t -> t -> pattern    option -> pattern
  val ocaml_repr : loc:Location.t -> t -> expression
end

module Branches : sig
  val fields       : label_declaration       list -> Field_case.t   list
  val row_fields   : row_field               list -> Variant_case.t list
  val constructors : constructor_declaration list -> Variant_case.t list
end
