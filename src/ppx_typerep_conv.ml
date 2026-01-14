open Base
open Ppxlib
open Ast_builder.Default

let ( @@ ) a b = a b

module Gen = struct
  let let_in loc list_lid_expr body =
    List.fold_right list_lid_expr ~init:body ~f:(fun (lid, expr) body ->
      [%expr
        let [%p pvar ~loc lid] = [%e expr] in
        [%e body]])
  ;;
end

module Field_case = struct
  type t =
    { label : string
    ; ctyp : core_type
    ; index : int
    ; mutable_flag : Asttypes.mutable_flag
    }
end

module Element_case = struct
  type t =
    { label : string option
    ; ctyp : core_type
    ; index : int
    }
end

module Variant_case = struct
  module Args = struct
    type t =
      | Inline_record of (string * core_type) list
      | Tupled of core_type list

    let ctys = function
      | Inline_record args -> List.map args ~f:(fun (_, cty) -> cty)
      | Tupled args -> args
    ;;
  end

  type t =
    { label : string
    ; args : Args.t
    ; args_loc : Location.t
    ; poly : bool
    ; arity : int
    ; index : int
    ; arity_index : int
    }

  let patt ~loc t arg =
    let label = t.label in
    if t.poly
    then ppat_variant ~loc label arg
    else ppat_construct ~loc (Located.lident ~loc label) arg
  ;;

  let expr ~loc t arg =
    let label = t.label in
    if t.poly
    then pexp_variant ~loc label arg
    else pexp_construct ~loc (Located.lident ~loc label) arg
  ;;

  let ocaml_repr ~loc { label; poly; arity_index; _ } =
    if poly
    then
      [%expr
        Typerep_lib.Std.Typerep_obj.repr_of_poly_variant [%e pexp_variant ~loc label None]]
    else eint ~loc arity_index
  ;;
end

module Branches = struct
  let fields fields =
    let mapi index ld : Field_case.t =
      { label = ld.pld_name.txt
      ; ctyp = ld.pld_type
      ; index
      ; mutable_flag = ld.pld_mutable
      }
    in
    List.mapi fields ~f:mapi
  ;;

  let row_fields rfs =
    (*= duplicates like [ `A | `B | `A ] cause warnings in the generated code (duplicated
       patterns), so we don't have to deal with them. *)
    let no_arg =
      let r = ref (-1) in
      fun () ->
        r := !r + 1;
        !r
    in
    let with_arg =
      let r = ref (-1) in
      fun () ->
        r := !r + 1;
        !r
    in
    let mapi index rf : Variant_case.t =
      match rf.prf_desc with
      | Rtag ({ txt = label; _ }, true, _) | Rtag ({ txt = label; _ }, _, []) ->
        { label
        ; args = Tupled []
        ; args_loc = rf.prf_loc
        ; poly = true
        ; arity = 0
        ; index
        ; arity_index = no_arg ()
        }
      | Rtag ({ txt = label; _ }, false, ctyp :: _) ->
        { label
        ; args = Tupled [ ctyp ]
        ; args_loc = rf.prf_loc
        ; poly = true
        ; arity = 1
        ; index
        ; arity_index = with_arg ()
        }
      | Rinherit ty ->
        Location.raise_errorf ~loc:ty.ptyp_loc "ppx_typerep_conv: unknown type"
    in
    List.mapi rfs ~f:mapi
  ;;

  let constructors cds =
    let no_arg =
      let r = ref (-1) in
      fun () ->
        r := !r + 1;
        !r
    in
    let with_arg =
      let r = ref (-1) in
      fun () ->
        r := !r + 1;
        !r
    in
    let mapi index cd : Variant_case.t =
      if Option.is_some cd.pcd_res
      then Location.raise_errorf ~loc:cd.pcd_loc "ppx_typerep_conv: GADTs not supported";
      let label = cd.pcd_name.txt in
      match cd.pcd_args with
      | Pcstr_tuple [] ->
        { label
        ; args = Tupled []
        ; args_loc = cd.pcd_loc
        ; poly = false
        ; arity = 0
        ; index
        ; arity_index = no_arg ()
        }
      | Pcstr_tuple args ->
        let args = List.map args ~f:Ppxlib_jane.Shim.Pcstr_tuple_arg.to_core_type in
        let arity = List.length args in
        { label
        ; args = Tupled args
        ; args_loc = cd.pcd_loc
        ; poly = false
        ; arity
        ; index
        ; arity_index = with_arg ()
        }
      | Pcstr_record labels ->
        let args =
          List.map labels ~f:(fun { pld_type; pld_name; _ } ->
            let label = pld_name.txt in
            let cty = pld_type in
            label, cty)
        in
        let arity = List.length args in
        { label
        ; args = Inline_record args
        ; args_loc = cd.pcd_loc
        ; poly = false
        ; arity
        ; index
        ; arity_index = with_arg ()
        }
    in
    List.mapi cds ~f:mapi
  ;;
end

module Typerep_signature = struct
  let remove_jkinds td =
    let params_without_jkinds =
      List.map td.ptype_params ~f:(fun (ty, variance) ->
        let ty_without_jkind =
          match Ppxlib_jane.Shim.Core_type_desc.of_parsetree ty.ptyp_desc with
          | Ptyp_var (name, _jkind) ->
            { ty with
              ptyp_desc =
                Ppxlib_jane.Shim.Core_type_desc.to_parsetree (Ptyp_var (name, None))
            }
          | _ -> ty
        in
        ty_without_jkind, variance)
    in
    { td with ptype_params = params_without_jkinds }
  ;;

  let sig_of_typerep_of_t td =
    let arg_type ~loc ty = [%type: [%t ty] Typerep_lib.Std.Typerep.t] in
    Ppx_helpers.combinator_type_of_type_declaration td ~f:arg_type
    |> Ppx_helpers.Polytype.to_core_type
         ~universally_quantify_only_if_jkind_annotation:true
  ;;

  let sig_of_typename_of_t td =
    let arg_type ~loc ty = [%type: [%t ty] Typerep_lib.Std.Typename.t] in
    Ppx_helpers.combinator_type_of_type_declaration td ~f:arg_type
    |> Ppx_helpers.Polytype.to_core_type
         ~universally_quantify_only_if_jkind_annotation:true
  ;;

  let sig_of_one_def td ~polymorphic =
    let td = if not polymorphic then remove_jkinds td else td in
    let typerep_of = sig_of_typerep_of_t td in
    let typename_of = sig_of_typename_of_t td in
    let loc = td.ptype_loc in
    let psig_value ~name ~type_ =
      psig_value
        ~loc
        (Ppxlib_jane.Ast_builder.Default.value_description
           ~loc
           ~name
           ~type_
           ~modalities:(Ppxlib_jane.Shim.Modalities.portable ~loc)
           ~prim:[])
    in
    let type_name = Ppx_helpers.mangle_unboxed td.ptype_name.txt in
    [ psig_value ~name:(Located.mk ~loc ("typerep_of_" ^ type_name)) ~type_:typerep_of
    ; psig_value ~name:(Located.mk ~loc ("typename_of_" ^ type_name)) ~type_:typename_of
    ]
  ;;

  let sig_generator ~loc ~path:_ ~polymorphic (_rec_flag, tds) =
    match
      mk_named_sig
        ~loc
        ~sg_name:"Typerep_lib.Typerepable.S"
        ~handle_polymorphic_variant:true
        tds
    with
    | Some include_infos ->
      [ Ppxlib_jane.Ast_builder.Default.psig_include ~loc ~modalities:[] include_infos ]
    | None -> List.concat_map tds ~f:(sig_of_one_def ~polymorphic)
  ;;

  let gen =
    Deriving.Generator.make
      Deriving.Args.(empty +> arg "named" Ast_pattern.(ebool __) +> flag "unboxed")
      (fun ~loc ~path (rf, tds) named unboxed ->
        let named = Option.value ~default:true named in
        let tds = Ppx_helpers.with_implicit_unboxed_records ~loc ~unboxed tds in
        sig_generator ~loc ~path ~polymorphic:(not named) (rf, tds))
  ;;
end

module Typerep_implementation = struct
  module Util : sig
    type param = string loc * Ppxlib_jane.jkind_annotation option

    val typename_field : loc:Location.t -> type_name:string option -> expression
    val arg_of_param : param -> string

    (* Extracts useful data from a list of parameters as core types.

       The [param list] returned is [~params], passed to other utility functions. The
       [string] returned is the [~typename_functor] which is one from the
       [Typerep_lib.Std.Make_typename.Make] (used when [~named]) or
       [Typerep_lib.Typename.Make] (used when not [~named]) families. The suffix indicates
       the number of type parameters and, through template mangling, their jkinds.

       Once we have jkind polymorphism, we should be able to remove template mangling from
       the functors. *)
    val parse_params
      :  ptype_params:(core_type * (variance * injectivity)) list
      -> named:bool
      -> param list * string

    val params_patts : loc:Location.t -> params:param list -> pattern list

    val type_name_module_definition
      :  loc:Location.t
      -> path:string
      -> type_name:string
      -> params:param list
      -> typename_functor:string
      -> structure

    val with_named
      :  loc:Location.t
      -> type_name:string
      -> params:param list
      -> expression
      -> expression

    val typerep_of_t : type_declaration -> params:param list -> core_type

    val typerep_abstract
      :  loc:Location.t
      -> path:string
      -> type_name:string
      -> params:param list
      -> structure_item

    module Record : sig
      val field_n_ident : fields:Field_case.t list -> int -> string

      val fields
        :  loc:Location.t
        -> typerep_of_type:(core_type -> expression)
        -> unboxed:bool
        -> fields:Field_case.t list
        -> (int * string * expression) list

      val create
        :  loc:Location.t
        -> unboxed:bool
        -> fields:Field_case.t list
        -> expression

      val has_double_array_tag
        :  loc:Location.t
        -> typerep_of_type:(core_type -> expression)
        -> fields:Field_case.t list
        -> expression
    end

    module Tuple_l : sig
      val element_n_ident : elements:Element_case.t list -> int -> string

      val elements
        :  loc:Location.t
        -> typerep_of_type:(core_type -> expression)
        -> elements:Element_case.t list
        -> (int * string option * expression) list

      val create : loc:Location.t -> elements:Element_case.t list -> expression
    end

    module Variant : sig
      val tag_n_ident : variants:Variant_case.t list -> int -> string

      val tags
        :  loc:Location.t
        -> typerep_of_type:(core_type -> expression)
        -> variants:Variant_case.t list
        -> (int * expression) list

      val value : loc:Location.t -> variants:Variant_case.t list -> expression
      val polymorphic : loc:Location.t -> variants:Variant_case.t list -> expression
    end
  end = struct
    let make_field_expr base field_name ~loc ~unboxed =
      if unboxed
      then Ppxlib_jane.Ast_builder.Default.pexp_unboxed_field base field_name ~loc
      else pexp_field base field_name ~loc
    ;;

    let make_record_expr fields base ~loc ~unboxed =
      if unboxed
      then Ppxlib_jane.Ast_builder.Default.pexp_record_unboxed_product fields base ~loc
      else pexp_record fields base ~loc
    ;;

    type param = string loc * Ppxlib_jane.jkind_annotation option

    let str_item_type_and_name ~loc ~path ~params ~type_name =
      let ptype_params =
        List.map params ~f:(fun (name, jkind) ->
          ( Ppxlib_jane.Ast_builder.Default.Latest.ptyp_var ~loc name.txt jkind
          , (NoVariance, NoInjectivity) ))
      in
      let td =
        let manifest =
          ptyp_constr
            ~loc
            (Located.lident ~loc type_name)
            (List.map params ~f:(fun (name, _) -> ptyp_var name.txt ~loc))
        in
        type_declaration
          ~loc
          ~name:(Located.mk ~loc "t")
          ~params:ptype_params
          ~manifest:(Some manifest)
          ~kind:Ptype_abstract
          ~cstrs:[]
          ~private_:Public
      in
      let name_def =
        let type_name = Ppx_helpers.mangle_unboxed type_name in
        let full_type_name = Printf.sprintf "%s.%s" path type_name in
        [%stri let name = [%e estring ~loc full_type_name]]
      in
      pmod_structure ~loc [ pstr_type ~loc Nonrecursive [ td ]; name_def ]
    ;;

    let arg_of_param (name, _) = "_of_" ^ name.txt
    let name_of_t ~type_name = "name_of_" ^ Ppx_helpers.mangle_unboxed type_name

    let typename_field ~loc ~type_name =
      match type_name with
      | None -> [%expr Typerep_lib.Std.Typename.create ()]
      | Some type_name ->
        [%expr
          Typerep_lib.Std.Typerep.Named.typename_of_t
            [%e evar ~loc @@ name_of_t ~type_name]]
    ;;

    let parse_params ~ptype_params ~named =
      let params = List.map ptype_params ~f:Ppxlib_jane.get_type_param_name_and_jkind in
      let remove_jkinds params = List.map params ~f:(fun (name, _jkind) -> name, None) in
      let arity_string = Int.to_string (List.length params) in
      if named
      then (
        let typename_functor = "Typerep_lib.Std.Make_typename.Make" ^ arity_string in
        remove_jkinds params, typename_functor)
      else (
        let typename_functor =
          String.concat
            ~sep:"__"
            (("Typerep_lib.Typename.Make" ^ arity_string)
             :: List.map params ~f:(function
               | _, Some { pjkind_desc = Pjk_abbreviation kind; _ } -> kind
               | _, None -> "value"
               | _, Some { pjkind_loc = loc; _ } ->
                 Location.raise_errorf
                   ~loc
                   "ppx_typerep: don't know how to mangle this kind compatibly with \
                    ppx_template"))
        in
        params, typename_functor)
    ;;

    let params_patts ~loc ~params =
      List.map params ~f:(fun s -> pvar ~loc @@ arg_of_param s)
    ;;

    let type_name_module_name ~type_name =
      "Typename_of_" ^ Ppx_helpers.mangle_unboxed type_name
    ;;

    let with_named ~loc ~type_name ~params expr =
      let name_t =
        eapply
          ~loc
          (pexp_ident ~loc
           @@ Located.lident ~loc
           @@ type_name_module_name ~type_name
           ^ ".named")
          (List.map params ~f:(fun name -> evar ~loc @@ arg_of_param name))
      in
      let name_of_t = name_of_t ~type_name in
      let args =
        [%expr
          [%e evar ~loc name_of_t]
          , First (Typerep_lib.For_ppx.Portable_lazy.from_fun (fun () -> [%e expr]))]
      in
      [%expr
        let [%p pvar ~loc name_of_t] = [%e name_t] in
        Typerep_lib.Std.Typerep.Named [%e args]]
    ;;

    let typerep_of_t td ~params =
      combinator_type_of_type_declaration td ~f:(fun ~loc ty ->
        [%type: [%t ty] Typerep_lib.Std.Typerep.t])
      |> Ppxlib_jane.Ast_builder.Default.ptyp_poly ~loc:td.ptype_loc params
    ;;

    let type_name_module_definition ~loc ~path ~type_name ~params ~typename_functor =
      let name = type_name_module_name ~type_name in
      let make = pmod_ident ~loc @@ Located.lident ~loc @@ typename_functor in
      let type_name_struct = str_item_type_and_name ~loc ~path ~params ~type_name in
      let type_name_module = pmod_apply ~loc make type_name_struct in
      let module_def =
        pstr_module ~loc
        @@ module_binding ~loc ~name:(Located.mk ~loc (Some name)) ~expr:type_name_module
      in
      let typename_of_t =
        let lid = "typename_of_" ^ Ppx_helpers.mangle_unboxed type_name in
        pstr_value
          ~loc
          Nonrecursive
          [ value_binding
              ~loc
              ~pat:(pvar ~loc lid)
              ~expr:(evar ~loc (name ^ ".typename_of_t"))
          ]
      in
      [ module_def; typename_of_t ]
    ;;

    let typerep_abstract ~loc ~path ~type_name ~params =
      let type_name_struct = str_item_type_and_name ~loc ~path ~params ~type_name in
      let type_arity = List.length params in
      let make =
        pmod_ident ~loc
        @@ Located.lident ~loc
        @@ "Typerep_lib.Std.Type_abstract.Make"
        ^ Int.to_string type_arity
      in
      pstr_include ~loc @@ include_infos ~loc @@ pmod_apply ~loc make type_name_struct
    ;;

    let field_or_tag_n_ident prefix ~list n =
      if n < 0 || n > List.length list then assert false;
      prefix ^ Int.to_string n
    ;;

    module Tuple_l = struct
      (* element_0, element_1, etc. *)
      let element_n_ident ~elements:list = field_or_tag_n_ident "element" ~list
      let element_eval_n_ident ~elements:list = field_or_tag_n_ident "el" ~list

      let elements ~loc ~typerep_of_type ~elements =
        let map { Element_case.ctyp; label; index } =
          let rep = typerep_of_type ctyp in
          let tuple_pat =
            Ppxlib_jane.Ast_builder.Default.ppat_tuple
              ~loc
              (List.mapi
                 ~f:(fun i { Element_case.label; _ } ->
                   label, if i = index then pvar ~loc "v" else ppat_any ~loc)
                 elements)
              Closed
          in
          let lab_as_exp =
            match label with
            | None -> [%expr None]
            | Some name -> [%expr Some [%e estring ~loc name]]
          in
          let get = [%expr fun [%p tuple_pat] () -> v] in
          let idx = eint ~loc index in
          ( index
          , label
          , [%expr
              Typerep_lib.Std.Typerep.Element.internal_use_only
                { Typerep_lib.Std.Typerep.Element_internal.label = [%e lab_as_exp]
                ; index = [%e idx]
                ; rep = [%e rep]
                ; tyid =
                    Typerep_lib.Std.Typename.Tuple_l.Internal_use_only.Boxed
                    .typename_of_index
                      typename
                      [%e idx]
                ; get = [%e get]
                }] )
        in
        List.map ~f:map elements
      ;;

      let create ~loc ~elements =
        let elements_rep =
          List.mapi elements ~f:(fun i { Element_case.label; index; _ } ->
            assert (i = index);
            label, evar ~loc @@ element_eval_n_ident ~elements index)
        in
        let tuple = Ppxlib_jane.Ast_builder.Default.pexp_tuple ~loc elements_rep in
        let vbs =
          List.mapi elements ~f:(fun i { index; _ } ->
            assert (i = index);
            let pat = pvar ~loc @@ element_eval_n_ident ~elements index in
            let expr =
              [%expr (get [%e evar ~loc @@ element_n_ident ~elements index]) ()]
            in
            value_binding ~loc ~pat ~expr)
        in
        [%expr
          fun ({ Typerep_lib.Std.Typerep.Tuple_l_internal.get } @ local) ->
            [%e pexp_let ~loc Nonrecursive vbs tuple]]
      ;;
    end

    module Record = struct
      let field_n_ident ~fields:list = field_or_tag_n_ident "field" ~list

      let fields ~loc ~typerep_of_type ~unboxed ~fields =
        let map { Field_case.ctyp; label; index; mutable_flag; _ } =
          let rep = typerep_of_type ctyp in
          let is_mutable =
            match mutable_flag with
            | Mutable -> true
            | Immutable -> false
          in
          let get =
            [%expr
              fun t () ->
                [%e make_field_expr ~unboxed ~loc [%expr t] (Located.lident ~loc label)]]
          in
          ( index
          , label
          , [%expr
              Typerep_lib.Std.Typerep.Field.internal_use_only
                { Typerep_lib.Std.Typerep.Field_internal.label = [%e estring ~loc label]
                ; index = [%e eint ~loc index]
                ; is_mutable = [%e ebool ~loc is_mutable]
                ; rep = [%e rep]
                ; tyid = Typerep_lib.Std.Typename.create ()
                ; get = [%e get]
                }] )
        in
        List.map ~f:map fields
      ;;

      let has_double_array_tag ~loc ~typerep_of_type ~fields =
        (* For [type t = { x : int; y : string }], this generates code that roughly looks
           like:
           {[
             match double_array_value typerep_of_int, double_array_value typerep_of_string with
             | Some x, Some y -> Typerep_obj.has_double_array_tag { x = x (); y = y () }
             | _ -> false
           ]}
        *)
        let field_thunk_option_exprs, field_thunk_some_pats, fields_binding =
          let map { Field_case.ctyp; label; _ } =
            (* The value must be a float else this segfaults. This is tested by the unit
               tests in case this property changes. *)
            let rep = typerep_of_type ctyp in
            let field_thunk_name = gen_symbol ~prefix:label () in
            ( [%expr Typerep_lib.Std.Typerep_obj.double_array_value [%e rep]]
            , [%pat? Some [%p pvar ~loc field_thunk_name]]
            , (Located.lident ~loc label, [%expr [%e evar ~loc field_thunk_name] ()]) )
          in
          List.unzip3 (List.map ~f:map fields)
        in
        [%expr
          Typerep_lib.For_ppx.Portable_lazy.from_fun (fun () ->
            match [%e pexp_tuple ~loc field_thunk_option_exprs] with
            | [%p ppat_tuple ~loc field_thunk_some_pats] ->
              Typerep_lib.Std.Typerep_obj.has_double_array_tag
                [%e pexp_record ~loc fields_binding None]
            | _ -> false)]
      ;;

      let create ~loc ~unboxed ~fields =
        let record =
          (* Calling [get] on the fields from left to right matters, so that iteration
             goes left to right too. *)
          let fields_binding =
            let map { Field_case.label; _ } =
              Located.lident ~loc label, evar ~loc label
            in
            List.map ~f:map fields
          in
          let record =
            [%expr
              let record = [%e make_record_expr ~unboxed ~loc fields_binding None] in
              fun () -> record]
          in
          let vbs =
            List.mapi fields ~f:(fun i { Field_case.index; label; _ } ->
              assert (i = index);
              let pat = pvar ~loc label in
              let expr = [%expr (get [%e evar ~loc @@ field_n_ident ~fields index]) ()] in
              value_binding ~loc ~pat ~expr)
          in
          pexp_let ~loc Nonrecursive vbs record
        in
        [%expr
          fun ({ Typerep_lib.Std.Typerep.Record_internal.get } @ local) -> [%e record]]
      ;;
    end

    module Variant = struct
      (* tag_0, tag_1, etc. *)
      let tag_n_ident ~variants:list = field_or_tag_n_ident "tag" ~list

      let polymorphic ~loc ~variants =
        let polymorphic =
          match variants with
          | [] -> true
          | hd :: _ -> hd.Variant_case.poly
        in
        [%expr [%e ebool ~loc polymorphic]]
      ;;

      let tags ~loc ~typerep_of_type ~variants =
        let create ({ Variant_case.arity; args; _ } as variant) =
          if arity = 0
          then
            [%expr
              Typerep_lib.Std.Typerep.Tag_internal.Const
                (fun () -> [%e Variant_case.expr ~loc variant None])]
          else (
            let arg_tuple i = "v" ^ Int.to_string i in
            let patt =
              if arity = 1
              then pvar ~loc @@ arg_tuple 0
              else (
                let f i = None, pvar ~loc @@ arg_tuple i in
                Ppxlib_jane.Ast_builder.Default.ppat_unboxed_tuple
                  ~loc
                  (List.init arity ~f)
                  Closed)
            in
            let expr =
              let f i = evar ~loc @@ arg_tuple i in
              let args =
                match args with
                | Tupled args -> pexp_tuple ~loc (List.mapi args ~f:(fun i _ -> f i))
                | Inline_record args ->
                  pexp_record
                    ~loc
                    (List.mapi args ~f:(fun i (label, _) ->
                       Located.lident ~loc label, f i))
                    None
              in
              Variant_case.expr ~loc variant (Some args)
            in
            [%expr
              Typerep_lib.Std.Typerep.Tag_internal.Args
                (fun f ->
                  let [%p patt] = f () in
                  [%e expr])])
        in
        let mapi
          index'
          ({ Variant_case.args; args_loc; label; arity; index; _ } as variant)
          =
          if index <> index' then assert false;
          let rep, tyid =
            match args with
            | Tupled [] -> [%expr typerep_of_tuple0], [%expr typename_of_tuple0]
            | Tupled [ cty ] | Inline_record [ (_, cty) ] ->
              typerep_of_type cty, [%expr Typerep_lib.Std.Typename.create ()]
            | (Tupled (_ :: _ :: _) | Inline_record _) as args ->
              let ctys =
                List.map (Variant_case.Args.ctys args) ~f:(fun cty -> None, cty)
              in
              ( typerep_of_type
                  (Ppxlib_jane.Ast_builder.Default.ptyp_unboxed_tuple ctys ~loc:args_loc)
              , [%expr Typerep_lib.Std.Typename.create ()] )
          in
          let args_labels =
            match args with
            | Tupled _ -> []
            | Inline_record args ->
              List.map args ~f:(fun (label, _) -> estring ~loc label)
          in
          let body =
            [%expr
              Typerep_lib.Std.Typerep.Tag.internal_use_only
                { Typerep_lib.Std.Typerep.Tag_internal.label = [%e estring ~loc label]
                ; rep = [%e rep]
                ; arity = [%e eint ~loc arity]
                ; args_labels = [%e elist ~loc args_labels]
                ; index = [%e eint ~loc index]
                ; ocaml_repr = [%e Variant_case.ocaml_repr ~loc variant]
                ; tyid = [%e tyid]
                ; create = [%e create variant]
                }]
          in
          index, body
        in
        List.mapi ~f:mapi variants
      ;;

      let value ~loc ~variants =
        let match_cases =
          let arg_tuple i = "v" ^ Int.to_string i in
          let mapi index' ({ Variant_case.arity; index; args; _ } as variant) =
            if index <> index' then assert false;
            let patt, value =
              if arity = 0
              then Variant_case.patt ~loc variant None, [%expr value_tuple0]
              else (
                let patt =
                  let f i = pvar ~loc @@ arg_tuple i in
                  let args =
                    match args with
                    | Tupled _ -> ppat_tuple ~loc (List.init arity ~f)
                    | Inline_record args ->
                      ppat_record
                        ~loc
                        (List.mapi args ~f:(fun i (label, _) ->
                           Located.lident ~loc label, f i))
                        Closed
                  in
                  Variant_case.patt ~loc variant (Some args)
                in
                let expr =
                  let ctys = Variant_case.Args.ctys args in
                  if arity = 1
                  then evar ~loc @@ arg_tuple 0
                  else
                    Ppxlib_jane.Ast_builder.Default.pexp_unboxed_tuple
                      ~loc
                      (List.mapi ctys ~f:(fun i _ -> None, evar ~loc @@ arg_tuple i))
                in
                patt, expr)
            in
            let tag = evar ~loc @@ tag_n_ident ~variants index in
            let prod =
              [%expr
                Typerep_lib.Std.Typerep.Variant_internal.Value
                  ([%e tag], fun () -> [%e value])]
            in
            case ~guard:None ~lhs:patt ~rhs:prod
          in
          List.mapi ~f:mapi variants
        in
        pexp_function ~loc match_cases
      ;;
    end
  end

  let typerep_of_labeled_tuple loc ~typerep_of_type ~recur tuple =
    let typerep_of_type ty = typerep_of_type ty ~recur in
    let elements =
      List.mapi ~f:(fun index (label, ctyp) -> { Element_case.index; label; ctyp }) tuple
    in
    let element_ident i = Util.Tuple_l.element_n_ident ~elements i in
    let indexed_elements = Util.Tuple_l.elements ~loc ~typerep_of_type ~elements in
    let elements_iarray =
      let elements =
        List.map
          ~f:(fun (index, _, _) ->
            [%expr
              Typerep_lib.Std.Typerep.Tuple_l_internal.Element
                [%e evar ~loc @@ element_ident index]])
          indexed_elements
      in
      [%expr
        Typerep_lib.For_ppx.Iarray.unsafe_of_array__promise_no_mutation
          [%e pexp_array ~loc elements]]
    in
    let typename =
      let elements =
        List.map elements ~f:(fun { label; ctyp; _ } ->
          let label =
            match label with
            | None -> [%expr None]
            | Some label -> [%expr Some [%e estring ~loc label]]
          in
          [%expr
            T ([%e label], Typerep_lib.Std.Typerep.typename_of_t [%e typerep_of_type ctyp])])
      in
      [%expr
        Typerep_lib.Std.Typename.Tuple_l.Internal_use_only.Boxed.typename_of_t
          [%e elist ~loc elements]]
    in
    let bindings =
      [ "elements", elements_iarray; "create", Util.Tuple_l.create ~loc ~elements ]
    in
    let elements_binding =
      let map (name, _) =
        ( Located.lident ~loc ("Typerep_lib.Std.Typerep.Tuple_l_internal." ^ name)
        , evar ~loc name )
      in
      List.map ~f:map (("typename", typename) :: bindings)
    in
    let tuple =
      let elements =
        [%expr
          Typerep_lib.Std.Typerep.Tuple_l.internal_use_only
            [%e pexp_record ~loc elements_binding None]]
      in
      [%expr Typerep_lib.Std.Typerep.Tuple_l [%e elements]]
    in
    let tuple = Gen.let_in loc bindings tuple in
    let tuple =
      List.fold_right
        indexed_elements
        ~f:(fun (index, _, expr) acc ->
          [%expr
            let [%p pvar ~loc @@ element_ident index] = [%e expr] in
            [%e acc]])
        ~init:tuple
    in
    let tuple =
      [%expr
        let typename = [%e typename] in
        [%e tuple]]
    in
    tuple
  ;;

  let typerep_of_labeled_tuple_u loc ~typerep_of_type ~recur tuple =
    let typerep_of_type ty = typerep_of_type ty ~recur in
    let arity = List.length tuple in
    if arity < 2 || arity > 5
    then
      Location.raise_errorf
        ~loc
        "ppx_typerep: labeled unboxed tuples of arity %d are not supported (only 2-5)"
        arity;
    let elements =
      List.mapi ~f:(fun index (label, ctyp) -> Element_case.{ index; label; ctyp }) tuple
    in
    (* Create element_info array *)
    let elements_array =
      let elements =
        List.map
          ~f:(fun Element_case.{ label; index; _ } ->
            [%expr
              { Typerep_lib.Std.Typerep.Tuple_l_u_internal.label =
                  [%e
                    match label with
                    | None -> [%expr None]
                    | Some name -> [%expr Some [%e estring ~loc name]]]
              ; index = [%e eint ~loc index]
              }])
          elements
      in
      [%expr
        Typerep_lib.For_ppx.Iarray.unsafe_of_array__promise_no_mutation
          [%e pexp_array ~loc elements]]
    in
    (* Generate pattern with underscores for unused variables *)
    let make_tuple_pat_for_getter labels target_index =
      Ppxlib_jane.Ast_builder.Default.ppat_unboxed_tuple
        ~loc
        (List.mapi
           ~f:(fun i label ->
             let var_name =
               if i = target_index then "v" ^ Int.to_string i else "_v" ^ Int.to_string i
             in
             label, pvar ~loc var_name)
           labels)
        Closed
    in
    let labels = List.map ~f:(fun s -> s.Element_case.label) elements in
    let typereps = List.map ~f:(fun s -> typerep_of_type s.Element_case.ctyp) elements in
    let typename =
      let elements =
        List.map elements ~f:(fun { label; ctyp; _ } ->
          let label =
            match label with
            | None -> [%expr None]
            | Some label -> [%expr Some [%e estring ~loc label]]
          in
          [%expr
            Typerep_lib.Std.Typename.Tuple_l.Internal_use_only.Unboxed.Element.T
              ([%e label], Typerep_lib.Std.Typerep.typename_of_t [%e typerep_of_type ctyp])])
      in
      let arg = pexp_tuple ~loc elements in
      let elements =
        match arity with
        | 2 ->
          [%expr Typerep_lib.Std.Typename.Tuple_l.Internal_use_only.Unboxed.T2 [%e arg]]
        | 3 ->
          [%expr Typerep_lib.Std.Typename.Tuple_l.Internal_use_only.Unboxed.T3 [%e arg]]
        | 4 ->
          [%expr Typerep_lib.Std.Typename.Tuple_l.Internal_use_only.Unboxed.T4 [%e arg]]
        | 5 ->
          [%expr Typerep_lib.Std.Typename.Tuple_l.Internal_use_only.Unboxed.T5 [%e arg]]
        | _ -> assert false (* Already checked above *)
      in
      [%expr
        Typerep_lib.Std.Typename.Tuple_l.Internal_use_only.Unboxed.typename_of_t
          [%e elements]]
    in
    let constructor =
      match typereps with
      | [ t1; t2 ] ->
        [%expr
          Typerep_lib.Std.Typerep.Tuple_l_u_internal.T2
            { fields = [%e elements_array]
            ; t1 = [%e t1]
            ; t2 = [%e t2]
            ; get1 = (fun [%p make_tuple_pat_for_getter labels 0] -> v0)
            ; get2 = (fun [%p make_tuple_pat_for_getter labels 1] -> v1)
            ; typename = [%e typename]
            }]
      | [ t1; t2; t3 ] ->
        [%expr
          Typerep_lib.Std.Typerep.Tuple_l_u_internal.T3
            { fields = [%e elements_array]
            ; t1 = [%e t1]
            ; t2 = [%e t2]
            ; t3 = [%e t3]
            ; get1 = (fun [%p make_tuple_pat_for_getter labels 0] -> v0)
            ; get2 = (fun [%p make_tuple_pat_for_getter labels 1] -> v1)
            ; get3 = (fun [%p make_tuple_pat_for_getter labels 2] -> v2)
            ; typename = [%e typename]
            }]
      | [ t1; t2; t3; t4 ] ->
        [%expr
          Typerep_lib.Std.Typerep.Tuple_l_u_internal.T4
            { fields = [%e elements_array]
            ; t1 = [%e t1]
            ; t2 = [%e t2]
            ; t3 = [%e t3]
            ; t4 = [%e t4]
            ; get1 = (fun [%p make_tuple_pat_for_getter labels 0] -> v0)
            ; get2 = (fun [%p make_tuple_pat_for_getter labels 1] -> v1)
            ; get3 = (fun [%p make_tuple_pat_for_getter labels 2] -> v2)
            ; get4 = (fun [%p make_tuple_pat_for_getter labels 3] -> v3)
            ; typename = [%e typename]
            }]
      | [ t1; t2; t3; t4; t5 ] ->
        [%expr
          Typerep_lib.Std.Typerep.Tuple_l_u_internal.T5
            { fields = [%e elements_array]
            ; t1 = [%e t1]
            ; t2 = [%e t2]
            ; t3 = [%e t3]
            ; t4 = [%e t4]
            ; t5 = [%e t5]
            ; get1 = (fun [%p make_tuple_pat_for_getter labels 0] -> v0)
            ; get2 = (fun [%p make_tuple_pat_for_getter labels 1] -> v1)
            ; get3 = (fun [%p make_tuple_pat_for_getter labels 2] -> v2)
            ; get4 = (fun [%p make_tuple_pat_for_getter labels 3] -> v3)
            ; get5 = (fun [%p make_tuple_pat_for_getter labels 4] -> v4)
            ; typename = [%e typename]
            }]
      | _ -> assert false (* Already checked above *)
    in
    [%expr
      Typerep_lib.Std.Typerep.Tuple_l_u
        (Typerep_lib.Std.Typerep.Tuple_l_u.internal_use_only [%e constructor])]
  ;;

  let rec typerep_of_type ty ~recur =
    let loc = { ty.ptyp_loc with loc_ghost = true } in
    match Ppxlib_jane.Shim.Core_type_desc.of_parsetree ty.ptyp_desc with
    | Ptyp_constr (id, params) ->
      let recursive =
        match id.txt with
        | Lident type_name -> recur ~type_name
        | _ -> None
      in
      let make_expr =
        match recursive with
        | Some make -> make
        | None ->
          type_constr_conv ~loc id ~f:(fun tn ->
            "typerep_of_" ^ Ppx_helpers.mangle_unboxed tn)
      in
      make_expr (List.map params ~f:(typerep_of_type ~recur))
    | Ptyp_var (name, jkind) -> evar ~loc @@ Util.arg_of_param ({ txt = name; loc }, jkind)
    | Ptyp_variant (row_fields, _, _) ->
      typerep_of_variant loc ~recur ~type_name:None (Branches.row_fields row_fields)
    | Ptyp_tuple labeled_typs ->
      (match Ppxlib_jane.as_unlabeled_tuple labeled_typs with
       | Some typs -> typerep_of_tuple loc typs ~recur
       | None -> typerep_of_labeled_tuple loc ~typerep_of_type ~recur labeled_typs)
    | Ptyp_unboxed_tuple labeled_typs ->
      (match Ppxlib_jane.as_unlabeled_tuple labeled_typs with
       | Some typs -> typerep_of_tuple_u loc typs ~recur
       | None -> typerep_of_labeled_tuple_u loc ~typerep_of_type ~recur labeled_typs)
    | _ -> Location.raise_errorf ~loc "ppx_typerep: unknown type"

  and typerep_of_tuple loc tuple ~recur =
    let typereps = List.map tuple ~f:(typerep_of_type ~recur) in
    let typerep_of_tuple =
      let len = List.length typereps in
      if len < 2 || len > 5
      then
        Location.raise_errorf
          ~loc
          "ppx_type_conv: unsupported tuple arity %d. must be in {2,3,4,5}"
          len
      else evar ~loc @@ "typerep_of_tuple" ^ Int.to_string len
    in
    eapply ~loc typerep_of_tuple typereps

  and typerep_of_tuple_u loc tuple ~recur =
    let typereps = List.map tuple ~f:(typerep_of_type ~recur) in
    let typerep_of_tuple_u =
      let len = List.length typereps in
      if len < 2 || len > 5
      then
        Location.raise_errorf
          ~loc
          "ppx_type_conv: unsupported unboxed tuple arity %d. must be in {2,3,4,5}"
          len
      else evar ~loc @@ Printf.sprintf "typerep_of_tuple%d_u" len
    in
    eapply ~loc typerep_of_tuple_u typereps

  and typerep_of_record loc ~recur ~type_name ~unboxed lds =
    let typerep_of_type = typerep_of_type ~recur in
    let fields = Branches.fields lds in
    let field_ident i = Util.Record.field_n_ident ~fields i in
    let indexed_fields = Util.Record.fields ~loc ~typerep_of_type ~unboxed ~fields in
    let fields_iarray =
      let fields =
        List.map
          ~f:(fun (index, _, _) ->
            [%expr
              Typerep_lib.Std.Typerep.Record_internal.Field
                [%e evar ~loc @@ field_ident index]])
          indexed_fields
      in
      [%expr
        Typerep_lib.For_ppx.Iarray.unsafe_of_array__promise_no_mutation
          [%e pexp_array ~loc fields]]
    in
    let bindings =
      [ "typename", Util.typename_field ~loc ~type_name:(Some type_name)
      ; ( "has_double_array_tag"
        , if unboxed
          then [%expr Typerep_lib.For_ppx.Portable_lazy.from_val false]
          else Util.Record.has_double_array_tag ~loc ~typerep_of_type ~fields )
      ; "fields", fields_iarray
      ; "create", Util.Record.create ~loc ~unboxed ~fields
      ]
    in
    let fields_binding =
      let map (name, _) =
        ( Located.lident ~loc ("Typerep_lib.Std.Typerep.Record_internal." ^ name)
        , evar ~loc name )
      in
      List.map ~f:map bindings
    in
    let record =
      let fields =
        [%expr
          Typerep_lib.Std.Typerep.Record.internal_use_only
            [%e pexp_record ~loc fields_binding None]]
      in
      if unboxed
      then [%expr Typerep_lib.Std.Typerep.Record_u [%e fields]]
      else [%expr Typerep_lib.Std.Typerep.Record [%e fields]]
    in
    let record = Gen.let_in loc bindings record in
    let record =
      List.fold_right
        indexed_fields
        ~f:(fun (index, _, expr) acc ->
          [%expr
            let [%p pvar ~loc @@ field_ident index] = [%e expr] in
            [%e acc]])
        ~init:record
    in
    record

  and typerep_of_variant loc ~recur ~type_name variants =
    let typerep_of_type = typerep_of_type ~recur in
    let tags = Util.Variant.tags ~loc ~typerep_of_type ~variants in
    let tag_ident i = Util.Variant.tag_n_ident ~variants i in
    let tags_iarray =
      let tags =
        List.map
          ~f:(fun (index, _) ->
            [%expr
              Typerep_lib.Std.Typerep.Variant_internal.Tag
                [%e evar ~loc @@ tag_ident index]])
          tags
      in
      [%expr
        Typerep_lib.For_ppx.Iarray.unsafe_of_array__promise_no_mutation
          [%e pexp_array ~loc tags]]
    in
    let bindings =
      [ "typename", Util.typename_field ~loc ~type_name
      ; "tags", tags_iarray
      ; "polymorphic", Util.Variant.polymorphic ~loc ~variants
      ; "value", Util.Variant.value ~loc ~variants
      ]
    in
    let tags_binding =
      let map (name, _) =
        ( Located.lident ~loc ("Typerep_lib.Std.Typerep.Variant_internal." ^ name)
        , evar ~loc name )
      in
      List.map ~f:map bindings
    in
    let variant =
      let tags =
        [%expr
          Typerep_lib.Std.Typerep.Variant.internal_use_only
            [%e pexp_record ~loc tags_binding None]]
      in
      [%expr Typerep_lib.Std.Typerep.Variant [%e tags]]
    in
    let variant = Gen.let_in loc bindings variant in
    let variant =
      List.fold_right
        tags
        ~f:(fun (index, expr) acc ->
          [%expr
            let [%p pvar ~loc @@ tag_ident index] = [%e expr] in
            [%e acc]])
        ~init:variant
    in
    variant
  ;;

  module Impl = struct
    type t =
      { body : expression
      ; core_type : core_type
      ; loc : Location.t
      ; type_name : string
      ; value_name : string
      ; prelude : structure_item list
      }
  end

  let impl_of_one_def ~path ~recur ~named td : Impl.t =
    let loc = td.ptype_loc in
    let type_name = td.ptype_name.txt in
    let body =
      match Ppxlib_jane.Shim.Type_kind.of_parsetree td.ptype_kind with
      | Ptype_variant cds ->
        typerep_of_variant
          loc
          ~recur
          ~type_name:(Some type_name)
          (Branches.constructors cds)
      | Ptype_record lds -> typerep_of_record loc ~recur ~type_name ~unboxed:false lds
      | Ptype_record_unboxed_product lds ->
        typerep_of_record loc ~recur ~type_name ~unboxed:true lds
      | Ptype_open ->
        Location.raise_errorf ~loc "ppx_typerep_conv: open types are not supported"
      | Ptype_abstract ->
        (match td.ptype_manifest with
         | None ->
           Location.raise_errorf
             ~loc
             "typerep cannot be applied on abstract types, except like 'type t \
              [@@@@deriving typerep ~abstract]'"
         | Some ty ->
           (match ty.ptyp_desc with
            | Ptyp_variant (row_fields, _, _) ->
              typerep_of_variant
                loc
                ~recur
                ~type_name:(Some type_name)
                (Branches.row_fields row_fields)
            | _ -> typerep_of_type ty ~recur))
    in
    let params, typename_functor =
      Util.parse_params ~named ~ptype_params:td.ptype_params
    in
    let params_patts = Util.params_patts ~loc ~params in
    let body = if named then Util.with_named ~loc ~type_name ~params body else body in
    let arguments =
      List.map2_exn params params_patts ~f:(fun (name, _) patt ->
        (* Add type annotations to parameters, at least to avoid the unused type warning. *)
        let loc = patt.ppat_loc in
        [%pat?
          ([%p patt] :
            [%t ptyp_constr ~loc (Located.lident ~loc name.txt) []]
              Typerep_lib.Std.Typerep.t)])
    in
    let body = eabstract ~loc arguments body in
    let body =
      List.fold_right params ~init:body ~f:(fun (name, jkind) acc ->
        Ppxlib_jane.Ast_builder.Default.pexp_newtype
          ~loc
          { txt = name.txt; loc }
          jkind
          acc)
    in
    let value_name = "typerep_of_" ^ Ppx_helpers.mangle_unboxed type_name in
    let core_type = Util.typerep_of_t td ~params in
    let prelude =
      Util.type_name_module_definition ~loc ~path ~type_name ~params ~typename_functor
    in
    { body; core_type; loc; prelude; type_name; value_name }
  ;;

  module List = struct
    include List

    (* to avoid gensym diffs with camlp4 *)
    let map_right_to_left xs ~f = rev xs |> map ~f |> rev
  end

  let with_typrep_nonrecursive tds ~loc ~path ~named =
    let impls =
      List.map_right_to_left tds ~f:(fun td ->
        impl_of_one_def td ~path ~recur:(fun ~type_name:_ -> None) ~named)
    in
    let bindings =
      List.map
        impls
        ~f:(fun { body; core_type; loc; type_name = _; value_name; prelude = _ } ->
          let pat =
            let var = pvar ~loc value_name in
            match core_type.ptyp_desc with
            | Ptyp_poly _ -> ppat_constraint ~loc var core_type
            | _ -> var
          in
          value_binding ~loc ~pat ~expr:body)
    in
    List.concat_map impls ~f:(fun impl -> impl.prelude)
    @ [ pstr_value ~loc Nonrecursive bindings ]
  ;;

  let with_typrep_recursive tds ~loc ~path ~named =
    let fixpoint_name = gen_symbol ~prefix:"fixpoint" () in
    let get_field_name_exn =
      let map =
        List.map tds ~f:(fun td ->
          let type_name = td.ptype_name.txt in
          type_name, gen_symbol ~prefix:(Ppx_helpers.mangle_unboxed type_name) ())
        |> Map.of_alist_exn (module String)
      in
      fun ~type_name -> Map.find_exn map type_name
    in
    let recur =
      let map =
        List.map tds ~f:(fun td ->
          let fn args =
            let loc = td.ptype_loc in
            let typerep =
              pexp_field
                ~loc
                [%expr
                  Typerep_lib.For_ppx.Portable_lazy.force [%e evar ~loc fixpoint_name]]
                (Loc.make
                   ~loc:td.ptype_name.loc
                   (Lident (get_field_name_exn ~type_name:td.ptype_name.txt)))
            in
            eapply ~loc typerep args
          in
          td.ptype_name.txt, fn)
        |> Map.of_alist_exn (module String)
      in
      fun ~type_name -> Map.find map type_name
    in
    let impls = List.map_right_to_left tds ~f:(impl_of_one_def ~path ~recur ~named) in
    let record_fields =
      List.map impls ~f:(fun { loc; core_type; type_name; _ } ->
        label_declaration
          ~loc
          ~name:(Loc.make ~loc (get_field_name_exn ~type_name))
          ~mutable_:Immutable
          ~type_:core_type)
    in
    let record_type_decl =
      type_declaration
        ~loc
        ~name:(Loc.make ~loc (gen_symbol ~prefix:"_tie_the_knot" ()))
        ~params:[]
        ~cstrs:[]
        ~kind:(Ptype_record record_fields)
        ~private_:Public
        ~manifest:None
    in
    let fixpoint_expr =
      let fields =
        List.map impls ~f:(fun { loc; body; type_name; _ } ->
          Loc.make ~loc (Lident (get_field_name_exn ~type_name)), body)
      in
      [%expr
        Typerep_lib.For_ppx.Portable_lazy.from_fun_fixed
          (fun [%p pvar ~loc fixpoint_name] -> [%e pexp_record ~loc fields None])]
    in
    let open_defns =
      [ pstr_type ~loc Nonrecursive [ record_type_decl ]
      ; [ value_binding ~loc ~pat:(pvar ~loc fixpoint_name) ~expr:fixpoint_expr ]
        |> pstr_value ~loc Nonrecursive
      ]
    in
    let incl_defns =
      List.map impls ~f:(fun { loc; core_type; type_name; value_name; _ } ->
        let pat = pvar ~loc value_name
        and expr =
          let vars =
            match core_type.ptyp_desc with
            | Ptyp_poly (list, _) -> List.map list ~f:(fun _ -> gen_symbol ())
            | _ -> []
          in
          List.map vars ~f:(evar ~loc)
          |> Option.value_exn (recur ~type_name)
          |> eabstract ~loc (List.map vars ~f:(pvar ~loc))
        in
        value_binding ~loc ~pat ~expr)
      |> pstr_value_list ~loc Nonrecursive
    in
    List.concat_map impls ~f:(fun impl -> impl.prelude)
    @ [ (open_infos ~loc ~override:Fresh ~expr:(pmod_structure ~loc open_defns)
         |> pstr_open ~loc)
        :: incl_defns
        |> pmod_structure ~loc
        |> include_infos ~loc
        |> pstr_include ~loc
      ]
  ;;

  let with_typerep ~loc ~path ~named (rec_flag, tds) =
    let tds = List.map tds ~f:name_type_params_in_td in
    match really_recursive rec_flag tds with
    | Nonrecursive -> with_typrep_nonrecursive tds ~loc ~path ~named
    | Recursive -> with_typrep_recursive tds ~loc ~path ~named
  ;;

  let with_typerep_abstract ~loc:_ ~path (_rec_flag, tds) =
    List.map tds ~f:(fun td ->
      let td = name_type_params_in_td td in
      let loc = td.ptype_loc in
      let type_name = td.ptype_name.txt in
      let params, _ = Util.parse_params ~named:true ~ptype_params:td.ptype_params in
      Util.typerep_abstract ~loc ~path ~type_name ~params)
  ;;

  let gen =
    Deriving.Generator.make
      Deriving.Args.(
        empty +> flag "abstract" +> arg "named" Ast_pattern.(ebool __) +> flag "unboxed")
      (fun ~loc ~path (rf, tds) abstract named unboxed ->
        let named = Option.value ~default:true named in
        let tds = Ppx_helpers.with_implicit_unboxed_records ~loc ~unboxed tds in
        match named, abstract with
        | false, true ->
          Location.raise_errorf
            ~loc
            "ppx_typerep_conv: [~named:false] and [~abstract] are not supported together"
        | true, true -> with_typerep_abstract ~loc ~path (rf, tds)
        | named, false -> with_typerep ~loc ~path ~named (rf, tds))
  ;;

  let typerep_of_extension ~loc:_ ~path:_ ctyp = typerep_of_type ctyp
end

let typerep =
  Deriving.add
    "typerep"
    ~sig_type_decl:Typerep_signature.gen
    ~str_type_decl:Typerep_implementation.gen
;;

let () =
  Deriving.add
    "typerep_of"
    ~extension:
      (Typerep_implementation.typerep_of_extension ~recur:(fun ~type_name:_ -> None))
  |> Deriving.ignore
;;
