open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience

let deriver = "conv"
let raise_errorf = Ppx_deriving.raise_errorf

let parse_options options =
  options |> List.map (fun (name, expr) ->
    match name, expr with
    | _, { pexp_desc = Pexp_ident {txt = Lident n} } when n = name -> name
    | _ -> raise_errorf ~loc:expr.pexp_loc "%s does not support option %s" deriver name)

let attr_printer attrs =
  Ppx_deriving.(attrs |> attr ~deriver "printer" |> Arg.(get_attr ~deriver expr))

let attr_polyprinter attrs =
  Ppx_deriving.(attrs |> attr ~deriver "polyprinter" |> Arg.(get_attr ~deriver expr))

let attr_opaque attrs =
  Ppx_deriving.(attrs |> attr ~deriver "opaque" |> Arg.get_flag ~deriver)

let argn = Printf.sprintf "a%d"

type mode = {
  fix : string; (* json *)
  type_ : string; (* Json.t *)
  conv : string; (* "Json_conv" *)
}

let (^.^) x y = x ^ "." ^ y

let conv m s = Exp.(ident @@ lid @@ m.conv ^.^ s)

module Expr(A : sig
  (* val m : mode *)
  val of_ : string -> Parsetree.expression (** t => ocaml_of_ x *)
  val mangle_lid : Longident.t -> Longident.t (** A.t => A.ocaml_of_x *)
  (* val mangle_type_decl : Parsetree.type_declaration -> string *)
end) = struct

  open A

  let rec expr_of_typ typ = match typ with
    | [%type: int]    -> of_ "int"
    | [%type: int32]     | [%type: Int32.t] -> of_ "int32"
    | [%type: int64]     | [%type: Int64.t] -> of_ "int64"
    | [%type: nativeint] | [%type: Nativeint.t] -> of_ "nativeint"
    | [%type: float]  -> of_ "float"
    | [%type: bool]   -> of_ "bool"
    | [%type: char]   -> of_ "char"
    | [%type: string] -> of_ "string"
    | [%type: bytes]  -> of_ "bytes"
    | [%type: [%t? typ] ref]   ->
        [%expr [%e of_ "ref"] [%e expr_of_typ typ] ]
    | [%type: [%t? typ] list]  -> 
        [%expr [%e of_ "list"] [%e expr_of_typ typ] ]
    | [%type: [%t? typ] array] ->
        [%expr [%e of_ "array"] [%e expr_of_typ typ] ]
    | [%type: [%t? typ] option] ->
        [%expr [%e of_ "option"] [%e expr_of_typ typ] ]
    | { ptyp_desc = Ptyp_arrow (l, t1, t2) } ->
        [%expr [% of_ "arrow"] l [%e expr_of_typ t1] [%e expr_of_typ t2]]
    | { ptyp_desc = Ptyp_constr ({ txt = lid }, args) } ->
        let args_pp = List.map (fun typ -> [%expr [%e expr_of_typ typ]]) args in
          app (Exp.ident (mknoloc (mangle_lid lid))) args_pp
    | { ptyp_desc = Ptyp_tuple typs } ->
        let args = List.mapi (fun i typ -> app (expr_of_typ typ) [evar (argn i)]) typs in
        [%expr
            fun [%p ptuple (List.mapi (fun i _ -> pvar (argn i)) typs)] ->
              [%e of_ "tuple"] [%e list args]
        ]
    | { ptyp_desc = Ptyp_variant (fields, _, _); ptyp_loc } ->
        let cases =
          fields |> List.map (fun field ->
            match field with
            | Rtag (label, _, true (*empty*), []) -> (* `L *)
                Exp.case (Pat.variant label None)
                  [%expr 
                      [%e of_ "poly_variant" ]
                      (str label)
                      None
                  ]
            | Rtag (label, _, false, [typ]) -> (* `L of typ *)
                Exp.case (Pat.variant label (Some [%pat? x]))
                  [%expr 
                      [% e of_ "poly_variant" ]
                      (str label)
                      Some ([%e expr_of_typ typ] x)
                  ]
            | Rinherit ({ ptyp_desc = Ptyp_constr (tname, []) } as typ) -> (* [ tname ] *)
                Exp.case [%pat? [%p Pat.type_ tname] as x]
                  [%expr [%e expr_of_typ typ] x]
            | _ ->
                raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                    deriver (Ppx_deriving.string_of_core_type typ))
        in
        Exp.function_ cases
    | { ptyp_desc = Ptyp_alias (typ, _) } -> expr_of_typ typ
    | { ptyp_desc = Ptyp_var name } -> [%expr [%e evar ("poly_"^name)]]
    | { ptyp_loc } ->
        raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
          deriver (Ppx_deriving.string_of_core_type typ)
end

module Encoder(A : sig
  val m : mode
end) = struct

  open A

  let of_ n = evar @@ m.conv ^.^ m.fix ^ "_of_" ^ n
  let mangle_lid = Ppx_deriving.mangle_lid ~fixpoint:" impos " (`Prefix (m.fix ^ "_of"))
  let mangle_type_decl = Ppx_deriving.mangle_type_decl ~fixpoint:" impos " (`Prefix (m.fix ^ "_of"))

  include Expr(struct
    let of_ = of_
    let mangle_lid = mangle_lid
    let mangle_type_decl = mangle_type_decl
  end)

  let str_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
    let _modes = parse_options options in
    (* let path = Ppx_deriving.path_of_type_decl ~path type_decl in *)
    let type_name = type_decl.ptype_name.txt in
    let conv_of =
      match type_decl.ptype_kind, type_decl.ptype_manifest with
      | Ptype_abstract, Some manifest ->
          expr_of_typ manifest
      | Ptype_variant constrs, _ ->
          let cases =
            constrs |> List.map (fun { pcd_name = { txt = constr_name }; pcd_args } ->
              let args = List.mapi (fun i typ -> app (expr_of_typ typ) [evar (argn i)]) pcd_args in
              let result =
                [%expr [%e of_ "variant"] 
                    [%e str type_name]
                    [%e str constr_name] 
                    [%e list args]
                ]
              in
              Exp.case (pconstr constr_name (List.mapi (fun i _ -> pvar (argn i)) pcd_args)) result)
          in
          Exp.function_ cases
      | Ptype_record labels, _ ->
          let fields =
            labels |> List.mapi (fun i { pld_name = { txt = name }; pld_type } ->
              [%expr ( [%e str name], 
                       [%e expr_of_typ pld_type] 
                         [%e Exp.field (evar "x") (lid name) ] )])
          in
          [%expr fun x -> 
            [%e of_ "record"] 
              [%e str type_name]
              [%e list fields]
          ]
    | Ptype_abstract, None ->
        raise_errorf ~loc "%s cannot be derived for fully abstract types" deriver
    | Ptype_open, _        ->
        raise_errorf ~loc "%s cannot be derived for open types" deriver
    in
(*
  let pp_poly_apply = Ppx_deriving.poly_apply_of_type_decl type_decl (evar
                        (mangle_type_decl type_decl)) in
*)
(*
  let stringprinter = [%expr fun x -> Format.asprintf "%a" [%e pp_poly_apply] x] in
*)
    let polymorphize  = Ppx_deriving.poly_fun_of_type_decl type_decl in
    [ Vb.mk 
        (pvar (mangle_type_decl type_decl))
        (polymorphize conv_of)
    ]

  let sig_of_type ~options ~path type_decl =
    ignore @@ parse_options options;
    let typ = Ppx_deriving.core_type_of_type_decl type_decl in
    let polymorphize = Ppx_deriving.poly_arrow_of_type_decl
      (fun var -> [%type: [%t var] -> conv]) type_decl in
    [ Sig.value (Val.mk 
                   (mknoloc (mangle_type_decl type_decl)) 
                   (polymorphize [%type: [%t typ] -> conv]))
    ]
(*
  let polymorphize = Ppx_deriving.poly_arrow_of_type_decl
        (fun var -> [%type: Format.formatter -> [%t var] -> unit]) type_decl in
  [Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix "pp") type_decl))
              (polymorphize [%type: Format.formatter -> [%t typ] -> unit]));
   Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix "show") type_decl))
              (polymorphize [%type: [%t typ] -> string]))]
*)
end

module Decoder(A : sig
  val m : mode
end) = struct

  open A

  let of_ n = evar @@ m.conv ^.^ m.fix ^ "_of_" ^ n
  let mangle_lid = Ppx_deriving.mangle_lid ~fixpoint:" impos " (`Suffix ("of_" ^ m.fix))
  let mangle_type_decl = Ppx_deriving.mangle_type_decl ~fixpoint:" impos " (`Suffix ("of_" ^ m.fix))

  include Expr(struct
    include A
    let of_ = of_
    let mangle_lid = mangle_lid
    let mangle_type_decl = mangle_type_decl
  end)

  let str_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
    let _modes = parse_options options in
    (* let type_name = type_decl.ptype_name.txt in *)
    let conv_of =
      match type_decl.ptype_kind, type_decl.ptype_manifest with
      | Ptype_abstract, Some manifest ->
          expr_of_typ manifest
      | Ptype_variant constrs, _ ->
          let cases =
            constrs |> List.map begin fun { pcd_name = { txt = constr_name }; pcd_args } ->
              [ Exp.case 
                  [%pat? ( [%p pstr constr_name],
                           [%p plist (List.mapi (fun i _ -> pvar (argn i)) pcd_args)] )]
                  (constr constr_name (List.mapi (fun i _ -> evar (argn i)) pcd_args))
              ; Exp.case
                  [%pat? ( [%p pstr constr_name], _)]
                  [%expr raise Exit]
              ]
            end
          in
          [%expr fun v -> 
            [%e Exp.match_ 
                [%expr [%e of_ "variant"] v ]
                (List.concat cases @ [ Exp.case [%pat? _] [%expr raise Exit]] )
            ]
          ]

      | Ptype_record labels, _ ->
          (* kvs and v must be unique *)
          let rec make_unique base labels =
            if not @@ List.exists (fun l -> base = l) labels then base
            else make_unique (base ^ "'") labels
          in
          let ls = List.map (fun { pld_name = { txt = name }} -> name) labels in
          let kvs = make_unique "kvs" ls in
          let v = make_unique "v" ls in
          let extract name pld_type k =
            [%expr
               let [%p pvar v], [%p pvar kvs] = Meta_conv.find [%e evar kvs] [%e str name] in
               let [%p pvar name] = [%e expr_of_typ pld_type] [%e evar v] in
               [%e k]
            ]
          in
          [%expr fun v ->
            let [%p pvar kvs] = [%e of_ "record"] v in
            [%e 
                List.fold_right (fun { pld_name = { txt = name }; pld_type } st ->
                  extract name pld_type st)
                labels
                [%expr
                    if [%e evar kvs] <> [] then raise Exit;
                    [%e 
                        record (List.map (fun { pld_name = { txt = name }} ->
                          (name, evar name)) labels)
                    ]
                ]
            ]
          ]
    | Ptype_abstract, None ->
        raise_errorf ~loc "%s cannot be derived for fully abstract types" deriver
    | Ptype_open, _        ->
        raise_errorf ~loc "%s cannot be derived for open types" deriver
    in
(*
  let pp_poly_apply = Ppx_deriving.poly_apply_of_type_decl type_decl (evar
                        (mangle_type_decl type_decl)) in
*)
(*
  let stringprinter = [%expr fun x -> Format.asprintf "%a" [%e pp_poly_apply] x] in
*)
    let polymorphize  = Ppx_deriving.poly_fun_of_type_decl type_decl in
    [ Vb.mk 
        (pvar (mangle_type_decl type_decl))
        (polymorphize conv_of)
    ]

  let sig_of_type ~options ~path type_decl =
    ignore @@ parse_options options;
    let typ = Ppx_deriving.core_type_of_type_decl type_decl in
    let polymorphize = Ppx_deriving.poly_arrow_of_type_decl
      (fun var -> [%type: conv -> [%t var]]) type_decl in
    [ Sig.value (Val.mk 
                   (mknoloc (mangle_type_decl type_decl)) 
                   (polymorphize [%type: conv -> [%t typ]]))
    ]
(*
  let polymorphize = Ppx_deriving.poly_arrow_of_type_decl
        (fun var -> [%type: Format.formatter -> [%t var] -> unit]) type_decl in
  [Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix "pp") type_decl))
              (polymorphize [%type: Format.formatter -> [%t typ] -> unit]));
   Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix "show") type_decl))
              (polymorphize [%type: [%t typ] -> string]))]
*)
end


module E = Encoder(struct 
  let m = { fix = "conv"; 
            type_ = "Conv.t";
            conv = "Conv_conv" }
end)

module D = Decoder(struct 
  let m = { fix = "conv"; 
            type_ = "Conv.t";
            conv = "Conv_conv" }
end)

let () =
  Ppx_deriving.(register deriver {
    core_type = None;
(*
      Some (fun typ ->
        [%expr fun x -> Format.asprintf "%a" (fun fmt -> [%e expr_of_typ typ]) x]);
*)
    structure = (fun ~options ~path type_decls ->
      [ Str.value Recursive (List.concat (List.map (E.str_of_type ~options ~path) type_decls))
      ; Str.value Recursive (List.concat (List.map (D.str_of_type ~options ~path) type_decls))
      ]);
    signature = (fun ~options ~path type_decls ->
      List.concat (List.concat (List.map (fun td ->
        [ E.sig_of_type ~options ~path td
        ; D.sig_of_type ~options ~path td
        ] ) type_decls)));
  })
