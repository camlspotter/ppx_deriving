open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience

let prefix = "conv"
let raise_errorf = Ppx_deriving.raise_errorf

let argn = Printf.sprintf "a%d"

let rec expr_of_typ typ =
  match Ppx_deriving.attr ~prefix "encoder" typ.ptyp_attributes with
  | Some (_, PStr [{ pstr_desc = Pstr_eval (encoder, _) }]) -> 
      (* [@conv <encoder>] *)
      [%expr [%e encoder]]
  | Some ({ loc }, _) -> 
      (* [@conv other thing] *)
      raise_errorf ~loc "Invalid [@deriving.%s.encoder] syntax" prefix
  | None ->
      match typ with
      | [%type: int]    -> [%expr E.int]
      | [%type: int32]     | [%type: Int32.t] -> [%expr E.int32]
      | [%type: int64]     | [%type: Int64.t] -> [%expr E.int64]
      | [%type: nativeint] | [%type: Nativeint.t] -> [%expr E.nativeint]
      | [%type: float]  -> [%expr E.float]
      | [%type: bool]   -> [%expr E.bool]
      | [%type: char]   -> [%expr E.char]
      | [%type: string] -> [%expr E.string]
      | [%type: bytes]  -> [%expr E.bytes]
      | [%type: [%t? typ] list]  -> 
          [%expr E.list [%e expr_of_typ typ ] ]
      | [%type: [%t? typ] array] -> 
          [%expr E.array [%e expr_of_typ typ ] ]
      | [%type: [%t? typ] option] ->
          [%expr E.option [%e expr_of_typ typ ] ]

      | { ptyp_desc = Ptyp_constr ({ txt = lid }, args) } ->
          app 
            (Exp.ident (mknoloc (Ppx_deriving.mangle_lid (`Prefix "encode") lid)))
            (List.map expr_of_typ args)

      | { ptyp_desc = Ptyp_tuple typs } ->
          let args = List.mapi (fun i typ -> app (expr_of_typ typ) [evar (argn i)]) typs in
          [%expr
              fun [%p ptuple (List.mapi (fun i _ -> pvar (argn i)) typs)] ->
                E.tuple 
                  [%e 
                      List.fold_left (fun x xs -> [%expr [%e x] :: [%e xs]]) 
                      [%expr []]
                      args
                  ]
          ]
(*
    | { ptyp_desc = Ptyp_variant (fields, _, _); ptyp_loc } ->
      let cases =
        fields |> List.map (fun field ->
          match field with
          | Rtag (label, _, true (*empty*), []) ->
            Exp.case (Pat.variant label None)
                     [%expr Format.pp_print_string fmt [%e str ("`" ^ label)]]
          | Rtag (label, _, false, [typ]) ->
            Exp.case (Pat.variant label (Some [%pat? x]))
                     [%expr Format.pp_print_string fmt [%e str ("`" ^ label ^ " (")];
                            [%e expr_of_typ typ] x;
                            Format.pp_print_string fmt ")"]
          | Rinherit ({ ptyp_desc = Ptyp_constr (tname, []) } as typ) ->
            Exp.case [%pat? [%p Pat.type_ tname] as x]
                     [%expr [%e expr_of_typ typ] x]
          | _ ->
            raise_errorf ~loc:ptyp_loc "Cannot derive Conv for %s"
                         (Ppx_deriving.string_of_core_type typ))
      in
      Exp.function_ cases
    | { ptyp_desc = Ptyp_var name } -> [%expr [%e evar ("poly_"^name)] fmt]
    | { ptyp_desc = Ptyp_alias (typ, _) } -> expr_of_typ typ
*)
    | { ptyp_loc } ->
      raise_errorf ~loc:ptyp_loc "Cannot derive Conv for %s"
                   (Ppx_deriving.string_of_core_type typ)

let str_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  let path = Ppx_deriving.path_of_type_decl ~path type_decl in
  let prettyprinter =
    match type_decl.ptype_kind, type_decl.ptype_manifest with
    | Ptype_abstract, Some manifest ->
      [%expr fun fmt -> [%e expr_of_typ manifest]]
    | Ptype_variant constrs, _ ->
      let cases =
        constrs |> List.map (fun { pcd_name = { txt = name' }; pcd_args } ->
          let constr_name = Ppx_deriving.expand_path ~path name' in
          let args = List.mapi (fun i typ -> app (expr_of_typ typ) [evar (argn i)]) pcd_args in
          let result =
            match args with
            | []   -> [%expr Format.pp_print_string fmt [%e str constr_name]]
            | args ->
              [%expr Format.pp_print_string fmt [%e str (constr_name ^ " (")];
              [%e args |> Ppx_deriving.(fold_exprs
                    (seq_reduce ~sep:[%expr Format.pp_print_string fmt ", "]))];
              Format.pp_print_string fmt ")"]
          in
          Exp.case (pconstr name' (List.mapi (fun i _ -> pvar (argn i)) pcd_args)) result)
      in
      [%expr fun fmt -> [%e Exp.function_ cases]]
    | Ptype_record labels, _ ->
      let fields =
        labels |> List.mapi (fun i { pld_name = { txt = name }; pld_type } ->
          let field_name = if i = 0 then Ppx_deriving.expand_path ~path name else name in
          [%expr Format.pp_print_string fmt [%e str (field_name ^ " = ")];
            [%e expr_of_typ pld_type] [%e Exp.field (evar "x") (mknoloc (Lident name))]])
      in
      [%expr fun fmt x ->
        Format.pp_print_string fmt "{ ";
        [%e fields |> Ppx_deriving.(fold_exprs
              (seq_reduce ~sep:[%expr Format.pp_print_string fmt "; "]))];
        Format.pp_print_string fmt " }"]
    | Ptype_abstract, None -> raise_errorf ~loc "Cannot derive Conv for fully abstract type"
    | Ptype_open, _        -> raise_errorf ~loc "Cannot derive Conv for open type"
  in
  let pp_poly_apply = Ppx_deriving.poly_apply_of_type_decl type_decl (evar
                        (Ppx_deriving.mangle_type_decl (`Prefix "pp") type_decl)) in
  let stringprinter = [%expr fun x -> Format.asprintf "%a" [%e pp_poly_apply] x] in
  let polymorphize  = Ppx_deriving.poly_fun_of_type_decl type_decl in
  [Vb.mk (pvar (Ppx_deriving.mangle_type_decl (`Prefix "pp") type_decl))
               (polymorphize prettyprinter);
   Vb.mk (pvar (Ppx_deriving.mangle_type_decl (`Prefix "conv") type_decl))
               (polymorphize stringprinter);]

let sig_of_type ~options ~path type_decl =
  let typ = Ppx_deriving.core_type_of_type_decl type_decl in
  let polymorphize = Ppx_deriving.poly_arrow_of_type_decl
        (fun var -> [%type: Format.formatter -> [%t var] -> unit]) type_decl in
  [Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix "pp") type_decl))
              (polymorphize [%type: Format.formatter -> [%t typ] -> unit]));
   Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix "conv") type_decl))
              (polymorphize [%type: [%t typ] -> string]))]

let () =
  Ppx_deriving.(register "Conv" {
    core_type = (fun typ ->
      [%expr fun x -> Format.asprintf "%a" (fun fmt -> [%e expr_of_typ typ]) x]);
    structure = (fun ~options ~path type_decls ->
      [Str.value Recursive (List.concat (List.map (str_of_type ~options ~path) type_decls))]);
    signature = (fun ~options ~path type_decls ->
      List.concat (List.map (sig_of_type ~options ~path) type_decls));
  })
