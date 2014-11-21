[@@deriving]
============

_deriving_ is a library simplifying type-driven code generation on OCaml >=4.02.

_deriving_ includes a set of useful plugins: [show][], [eq][], [ord][eq], [enum][], [iter][], [map][iter], [fold][iter], [yojson][], [protobuf][].

Sponsored by [Evil Martians](http://evilmartians.com).

[show]: #plugin-show
[eq]: #plugins-eq-and-ord
[enum]: #plugin-enum
[iter]: #plugins-iter-map-and-fold
[yojson]: https://github.com/whitequark/ppx_deriving_yojson#usage
[protobuf]: https://github.com/whitequark/ppx_deriving_protobuf#usage

Installation
------------

_deriving_ can be installed via [OPAM](https://opam.ocaml.org):

    opam install ppx_deriving

Buildsystem integration
-----------------------

To use _deriving_, only one modification is needed: you need to require via ocamlfind the package corresponding to the _deriving_ plugin. This will both engage the syntax extension and link in the runtime components of the _deriving_ plugin, if any.

For example, if you are using ocamlbuild, add the following to `_tags` to use the default _deriving_ plugins:

    <src/*>: package(ppx_deriving.std)

If you are using another buildsystem, just make sure it passes `-package ppx_deriving_whatever` to ocamlfind.

Usage
-----

From a user's perspective, _deriving_ is triggered by a `[@@deriving plugin]` annotation attached to a type declaration in structure or signature:

``` ocaml
type point2d = float * float
[@@deriving show]
```

It's possible to invoke several plugins by separating their names with commas:

``` ocaml
type point3d = float * float * float
[@@deriving show, eq]
```

It's possible to pass options to a plugin by appending a record to plugin's name:

``` ocaml
type t = string
[@@deriving ord { affix = true }]
```

It's possible to make _deriving_ ignore a missing plugin rather than raising an error by passing an `optional = true` option, for example, to enable conditional compilation:

``` ocaml
type addr = string * int
[@@deriving json { optional = true }]
```

It's also possible for many plugins to derive a function directly from a type, without declaring it first.

``` ocaml
open OUnit2
let test_list_sort ctxt =
  let sort = List.sort [%derive.ord: int * int] in
  assert_equal ~printer:[%derive.show: (int * int) list]
               [(1,1);(2,0);(3,5)] (sort [(2,0);(3,5);(1,1)])
```

The `[%derive.x:]` syntax can be shortened to `[%x:]`, given that the deriver `x` exists and the payload is a type. If these conditions are not satisfied, the extension node will be left uninterpreted to minimize potential conflicts with other rewriters.

### Working with existing types

At first, it may look like _deriving_ requires complete control of the type declaration. However, a lesser-known OCaml feature allows to derive functions for any existing type. Using `Pervasives.fpclass` as an example, _show_ can be derived as follows:

``` ocaml
# module M = struct
  type myfpclass = fpclass = FP_normal | FP_subnormal | FP_zero | FP_infinite | FP_nan
  [@@deriving show]
end;;
module M :
  sig
    type myfpclass =
      fpclass =
        FP_normal
      | FP_subnormal
      | FP_zero
      | FP_infinite
      | FP_nan
    val pp_myfpclass : Format.formatter -> fpclass -> unit
    val show_myfpclass : fpclass -> bytes
  end
# M.show_myfpclass FP_normal;;
- : bytes = "FP_normal"
```

The module is used to demonstrate that `show_myfpclass` really accepts `Pervasives.fpclass`, and not just `M.myfpclass`.

The need to repeat the type definition may look tedious, but consider this: if the definition was automatically imported from the declaration point, how would you attach attributes to refine the behavior of the deriving plugin?

Nevertheless, for the case where no attributes need to be attached, it is possible to use [ppx_import](https://github.com/whitequark/ppx_import#usage) to automatically pull in the type definition.

Plugin conventions
------------------

It is expected that all _deriving_ plugins will follow the same conventions, thus simplifying usage.

  * By default, the functions generated by a plugin for a `type foo` are called `fn_foo` or `foo_fn`. However, if the type is called `type t`, the function will be named `foo`. The defaults can be overridden by an `affix = true|false` plugin option.

  * There may be additional attributes attached to the AST. In case of a plugin named `eq` and attributes named `compare` and `skip`, the plugin must recognize all of `compare`, `skip`, `eq.compare`, `eq.skip`, `deriving.eq.compare` and `deriving.eq.skip` annotations. However, if it detects that at least one namespaced (e.g. `eq.compare` or `deriving.eq.compare`) attribute is present, it must not look at any attributes located within a different namespace. As a result, different ppx rewriters can avoid interference even if the attribute names they use overlap.

  * A typical plugin should handle tuples, records, normal and polymorphic variants; builtin types: `int`, `int32`, `int64`, `nativeint`, `float`, `bool`, `char`, `string`, `bytes`, `ref`, `list`, `array`, `option` and their `Mod.t` aliases; abstract types; and `_`. For builtin types, it should have customizable, sensible default behavior. For abstract types, it should expect to find the functions it would derive itself for that type.

  * If a type is parametric, the generated functions accept an argument for every type variable before all other arguments.

Plugin: show
------------

_show_ derives a function that inspects a value; that is, pretty-prints it with OCaml syntax. However, _show_ offers more insight into the structure of values than the Obj-based pretty printers (e.g. `Printexc`), and more flexibility than the toplevel printer.

``` ocaml
# type t = [ `A | `B of int ] [@@deriving show];;
type t = [ `A | `B of i ]
val pp : Format.formatter -> [< `A | `B of i ] -> unit = <fun>
val show : [< `A | `B of i ] -> bytes = <fun>
# show (`B 1);;
- : bytes = "`B (1)"
```

For an abstract type `ty`, _show_ expects to find a `pp_ty` function in the corresponding module.

_show_ allows to specify custom formatters for types to override default behavior. A formatter for type `t` has a type `Format.formatter -> t -> unit`:

``` ocaml
# type file = {
  name : string;
  perm : int     [@printer fun fmt -> fprintf fmt "0o%03o"];
} [@@deriving show];;
# show_file { name = "dir"; perm = 0o755 };;
- : bytes = "{ name = \"dir\"; perm = 0o755 }"
```

It is also possible to use `[@polyprinter]`. The difference is that for a type `int list`, `[@printer]` should have a signature `formatter -> int list -> unit`, and for `[@polyprinter]` it's `('a -> formatter -> unit) -> formatter -> 'a list -> unit`.

`[@opaque]` is a shorthand for `[@printer fun fmt _ -> Format.pp_print_string fmt "<opaque>"]`.

The function `fprintf` is locally defined in the printer.

Plugins: eq and ord
-------------------

_eq_ derives a function comparing values by semantic equality; structural or physical depending on context. _ord_ derives a function defining a total order for values, returning `-1`, `0` or `1`. They're similar to `Pervasives.(=)` and `Pervasives.compare`, but are faster, allow to customize the comparison rules, and never raise at runtime. _eq_ and _ord_ are short-circuiting.

``` ocaml
# type t = [ `A | `B of int ] [@@deriving eq, ord];;
type t = [ `A | `B of int ]
val equal : [> `A | `B of int ] -> [> `A | `B of int ] -> bool = <fun>
val compare : [ `A | `B of int ] -> [ `A | `B of int ] -> int = <fun>
# equal `A `A;;
- : bool = true
# equal `A (`B 1);;
- : bool = false
# compare `A `A;;
- : int = 0
# compare (`B 1) (`B 2);;
- : int = -1
```

For variants, _ord_ uses the definition order. For builtin types, properly monomorphized `(=)` is used for _eq_, or corresponding `Mod.compare` function (e.g. `String.compare` for `string`) for _ord_. For an abstract type `ty`, _eq_ and _ord_ expect to find an `equal_ty` or `compare_ty` function in the corresponding module.

_eq_ and _ord_ allow to specify custom comparison functions for types to override default behavior. A comparator for type `t` has a type `t -> t -> bool` for _eq_ or `t -> t -> int` for _ord_. If an _ord_ comparator returns a value outside -1..1 range, the behavior is unspecified.

``` ocaml
# type file = {
  name : string [@equal fun a b -> String.(lowercase a = lowercase b)];
  perm : int    [@compare fun a b -> compare b a]
} [@@deriving eq, Ord];;
type file = { name : bytes; perm : int; }
val equal_file : file -> file -> bool = <fun>
val compare_file : file -> file -> int = <fun>
# equal_file { name = "foo"; perm = 0o644 } { name = "Foo"; perm = 0o644 };;
- : bool = true
# compare_file { name = "a"; perm = 0o755 } { name = "a"; perm = 0o644 };;
- : int = -1
```

Plugin: enum
------------

_enum_ is a plugin that treats variants with argument-less constructors as enumerations with an integer value assigned to every constructor. _enum_ derives functions to convert the variants to and from integers, and minimal and maximal integer value.

``` ocaml
# type insn = Const | Push | Pop | Add [@@deriving enum];;
type insn = Const | Push | Pop | Add
val insn_to_enum : insn -> int = <fun>
val insn_of_enum : int -> insn option = <fun>
val min_insn : int = 0
val max_insn : int = 3
# insn_to_enum Pop;;
- : int = 2
# insn_of_enum 3;;
- : insn option = Some Add
```

By default, the integer value associated is `0` for lexically first constructor, and increases by one for every next one. It is possible to set the value explicitly with `[@value 42]`; it will keep increasing from the specified value.

Plugins: iter, map and fold
---------------------------

_iter_, _map_ and _fold_ are three closely related plugins that generate code for traversing polymorphic data structures in lexical order and applying a user-specified action to all values corresponding to type variables.

``` ocaml
# type 'a btree = Node of 'a btree * 'a * 'a btree | Leaf [@@deriving iter, map, fold];;
type 'a btree = Node of 'a btree * 'a * 'a btree | Leaf
val iter_btree : ('a -> unit) -> 'a btree -> unit = <fun>
val map_btree : ('a -> 'b) -> 'a btree -> 'b btree = <fun>
val fold_btree : ('a -> 'b -> 'a) -> 'a -> 'b btree -> 'a = <fun>
# let tree = (Node (Node (Leaf, 0, Leaf), 1, Node (Leaf, 2, Leaf)));;
val tree : int btree = Node (Node (Leaf, 0, Leaf), 1, Node (Leaf, 2, Leaf))
# iter_btree (Printf.printf "%d\n") tree;;
0
1
2
- : unit = ()
# map_btree ((+) 1) tree;;
- : int btree = Node (Node (Leaf, 1, Leaf), 2, Node (Leaf, 3, Leaf))
# fold_btree (+) 0 tree;;
- : int = 3
```

Building ppx drivers
--------------------

By default, _deriving_ dynlinks every plugin, whether invoked as a part of a batch compilation or from the toplevel. If this is unsuitable for you for some reason, it is possible to precompile a ppx rewriter executable that includes several _deriving_ plugins:

```
$ ocamlfind opt -predicates ppx_driver -package ppx_deriving_foo -package ppx_deriving_bar \
                -package ppx_deriving.main -linkpkg -linkall -o ppx_driver
```

Currently, the resulting ppx driver still depends on Dynlink as well as retains the ability to load more plugins.

Developing plugins
------------------

This section only explains the tooling and best practices. Anyone aiming to implement their own _deriving_ plugin is encouraged to explore the existing ones, e.g. [eq](src_plugins/ppx_deriving_eq.ml) or [show](src_plugins/ppx_deriving_show.ml).

### Tooling and environment

A _deriving_ plugin is packaged as a Findlib library; this library should include a peculiar META file. As an example, let's take a look at a description of a _yojson_ plugin:

```
version = "1.0"
description = "[@@deriving yojson]"
exists_if = "ppx_deriving_yojson.cma"
# The following part affects batch compilation and toplevel.
# The plugin package may require any runtime component it needs.
requires(-ppx_driver) = "ppx_deriving yojson"
ppxopt(-ppx_driver) = "ppx_deriving,./ppx_deriving_yojson.cma"
# The following part affects ppx driver compilation.
requires(ppx_driver) = "ppx_deriving.api"
archive(ppx_driver, byte) = "ppx_deriving_yojson.cma"
archive(ppx_driver, native) = "ppx_deriving_yojson.cmxa"
```

The module(s) provided by the package in the `ppxopt` variable must register the derivers using `Ppx_deriving.register "foo"` during loading. Any number of derivers may be registered; careful registration would allow a _yojson_ deriver to support all three of `[@@deriving yojson]`, `[@@deriving of_yojson]` and `[@@deriving to_yojson]`, as well as `[%derive.of_yojson:]` and `[%derive.to_yojson:]`.

It is possible to test the plugin without installing it by instructing _deriving_ to load it directly; the compiler should be invoked as `ocamlfind c -ppx 'ocamlfind ppx_deriving/ppx_deriving src/ppx_deriving_foo.cma' ...`. The file extension is replaced with `.cmxs` automatically for native builds. This can be integrated with buildsystem, e.g. for ocamlbuild:

``` ocaml
let () = dispatch (
  function
  | After_rules ->
    flag ["ocaml"; "compile"; "deriving_foo"] &
      S[A"-ppx"; A("ocamlfind ppx_deriving/ppx_deriving src/ppx_deriving_foo.cma")]
  | _ -> ()
```

### Goals of the API

_deriving_ is a thin wrapper over the ppx rewriter system. Indeed, it includes very little logic; the goal of the project is 1) to provide common reusable abstractions required by most, if not all, deriving plugins, and 2) encourage the deriving plugins to cooperate and to have as consistent user interface as possible.

As such, _deriving_:

  * Completely defines the syntax of `[@@deriving]` annotation and unifies the plugin discovery mechanism;
  * Provides an unified, strict option parsing API to plugins;
  * Provides helpers for parsing annotations to ensure that the plugins interoperate with each other and the rest of the ecosystem.

### Using the API

Complete API documentation is available [online](http://whitequark.github.io/ppx_deriving/Ppx_deriving.html).

The following is a list of tips for developers trying to use the ppx interface:

  * Module paths overwhelm you? Open all of the following modules, they don't conflict with each other: `Longident`, `Location`, `Asttypes`, `Parsetree`, `Ast_helper`, `Ast_convenience`.
  * Need to insert some ASTs? See [ppx_metaquot](https://github.com/alainfrisch/ppx_tools/blob/master/ppx_metaquot.ml); it is contained in the `ppx_tools.metaquot` package.
  * Need to display an error? Use `Ppx_deriving.raise_errorf ~loc "Cannot derive Foo: (error description)"` ([doc](http://whitequark.github.io/ppx_deriving/Ppx_deriving.html#VALraise_errorf)); keep it clear which deriving plugin raised the error!
  * Need to derive a function name from a type name? Use [Ppx_deriving.mangle_type_decl](http://whitequark.github.io/ppx_deriving/Ppx_deriving.html#VALmangle_type_decl) and [Ppx_deriving.mangle_lid](http://whitequark.github.io/ppx_deriving/Ppx_deriving.html#VALmangle_lid).
  * Need to fetch an attribute from a node? Use `Ppx_deriving.attr ~prefix "foo" nod.nod_attributes` ([doc](http://whitequark.github.io/ppx_deriving/Ppx_deriving.html#VALattr)); this takes care of interoperability.
  * Put all functions derived from a set of type declarations into a single `let rec` block; this reflects the always-recursive nature of type definitions.
  * Need to handle polymorphism? Use [Ppx_deriving.poly_fun_of_type_decl](http://whitequark.github.io/ppx_deriving/Ppx_deriving.html#VALpoly_fun_of_type_decl) for derived functions, [Ppx_deriving.poly_arrow_of_type_decl](http://whitequark.github.io/ppx_deriving/Ppx_deriving.html#VALpoly_arrow_of_type_decl) for signatures, and [Ppx_deriving.poly_apply_of_type_decl](http://whitequark.github.io/ppx_deriving/Ppx_deriving.html#VALpoly_apply_of_type_decl) for "forwarding" the arguments corresponding to type variables to another generated function.
  * Need to display a full path to a type, e.g. for an error message? Use [Ppx_deriving.path_of_type_decl](http://whitequark.github.io/ppx_deriving/Ppx_deriving.html#VALpath_of_type_decl).
  * Need to apply a sequence or a binary operator to variant, tuple or record elements? Use [Ppx_deriving.fold_exprs](http://whitequark.github.io/ppx_deriving/Ppx_deriving.html#VALfold_exprs).
  * Don't forget to display an error message if your plugin doesn't parse any options.

License
-------

_deriving_ is distributed under the terms of [MIT license](LICENSE.txt).
