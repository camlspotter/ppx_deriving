open OUnit2

(* Mostly it is sufficient to test that the derived code compiles. *)

let printer = string_of_bool

type a1 = int        [@@deriving eq]
type a2 = int32      [@@deriving eq]
type a3 = int64      [@@deriving eq]
type a4 = nativeint  [@@deriving eq]
type a5 = float      [@@deriving eq]
type a6 = bool       [@@deriving eq]
type a7 = char       [@@deriving eq]
type a8 = string     [@@deriving eq]
type a9 = bytes      [@@deriving eq]
type r  = int ref    [@@deriving eq]
type l  = int list   [@@deriving eq]
type a  = int array  [@@deriving eq]
type o  = int option [@@deriving eq]

let test_simple ctxt =
  assert_equal ~printer true  (equal_a1 1 1);
  assert_equal ~printer false (equal_a1 1 2)

type v = Foo | Bar of int * string | Baz of string [@@deriving eq]

type pv1 = [ `Foo | `Bar of int * string ] [@@deriving eq]
type pv2 = [ `Baz | pv1 ] [@@deriving eq]

type ty = int * string [@@deriving eq]

type re = {
  f1 : int;
  f2 : string;
} [@@deriving eq]

module M : sig
  type t = int [@@deriving eq]
end = struct
  type t = int [@@deriving eq]
end

type z = M.t [@@deriving eq]

type file = {
  name : string;
  perm : int     [@equal (<>)];
} [@@deriving eq]
let test_custom ctxt =
  assert_equal ~printer false (equal_file { name = ""; perm = 1 }
                                          { name = ""; perm = 1 });
  assert_equal ~printer true  (equal_file { name = ""; perm = 1 }
                                          { name = ""; perm = 2 })

type 'a pt = { v : 'a } [@@deriving eq]

let test_placeholder ctxt =
  assert_equal ~printer true ([%eq: _] 1 2)


type mrec_variant =
  | MrecFoo of string
  | MrecBar of int

and mrec_variant_list = mrec_variant list [@@deriving eq]

let test_mrec ctxt =
  assert_equal ~printer true  (equal_mrec_variant_list [MrecFoo "foo"; MrecBar 1]
                                                       [MrecFoo "foo"; MrecBar 1]);
  assert_equal ~printer false (equal_mrec_variant_list [MrecFoo "foo"; MrecBar 1]
                                                       [MrecFoo "bar"; MrecBar 1])

type e = Bool of be | Plus of e * e | IfE  of (be, e) if_e | Unit
and be = True | False | And of be * be | IfB of (be, be) if_e
and ('cond, 'a) if_e = 'cond * 'a * 'a
  [@@deriving eq]

let test_mut_rec ctxt =
  let e1 = IfE (And (False, True), Unit, Plus (Unit, Unit)) in
  let e2 = Plus (Unit, Bool False) in
  assert_equal ~printer true (equal_e e1 e1);
  assert_equal ~printer true (equal_e e2 e2);
  assert_equal ~printer false (equal_e e1 e2);
  assert_equal ~printer false (equal_e e2 e1)

type es =
  | ESBool of bool_
  | ESString of string
and bool_ =
  | Bfoo of int * ((int -> int) [@equal fun _ _ -> true])
and string =
  | Sfoo of String.t * ((int -> int) [@equal fun _ _ -> true])
  [@@deriving eq{ allow_std_type_shadowing }]

let test_shadowed_std_type ctxt =
  let e1 = ESBool (Bfoo (1, (+) 1)) in
  let e2 = ESString (Sfoo ("lalala", (+) 3)) in
  assert_equal ~printer false (equal_es e1 e2);
  assert_equal ~printer false (equal_es e2 e1);
  assert_equal ~printer true (equal_es e1 e1);
  assert_equal ~printer true (equal_es e2 e2)


let suite = "Test deriving(eq)" >::: [
    "test_simple"       >:: test_simple;
    "test_custom"       >:: test_custom;
    "test_placeholder"  >:: test_placeholder;
    "test_mrec"         >:: test_mrec;
    "test_mut_rec"      >:: test_mut_rec;
  ]

