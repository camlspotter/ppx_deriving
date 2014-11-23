type 'a t = Foo | Bar of int | Boo of int * 'a [@@deriving conv]

type 'a r = { x : int; y : float * 'a } [@@deriving conv]
