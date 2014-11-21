type 'a t = Foo | Bar of int | Boo of int * 'a [@@deriving conv]
