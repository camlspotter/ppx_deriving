type 'a t = Foo | Bar of int | Boo of 'a * 'a [@@deriving conv]
