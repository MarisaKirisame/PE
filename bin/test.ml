open Runcode;;

module type Lang = sig
  type 'a repr
  val lam_: ('a repr -> 'b repr) -> ('a -> 'b) repr
  val app_: ('a -> 'b) repr -> ('a repr -> 'b repr)
  val let_: 'a repr -> ('a repr -> 'b repr) -> 'b repr
  val int_: int -> int repr
  val add_: int repr -> int repr -> int repr
  val mkRef_: 'a repr -> 'a ref repr
  val getRef_: 'a ref repr -> 'a repr
  val setRef_: 'a ref repr -> 'a repr -> unit repr
  val mkProd_: 'a repr -> 'b repr -> ('a * 'b) repr
  val zro_: ('a * 'b) repr -> 'a repr
  val fst_: ('a * 'b) repr -> 'b repr
  val left_: 'a repr -> ('a, 'b) sum repr
  val right_: 'b repr -> ('a, 'b) sum repr
  val match_: ('a, 'b) sum repr -> ('a -> 'c) repr -> ('b -> 'c) repr -> 'c repr
end;;

module Eval : Lang = struct
  type 'a repr = 'a
  let lam_ f = f
  let app_ f x = f x
  let let_ x f = f x
  let int_ x = x
  let add_ = (+)
  let mkRef_ x = ref x
  let getRef_ x = !x
  let setRef_ x y = x := y
  let mkProd_ x y = (x, y)
  let zro_ (x, y) = x
  let fst_ (x, y) = y
  let left_ x = Left x
  let right_ x = Right x
  let match_ s l r =
    match s with
    | Left x -> l x
    | Right x -> r x
end;;

exception NYI;;

module HalfDone = struct
  let lam_ f = raise NYI
  let app_ f = raise NYI
  let let_ f = raise NYI
  let int_ x = raise NYI
  let add_ x = raise NYI
  let mkRef_ x = raise NYI
  let getRef_ x = raise NYI
  let setRef_ x = raise NYI
  let mkProd_ x = raise NYI
  let zro_ x = raise NYI
  let fst_ x = raise NYI
  let left_ x = raise NYI
  let right_ x = raise NYI
  let match_ s = raise NYI
end;;

module Code : Lang = struct
  include HalfDone
  type 'a repr = 'a code
  let lam_ f = .<fun x -> .~(f .<x>.)>.
  let app_ f x = .<.~f .~x>.
  let let_ x f = .<let y = .~x in .~(f .<y>.)>.
  let int_ x = .<x>.
  let add_ x y = .<.~x + .~y>.
  let mkRef_ x = .<ref .~x>.
  let getRef_ x = .<!(.~x)>.
  let setRef_ x y = .<(.~x):=(.~y)>.
  let mkProd_ x y = .<(.~x, .~y)>.
  let zro_ x = .<fst .~x>.
  let fst_ x = .<snd .~x>.
  let left_ x = .<Left .~x>.
end;;
