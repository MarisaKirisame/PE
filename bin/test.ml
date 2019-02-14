open PE.Common;;
open Trx;;

module type Lang = sig
  type 'a repr
  type 'a value = 'a repr
  type 'a var = 'a repr
  val lam_: ('a value -> 'b repr) -> ('a -> 'b) repr
  val app_: ('a -> 'b) repr -> ('a repr -> 'b repr)
  val let_: 'a repr -> ('a value -> 'b repr) -> 'b repr
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

module HalfDone = struct
  let lam_ _ = raise NYI
  let app_ _ = raise NYI
  let let_ _ = raise NYI
  let int_ _ = raise NYI
  let add_ _ = raise NYI
  let mkRef_ _ = raise NYI
  let getRef_ _ = raise NYI
  let setRef_ _ = raise NYI
  let mkProd_ _ = raise NYI
  let zro_ _ = raise NYI
  let fst_ _ = raise NYI
  let left_ _ = raise NYI
  let right_ _ = raise NYI
  let match_ _ = raise NYI
end;;

module Eval:Lang = struct
  type 'a repr = 'a
  type 'a value = 'a repr
  let lam_ f = f
  let app_ f x = f x
  let let_ x f = f x
  let int_ x = x
  let add_ = (+)
  let mkRef_ x = ref x
  let getRef_ x = !x
  let setRef_ x y = x := y
  let mkProd_ x y = (x, y)
  let zro_ (x, _) = x
  let fst_ (_, y) = y
  let left_ x = Left x
  let right_ x = Right x
  let match_ s l r =
    match s with
    | Left x -> l x
    | Right x -> r x
end;;

exception NYI;;

module Code: Lang = struct
  type 'a repr = 'a code
  type 'a value = 'a repr
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
  let right_ x = .<Right .~x>.
  let match_ s l r = .<
    match .~s with
    | Left x -> .~l x
    | Right x -> .~r x>.
end;;

module PE(L: Lang): Lang = struct
  include HalfDone
  type 'a shared = Return of 'a | Let: 'a L.repr * ('a L.value -> 'b shared) -> 'b shared
  let rec shared_join =
    function
    | Return a -> a
    | Let (a, f) -> Let (a, fun a -> shared_join (f a))
  (*this is a free monad.
    might do asymptotic improvement of computations over free monad
    to improve the performance.*)
  let rec shared_fmap f =
    function
    | Return a -> f a
    | Let (a, g) -> Let (a, fun a -> shared_fmap f (g a))
  let rec shared_bind a m =
    match a with
    | Return a -> m a
    | Let (a, f) -> Let (a, fun a -> shared_bind (f a) m)
  type
    'a static =
    | SInt: int -> int static
    | SProd: ('a ps * 'b ps) -> ('a * 'b) static
  and
    'a ps = PS of 'a static option * 'a L.repr
  type 'a repr = 'a ps
  type 'a value = 'a repr
  let dyn = function | PS (_, x) -> x
  let lam_ f = PS (None, L.lam_ (fun x -> dyn (f (PS (None, x)))))
  let app_ (PS (_, f)) (PS (_, x)) = PS (None, L.app_ f x)
  let let_ x f = f x
  let int_ x = PS (Some (SInt x), L.int_ x)
  let add_ (PS (sl, dl)) (PS (sr, dr)) =
    let sip =
      function
      | (Some (SInt x), Some (SInt y)) -> Some (SInt (x + y))
      | _ -> None
    in
    PS (sip (sl, sr), L.add_ dl dr)
end;;
