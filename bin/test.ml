open PE.Common;;
open Trx;;

type var = Var of int

type term =
  | FromVar of var
  | Abs of (var * term)
  | App of (term * term)
  | Let of (var * term * term)
  | Int of int
  | Add of (term * term)
  | MkRef of term
  | GetRef of term
  | SetRef of (term * term)
  | MkProd of (term * term)
  | Zro of term
  | Fst of term
  | Left of term
  | Right of term
  | Match of term * term * term
  | Unit

let fresh = ref 0

let genFresh() =
  let ret = !fresh in
  fresh := ret + 1;
  Var ret

type letList = (term -> term) ref

let push l x =
  let lv = !l in
  let v = genFresh() in
  l := (fun t -> lv(Let(v, x, t)));
  FromVar v

type value =
  | VFun of (value -> value)
  | VInt of int
  | VRef of value ref
  | VProd of value * value
  | VSum of (value, value) sum
  | VUnit

(*Our partial evaluator has almost the same value as the ordinary evaluator.
  the only problem is that reference environment might be touched by unknown SetRef/App,
  so we have to modify it by keeping a time ref denoting the last time it was touched.
  The static ref will include a timestamp denoting the last valid time.

  Since duplication with effect is semantically incorrect, dynVal will hold only value.
  Computation must be pushed to a letList ref.
*)
type time = int

type
  static =
  | SFun of (letList -> pValue -> pValue)
  | SInt of int
  | SRef of (pValue * time) ref
  | SProd of pValue * pValue
  | SSum of (pValue, pValue) sum
  | SUnit
and
  pValue =
  { pStatic: static option;
    dynVal: term }

let fresh: int ref = ref 0

type 'a env = var -> 'a

let extend e (Var v) x =
  function
  | Var i when i == v -> x
  | i -> e i

let incTime x =
  x := (!x) + 1

let static s d = { pStatic = Some s; dynVal = d }

let staticInt s = static (SInt s) (Int s)

let dynamic d = { pStatic = None; dynVal = d }

let rec peAux(curTime: time ref)(e: pValue env)(l : letList): term -> pValue =
  let recurse = peAux curTime e l in
  let app x y =
    match x.pStatic with
    | Some (SFun f) -> f l y
    | _ -> incTime curTime; dynamic (push l (App (x.dynVal, y.dynVal)))
  in
  function
  | Int i -> staticInt i
  | Add (x, y) ->
    let px = recurse(x) in
    let py = recurse(y) in
    (match (px.pStatic, py.pStatic) with
    | (Some (SInt x), Some (SInt y)) -> staticInt (x + y)
    | _ -> dynamic (push l (Add (px.dynVal, py.dynVal))))
  | MkProd (x, y) ->
    let px = recurse(x) in
    let py = recurse(y) in
    static (SProd (px, py)) (push l (MkProd (px.dynVal, py.dynVal)))
  | Zro x ->
    let px = recurse(x) in
    (match px.pStatic with
     | Some (SProd (x, _)) -> x
     | _ -> dynamic (push l (Zro (px.dynVal))))
  | Fst x ->
    let px = recurse(x) in
    (match px.pStatic with
     | Some (SProd (_, y)) -> y
     | _ -> dynamic (push l (Fst (px.dynVal))))
  | Left x ->
    let px = recurse(x) in
    static (SSum (Left px)) (push l (Left px.dynVal))
  | Right x ->
    let px = recurse(x) in
    static (SSum (Right px)) (push l (Right px.dynVal))
  | App (f, x) ->
    let pf = recurse(f) in
    let px = recurse(x) in
    app pf px
  | Match (s, lcase, rcase) ->
    let ps = recurse(s) in
    let pl = recurse(lcase) in
    let pr = recurse(rcase) in
    (match ps.pStatic with
    | (Some (SSum (Left x))) -> app pl x
    | (Some (SSum (Right x))) -> app pr x
    | _ -> incTime curTime; dynamic (push l (Match (ps.dynVal, pl.dynVal, pr.dynVal))))
  | MkRef x ->
    let px = recurse(x) in
    static (SRef (ref (px, !curTime))) (push l (MkRef px.dynVal))
  | GetRef r ->
    let pr = recurse(r) in
    (match pr.pStatic with
     | Some (SRef { contents = (px, time) }) when !curTime == time -> px
     | _ -> dynamic (push l (GetRef pr.dynVal)) )
  | SetRef (r, v) ->
    let pr = recurse(r) in
    let pv = recurse(v) in
    (match pr.pStatic with
     | Some (SRef r) -> r := (pv, !curTime)
     | _ -> let _ = push l (SetRef (pr.dynVal, pv.dynVal)) in incTime curTime);
    static SUnit Unit
  | Unit -> static SUnit Unit
  | FromVar v -> e v
  | Let (var, v, body) -> peAux(curTime)(extend e var (recurse(v)))(l)(body)
  | Abs e -> static (SFun (fun l p ->
      { pStatic = p.pStatic; dynVal = push l p.dynVal })) (Abs e)

exception NotFound;;

let pe x =
  let
    ll = ref (fun x -> x)
  in
  let
    res = peAux(ref 0)(fun _ -> raise NotFound)(ll) x
  in
  (!ll) res.dynVal
