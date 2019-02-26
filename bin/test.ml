open PE.Common;;
open Trx;;

type var = Var of int

type 'a typeRep =
  | FloatRep: float typeRep
  | UnitRep: unit typeRep
  | ArrowRep: ('a typeRep * 'b typeRep) -> ('a -> 'b) typeRep
  | RefRep: 'a typeRep -> 'a ref typeRep
  | SumRep: ('a typeRep * 'b typeRep) -> ('a, 'b) sum typeRep
  | ProdRep: ('a typeRep * 'b typeRep) -> ('a * 'b) typeRep

type 'a dynTypeAux = { useDynType: 't. 't typeRep -> 'a }
type dynType = { extractType: 'a. ('a dynTypeAux) -> 'a }

let makeDynType t = { extractType = fun dtx -> dtx.useDynType t }

let typeRepEq(type a)(type b): (a typeRep * b typeRep) -> bool =
  function
  | (FloatRep, FloatRep) -> true
  | (FloatRep, _) -> false
  | (UnitRep, UnitRep) -> true
  | (UnitRep, _) -> false
  | (ArrowRep (a, b), ArrowRep (c, d)) -> typeRepEq (a, c) && typeRepEq (b, d)
  | (ArrowRep _, _) -> false
  | (RefRep a, RefRep b) -> typeRepEq (a, b)
  | (RefRep _, _) -> false
  | (SumRep (a, b), SumRep (c, d)) -> typeRepEq (a, c) && typeRepEq (b, d)
  | (ProdRep (a, b), ProdRep (c, d)) -> typeRepEq (a, c) && typeRepEq (b, d)

type term =
  | FromVar of var
  | Abs of (var * dynType * term)
  | App of (term * term)
  | Let of (var * term * term)
  | Float of float
  | Add of (term * term)
  | Mult of (term * term)
  | MkRef of term
  | GetRef of term
  | SetRef of (term * term)
  | MkProd of (term * term)
  | Zro of term
  | Fst of term
  | Left of (term * dynType)
  | Right of (dynType * term)
  | Match of term * term * term
  | Unit

type 'a env = var -> 'a

let extend e (Var v) x =
  function
  | Var i when i == v -> x
  | i -> e i

let rec typeInfer (tyEnv: dynType env): term -> dynType =
  function
  | Unit -> makeDynType UnitRep
  | Float _ -> makeDynType FloatRep

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
  | VFloat of float
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
  | SFloat of float
  | SRef of (pValue * time) ref
  | SProd of pValue * pValue
  | SSum of (pValue, pValue) sum
  | SUnit
and
  pValue =
  { pStatic: static option;
    dynVal: term }

let fresh: int ref = ref 0

let incTime x =
  x := (!x) + 1

let static s d = { pStatic = Some s; dynVal = d }

let staticFloat f = static (SFloat f) (Float f)

let dynamic d = { pStatic = None; dynVal = d }

let rec peAux(curTime: time ref)(e: pValue env)(l : letList): term -> pValue =
  let recurse = peAux curTime e l in
  let app x y =
    match x.pStatic with
    | Some (SFun f) -> f l y
    | _ -> incTime curTime; dynamic (push l (App (x.dynVal, y.dynVal)))
  in
  function
  | Float f -> staticFloat f
  | Add (x, y) ->
    let px = recurse(x) in
    let py = recurse(y) in
    (match (px.pStatic, py.pStatic) with
    | (Some (SFloat x), Some (SFloat y)) -> staticFloat (x +. y)
    | _ -> dynamic (push l (Add (px.dynVal, py.dynVal))))
  | Mult (x, y) ->
    let px = recurse(x) in
    let py = recurse(y) in
    (match (px.pStatic, py.pStatic) with
     | (Some (SFloat x), Some (SFloat y)) -> staticFloat (x *. y)
     | _ -> dynamic (push l (Mult (px.dynVal, py.dynVal))))
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
  | Left (x, t) ->
    let px = recurse(x) in
    static (SSum (Left px)) (push l (Left (px.dynVal, t)))
  | Right (t, x) ->
    let px = recurse(x) in
    static (SSum (Right px)) (push l (Right (t, px.dynVal)))
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
  | Abs (v, t, b) ->
    static
      (SFun (fun l p ->
           let res = peAux(curTime)(extend e v p)(l)(b) in
           { pStatic = res.pStatic; dynVal = push l res.dynVal }))
      (Abs (v, t, b))

exception NotFound;;

let pe x =
  let
    ll = ref (fun x -> x)
  in
  let
    res = peAux(ref 0)(fun _ -> raise NotFound)(ll) x
  in
  (!ll) res.dynVal

type dynCode = { extract : 'a . 'a typeRep -> 'a code }

exception TypeError;;

let dynFloat (f: float): dynCode =
  let x (type ty) (t: ty typeRep) : ty code =
    match t with
    | FloatRep -> .<f>.
    | _ -> raise TypeError
  in
  { extract = x }

let dynUnit: dynCode =
  let x (type ty) (t: ty typeRep) : ty code =
    match t with
    | UnitRep -> .<()>.
    | _ -> raise TypeError
  in
  { extract = x }

let rec compile: term -> dynCode =
  function
  | Float f -> dynFloat f
  | Unit -> dynUnit
