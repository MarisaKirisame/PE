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

let rec typeRepEq: type a b. (a typeRep * b typeRep) -> bool =
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
  | (SumRep _, _) -> false
  | (ProdRep (a, b), ProdRep (c, d)) -> typeRepEq (a, c) && typeRepEq (b, d)
  | (ProdRep _, _) -> false

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

type 'a env = int -> 'a

let extend e v x =
  function
  | i when i == v -> x
  | i -> e i

let rec typeInfer (tyEnv: dynType env): term -> dynType =
  function
  | Unit -> makeDynType UnitRep
  | Float _ -> makeDynType FloatRep

let genCounter() =
  let cnt = ref 0 in
  let gen() =
    let ret = !cnt in
    cnt := ret + 1;
    ret
  in
  gen

let freshVar = genCounter()

type letList = (term -> term) ref

let pushVar l v x =
  let lv = !l in
  l := (fun t -> lv(Let(v, x, t)))

let push l x =
  let v = Var(freshVar()) in
  pushVar l v x;
  FromVar v

type value =
  | VFun of (value -> value)
  | VFloat of float
  | VRef of value ref
  | VProd of value * value
  | VSum of (value, value) sum
  | VUnit

(*Our partial evaluator has almost the same value as the ordinary evaluator.
  the only problem is that reference has effect.

  So we reify the store, making the partial evaluator take a ref of the store.
  (It can also take store as input and pass one out ala state monad)

  Since duplication with effect is semantically incorrect, dynVal will hold only value.
  Computation must be pushed to a letList ref.
*)
let freshStoreId = genCounter()

type storeId = StoreId of int

type
  static =
  | SFun of (letList -> pValue -> pValue)
  | SFloat of float
  | SRef of storeId
  | SProd of pValue * pValue
  | SSum of (pValue, pValue) sum
  | SUnit
and
  pValue =
  { pStatic: static option;
    dynVal: term }

let static s d = { pStatic = Some s; dynVal = d }

let staticFloat f = static (SFloat f) (Float f)

let dynamic d = { pStatic = None; dynVal = d }

let emptyStore = fun _ -> raise Not_found

let withLetList f =
  let l = ref (fun x -> x) in
  let res = f l in
  (!l) res

let rec peAux(curStore: pValue env ref)(e: pValue env)(l : letList): term -> pValue =
  let recurse t = peAux curStore e l t in
  let app x y =
    match x.pStatic with
    | Some (SFun f) -> f l y
    | _ -> curStore := emptyStore; dynamic (push l (App (x.dynVal, y.dynVal)))
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
    | _ ->
      curStore := emptyStore;
      dynamic (push l (Match (ps.dynVal, pl.dynVal, pr.dynVal))))
  | MkRef x ->
    let px = recurse(x) in
    static (SRef (StoreId (freshStoreId()))) (push l (MkRef px.dynVal))
  | GetRef r ->
    let pr = recurse(r) in
    (try (match pr.pStatic with
        | Some (SRef (StoreId s)) -> (!curStore) s
        | _ -> raise Not_found)
    with _ -> dynamic (push l (GetRef pr.dynVal)))
 | SetRef (r, v) ->
    let pr = recurse(r) in
    let pv = recurse(v) in
    (match pr.pStatic with
     | Some (SRef (StoreId s)) -> curStore := extend (!curStore) s pv
     | _ -> let _ = push l (SetRef (pr.dynVal, pv.dynVal)) in curStore := emptyStore);
    static SUnit Unit
  | Unit -> static SUnit Unit
  | FromVar (Var v) -> e v
  | Let ((Var var), v, body) ->
    let pv = recurse(v) in
    pushVar l (Var var) pv.dynVal;
    peAux(curStore)(extend e var pv)(l)(body)
  | Abs ((Var v), t, b) ->
    static
      (SFun (fun l p -> peAux(curStore)(extend e v p)(l)(b)))
      (push l (Abs ((Var v), t,
                    withLetList (fun l ->
                        (peAux
                           (ref (!curStore))
                           (extend e v (dynamic (FromVar (Var v))))
                           l
                           b).dynVal))))

let pe x = withLetList (fun l -> (peAux (ref emptyStore) emptyStore l x).dynVal)

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

let lam t f = let v = Var (freshVar()) in Abs (v, t, f (FromVar v))

let let_ x f = let v = Var (freshVar()) in Let (v, x, f (FromVar v))

let m2 =
  let_
    (lam (makeDynType FloatRep) (fun x -> Add (x, x)))
    (fun dub -> (lam (makeDynType FloatRep) (fun x -> App (dub, x))))

let m8 =
  let_
    (lam (makeDynType FloatRep) (fun x -> Add (x, x)))
    (fun dub -> (lam (makeDynType FloatRep) (fun x -> App (dub, App (dub, App (dub, x))))))

let pem2 = pe m2
let pem8 = pe m8

(*fix later*)
let adType t = t

let seq l r =
  let_ l (fun _ -> r)

let addGrad g f =
  let_ g (fun g -> SetRef (g, Add (GetRef g, f)))

let updateBp bp action =
  let_
    (GetRef bp)
    (fun bpv -> (SetRef (bp,
                         lam (makeDynType UnitRep)
                           (fun _ -> seq action (App(bp, Unit))))))

let rec adAux bp = function
  | Unit -> Unit
  | Zro e -> Zro (adAux bp e)
  | Fst e -> Fst (adAux bp e)
  | MkProd (l, r) -> MkProd (adAux bp l, adAux bp r)
  | Left (e, t) -> Left (adAux bp e, adType t)
  | Right (t, e) -> Right (adType t, adAux bp e)
  | FromVar v -> FromVar v
  | App (f, x) -> App (adAux bp f, adAux bp x)
  | GetRef r -> GetRef (adAux bp r)
  | SetRef (r, v) -> SetRef (adAux bp r, adAux bp v)
  | MkRef e -> MkRef (adAux bp e)
  | Let (var, v, body) -> Let (var, adAux bp v, adAux bp body)
  | Abs (v, t, body) -> Abs (v, t, adAux bp body)
  | Match (s, l, r) -> Match (adAux bp s, adAux bp l, adAux bp r)
  | Float f -> MkProd (Float f, MkRef (Float 0.))
  | Add (l, r) ->
    let_ (adAux bp l)
      (fun lad -> let_ (adAux bp r)
          (fun rad -> let_ (MkRef (Float 0.))
              (fun g -> seq
                  (updateBp bp
                     (seq (addGrad (Fst lad) (GetRef g))
                        (addGrad (Fst rad) (GetRef g))))
                  (MkProd (Add (Zro lad, Zro rad), g)))))
  | Mult (l, r) ->
    let_ (adAux bp l)
      (fun lad -> let_ (adAux bp r)
          (fun rad -> let_ (MkRef (Float 0.))
              (fun g -> seq
                  (updateBp bp
                     (seq (addGrad (Fst lad) (Mult (Zro rad, GetRef g)))
                        (addGrad (Fst rad) (Mult (Zro lad, GetRef g)))))
                  (MkProd (Mult (Zro lad, Zro rad), g)))))

let rec multiAbs i t f =
  if i = 0
  then f []
  else
    let v = Var (freshVar()) in
    Abs (v, t, multiAbs (i - 1) t (fun x -> f (FromVar v :: x)))

let rec multiLet l f =
  match l with
  | [] -> f []
  | x :: xs ->
    let v = Var (freshVar()) in
    Let (v, x, multiLet xs (fun l -> f (FromVar v :: l)))

let rec multiApp f x =
  match x with
  | [] -> f
  | x :: xs -> multiApp (App (f, x)) xs

let rec hList =
  function
  | [] -> Unit
  | x :: xs -> MkProd (x, hList xs)

let initBp = MkRef (lam (makeDynType UnitRep) (fun _ -> Unit))

let ad i e =
  multiAbs
    i
    (makeDynType FloatRep)
    (fun l ->
       let_ initBp
         (fun bp -> let_ (adAux bp e)
             (fun ade -> multiLet (List.map (fun x -> MkProd (x, MkRef (Float 0.0))) l)
                 (fun l -> let_ (multiApp ade l)
                     (fun res -> seq (SetRef (Fst res, Float 1.0))
                         (seq (App (GetRef bp, Unit))
                            (MkProd (Zro res,
                                     hList (List.map (fun x -> GetRef (Fst x)) l)))))))))

let sad = ad 1 (lam (makeDynType FloatRep) (fun x -> Mult (x, x)))

(* After some manual inspection, this does indeed fuse away reference and closure.
 * However it generate tons of unused binding,
 * which can be removed by dead code elimination.
 * Note that escape analysis is needed to remove some dead code,
 * as they might update a dead reference.
 *)
let pesad = pe sad
