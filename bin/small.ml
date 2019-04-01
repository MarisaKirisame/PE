type var = Var of int

type term =
  | FromVar of var
  | Abs of (var * term)
  | App of (term * term)
  | Let of (var * term * term)
  | Int of int
  | Add of (term * term)
  | Mult of (term * term)
  | MkRef of term
  | GetRef of term
  | SetRef of (term * term)
  | MkProd of (term * term)
  | Zro of term
  | Fst of term
  | Unit
  | IfZero of (term * term * term)

type 'a env = int -> 'a

let extend e v x =
  function
  | i when i == v -> x
  | i -> e i

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
  | SInt of int
  | VRef of value ref
  | VProd of value * value
  | VSum of (value, value) sum
  | VUnit

let freshStoreId = genCounter()

type storeId = StoreId of int

type
  static =
  | SFun of (letList -> pValue -> pValue)
  | SInt of int
  | SRef of storeId
  | SProd of pValue * pValue
  | SSum of (pValue, pValue) sum
  | SUnit
and
  pValue =
  { pStatic: static option;
    dynVal: term }

let static s d = { pStatic = Some s; dynVal = d }

let staticInt i = static (SInt i) (Int i)

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
  | Int f -> staticInt f
  | Add (x, y) ->
    let px = recurse(x) in
    let py = recurse(y) in
    (match (px.pStatic, py.pStatic) with
    | (Some (SInt x), Some (SInt y)) -> staticInt (x + y)
    | _ -> dynamic (push l (Add (px.dynVal, py.dynVal))))
  | Mult (x, y) ->
    let px = recurse(x) in
    let py = recurse(y) in
    (match (px.pStatic, py.pStatic) with
     | (Some (SInt x), Some (SInt y)) -> staticInt (x * y)
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
  | App (f, x) ->
    let pf = recurse(f) in
    let px = recurse(x) in
    app pf px
  | MkRef x ->
    let px = recurse(x) in
    let id = freshStoreId() in
    curStore := extend (!curStore) id px;
    static (SRef (StoreId id)) (push l (MkRef px.dynVal))
  | GetRef r ->
    let pr = recurse(r) in
    (try (match pr.pStatic with
        | Some (SRef (StoreId s)) -> (!curStore) s
        | _ -> raise Not_found)
     with _ -> dynamic (push l (GetRef pr.dynVal)))
  | SetRef (r, v) ->
    let pr = recurse(r) in
    let pv = recurse(v) in
    let _ = push l (SetRef (pr.dynVal, pv.dynVal)) in
    (match pr.pStatic with
     | Some (SRef (StoreId s)) -> curStore := extend (!curStore) s pv
     | _ -> curStore := emptyStore);
    static SUnit Unit
  | Unit -> static SUnit Unit
  | FromVar (Var v) -> e v
  | Let (Var var, v, body) ->
    let pv = recurse(v) in
    pushVar l (Var var) pv.dynVal;
    peAux(curStore)(extend e var pv)(l)(body)
  | Abs (Var v, b) ->
    static
      (SFun (fun l p -> peAux(curStore)(extend e v p)(l)(b)))
      (push l (Abs (Var v,
                    withLetList (fun l ->
                        (peAux
                           (ref emptyStore)
                           (extend e v (dynamic (FromVar (Var v))))
                           l
                           b).dynVal))))
  | IfZero (i, z, nz) ->
    let pi = recurse(i) in
    match pi.pStatic with
    | Some (SInt 0) -> recurse(z)
    | Some (SInt _) -> recurse(nz)
    | _ -> dynamic (push l (IfZero (pi.dynVal,
                                    (peAux (ref emptyStore) e l z).dynVal,
                                    (peAux (ref emptyStore) e l nz).dynVal)))

let pe x = withLetList (fun l -> (peAux (ref emptyStore) emptyStore l x).dynVal)
