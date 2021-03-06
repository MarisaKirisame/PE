type ('a, 'b) sum = Left of 'a | Right of 'b

type var = Var of int

type term =
  | Let of (var * term * term)
  | FromVar of var
  | Abs of (var * term)
  | App of (term * term)
  | Unit
  | Int of int
  | Add of (term * term)
  | Mult of (term * term)
  | IfZero of (term * term * term)
  | MkProd of (term * term)
  | Zro of term
  | Fst of term
  | MkRef of term
  | SetRef of (term * term)
  | GetRef of term
  | TLeft of term
  | TRight of term
  | Match of term * term * term

type 'a env = int -> 'a

let emptyStore _ = raise Not_found

let extend e v x = function i when i == v -> x | i -> e i

let genCounter () =
  let cnt = ref 0 in
  let gen () =
    let ret = !cnt in
    cnt := ret + 1 ;
    ret
  in
  gen

let freshVar = genCounter ()

type value =
  | VFun of (value -> value)
  | VUnit
  | VInt of int
  | VProd of value * value
  | VRef of value ref
  | VSum of (value, value) sum

(* The standard metacircular evaluator. *)
let rec evalAux (e : value env) : term -> value =
  let recurse t = evalAux e t in
  let app x y = match x with VFun f -> f y in
  function
  | Let (Var var, v, body) ->
      let rv = recurse v in
      evalAux (extend e var rv) body
  | FromVar (Var v) -> e v
  | Abs (Var v, b) -> VFun (fun p -> evalAux (extend e v p) b)
  | App (f, x) -> app (recurse f) (recurse x)
  | Unit -> VUnit
  | Int f -> VInt f
  | Add (x, y) -> (
      let rx = recurse x in
      let ry = recurse y in
      match (rx, ry) with VInt x, VInt y -> VInt (x + y) )
  | Mult (x, y) -> (
      let rx = recurse x in
      let ry = recurse y in
      match (rx, ry) with VInt x, VInt y -> VInt (x * y) )
  | IfZero (i, z, nz) -> (
    match recurse i with VInt 0 -> recurse z | VInt _ -> recurse nz )
  | MkProd (x, y) ->
      let rx = recurse x in
      let ry = recurse y in
      VProd (rx, ry)
  | Zro x -> ( match recurse x with VProd (x, _) -> x )
  | Fst x -> ( match recurse x with VProd (_, y) -> y )
  | MkRef x -> VRef (ref (recurse x))
  | SetRef (r, v) -> (
      let vr = recurse r in
      let vv = recurse v in
      match vr with VRef r ->
        r := vv ;
        VUnit )
  | GetRef r -> ( match recurse r with VRef r -> !r )
  | TLeft x -> VSum (Left (recurse x))
  | TRight x -> VSum (Right (recurse x))
  | Match (s, lcase, rcase) -> (
      let ps = recurse s in
      let pl = recurse lcase in
      let pr = recurse rcase in
      match ps with VSum (Left x) -> app pl x | VSum (Right x) -> app pr x )

let eval = evalAux emptyStore

let freshStoreId = genCounter ()

type storeId = StoreId of int

type rValue =
  | RFun of (rValue -> rValue)
  | RUnit
  | RInt of int
  | RProd of rValue * rValue
  | RRef of storeId
  | RSum of (rValue, rValue) sum

(* The evaluator, but with the store reified -
   it is now represented and manipulated explicitly. *)
let rec rEvalAux (curStore : rValue env ref) (e : rValue env) : term -> rValue
    =
  let recurse t = rEvalAux curStore e t in
  let app x y = match x with RFun f -> f y in
  function
  | Let (Var var, v, body) ->
      let rv = recurse v in
      rEvalAux curStore (extend e var rv) body
  | FromVar (Var v) -> e v
  | Abs (Var v, b) -> RFun (fun p -> rEvalAux curStore (extend e v p) b)
  | App (f, x) -> app (recurse f) (recurse x)
  | Unit -> RUnit
  | Int f -> RInt f
  | Add (x, y) -> (
      let rx = recurse x in
      let ry = recurse y in
      match (rx, ry) with RInt x, RInt y -> RInt (x + y) )
  | Mult (x, y) -> (
      let rx = recurse x in
      let ry = recurse y in
      match (rx, ry) with RInt x, RInt y -> RInt (x * y) )
  | IfZero (i, z, nz) -> (
    match recurse i with RInt 0 -> recurse z | RInt _ -> recurse nz )
  | MkProd (x, y) ->
      let rx = recurse x in
      let ry = recurse y in
      RProd (rx, ry)
  | Zro x -> ( match recurse x with RProd (x, _) -> x )
  | Fst x -> ( match recurse x with RProd (_, y) -> y )
  | MkRef x ->
      let rx = recurse x in
      let id = freshStoreId () in
      curStore := extend !curStore id rx ;
      RRef (StoreId id)
  | SetRef (r, v) ->
      let rr = recurse r in
      let rv = recurse v in
      (match rr with RRef (StoreId s) -> curStore := extend !curStore s rv) ;
      RUnit
  | GetRef r -> ( match recurse r with RRef (StoreId s) -> !curStore s )
  | TLeft x -> RSum (Left (recurse x))
  | TRight x -> RSum (Right (recurse x))
  | Match (s, lcase, rcase) -> (
      let rs = recurse s in
      let rl = recurse lcase in
      let rr = recurse rcase in
      match rs with RSum (Left x) -> app rl x | RSum (Right x) -> app rr x )

let rEval = rEvalAux (ref emptyStore) emptyStore

(* letList bind complex expression to a simple variable,
   so one can construct some complex expression, and use it
   as a variable by storing a binding in the letlist. *)
type letList = (term -> term) ref

let withLetList f =
  let l = ref (fun x -> x) in
  let res = f l in
  !l res

let pushVar l v x =
  let lv = !l in
  l := fun t -> lv (Let (v, x, t))

let push l x =
  let v = Var (freshVar ()) in
  pushVar l v x ; FromVar v

(* Using the letList to do anf conversion by 'running' the program in compile time. *)
let rec anfAux (l : letList) : term -> term =
  let recurse t = anfAux l t in
  function
  | Let (Var var, v, body) ->
      pushVar l (Var var) (recurse v) ;
      recurse body
  | FromVar (Var v) -> FromVar (Var v)
  | Abs (Var v, b) -> push l (Abs (Var v, withLetList (fun l -> anfAux l b)))
  | App (f, x) -> push l (App (recurse f, recurse x))
  | Unit -> Unit
  | Int f -> Int f
  | Add (x, y) -> push l (Add (recurse x, recurse y))
  | Mult (x, y) -> push l (Mult (recurse x, recurse y))
  | IfZero (i, z, nz) -> push l (IfZero (recurse i, recurse z, recurse nz))
  | MkProd (x, y) -> push l (MkProd (recurse x, recurse y))
  | Zro x -> push l (Zro (recurse x))
  | Fst x -> push l (Fst (recurse x))
  | MkRef x -> push l (MkRef (recurse x))
  | SetRef (r, v) -> push l (SetRef (recurse r, recurse v))
  | GetRef r -> push l (GetRef (recurse r))
  | TLeft x -> push l (TLeft (recurse x))
  | TRight x -> push l (TRight (recurse x))
  | Match (s, lcase, rcase) ->
      push l (Match (recurse s, recurse lcase, recurse rcase))

let anf x = withLetList (fun l -> anfAux l x)

(* The partially-static value is just like value with store reified, but might be empty,
   and always come with a term that is semantically equivalent to the original expression.
   The term must not be a compound expression as it duplicate computation and effect. *)
type sValue =
  | SFun of (letList -> pValue -> pValue)
  | SUnit
  | SInt of int
  | SProd of pValue * pValue
  | SRef of storeId
  | SSum of (pValue, pValue) sum

and pValue = {pStatic: sValue option; dynVal: term}

let static s d = {pStatic= Some s; dynVal= d}

let staticInt i = static (SInt i) (Int i)

let dynamic d = {pStatic= None; dynVal= d}

(* rEval on the static part(if exist), anf on the dynamic part.
   Will try to recurse aggressively to optimize even with value/control unknown.
   Must clear curStore when unknown code is executed, as the store is contaminated. *)
let rec peAux (curStore : pValue env ref) (e : pValue env) (l : letList) :
    term -> pValue =
  let recurse t = peAux curStore e l t in
  let app x y =
    match x.pStatic with
    | Some (SFun f) -> f l y
    | _ ->
        curStore := emptyStore ;
        dynamic (push l (App (x.dynVal, y.dynVal)))
  in
  function
  | Let (Var var, v, body) ->
      let pv = recurse v in
      pushVar l (Var var) pv.dynVal ;
      peAux curStore (extend e var pv) l body
  | FromVar (Var v) -> e v
  | Abs (Var v, b) ->
      static
        (SFun (fun l p -> peAux curStore (extend e v p) l b))
        (push l
           (Abs
              ( Var v
              , withLetList (fun l ->
                    (peAux (ref emptyStore)
                       (extend e v (dynamic (FromVar (Var v))))
                       l b)
                      .dynVal ) )))
  | App (f, x) -> app (recurse f) (recurse x)
  | Unit -> static SUnit Unit
  | Int f -> staticInt f
  | Add (x, y) -> (
      let px = recurse x in
      let py = recurse y in
      match (px.pStatic, py.pStatic) with
      | Some (SInt x), Some (SInt y) -> staticInt (x + y)
      | _ -> dynamic (push l (Add (px.dynVal, py.dynVal))) )
  | Mult (x, y) -> (
      let px = recurse x in
      let py = recurse y in
      match (px.pStatic, py.pStatic) with
      | Some (SInt x), Some (SInt y) -> staticInt (x * y)
      | _ -> dynamic (push l (Mult (px.dynVal, py.dynVal))) )
  | IfZero (i, z, nz) -> (
      let pi = recurse i in
      match pi.pStatic with
      | Some (SInt 0) -> recurse z
      | Some (SInt _) -> recurse nz
      | _ ->
          let res =
            dynamic
              (push l
                 (IfZero
                    ( pi.dynVal
                    , (peAux (ref !curStore) e l z).dynVal
                    , (peAux (ref !curStore) e l nz).dynVal )))
          in
          curStore := emptyStore ;
          res )
  | MkProd (x, y) ->
      let px = recurse x in
      let py = recurse y in
      static (SProd (px, py)) (push l (MkProd (px.dynVal, py.dynVal)))
  | Zro x -> (
      let px = recurse x in
      match px.pStatic with
      | Some (SProd (x, _)) -> x
      | _ -> dynamic (push l (Zro px.dynVal)) )
  | Fst x -> (
      let px = recurse x in
      match px.pStatic with
      | Some (SProd (_, y)) -> y
      | _ -> dynamic (push l (Fst px.dynVal)) )
  | MkRef x ->
      let px = recurse x in
      let id = freshStoreId () in
      curStore := extend !curStore id px ;
      static (SRef (StoreId id)) (push l (MkRef px.dynVal))
  | SetRef (r, v) ->
      let pr = recurse r in
      let pv = recurse v in
      let _ = push l (SetRef (pr.dynVal, pv.dynVal)) in
      ( match pr.pStatic with
      | Some (SRef (StoreId s)) -> curStore := extend !curStore s pv
      | _ -> curStore := emptyStore ) ;
      static SUnit Unit
  | GetRef r -> (
      let pr = recurse r in
      try
        match pr.pStatic with
        | Some (SRef (StoreId s)) -> !curStore s
        | _ -> raise Not_found
      with _ -> dynamic (push l (GetRef pr.dynVal)) )
  | TLeft x ->
      let px = recurse x in
      static (SSum (Left px)) (push l (TLeft px.dynVal))
  | TRight x ->
      let px = recurse x in
      static (SSum (Right px)) (push l (TRight px.dynVal))
  | Match (s, lcase, rcase) -> (
      let ps = recurse s in
      let pl = recurse lcase in
      let pr = recurse rcase in
      match ps.pStatic with
      | Some (SSum (Left x)) -> app pl x
      | Some (SSum (Right x)) -> app pr x
      | _ ->
          curStore := emptyStore ;
          dynamic (push l (Match (ps.dynVal, pl.dynVal, pr.dynVal))) )

let pe x = withLetList (fun l -> (peAux (ref emptyStore) emptyStore l x).dynVal)
