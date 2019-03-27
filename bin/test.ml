open PE.Common;;
open Trx;;
open Format;;
open Lazy;;

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

let print_var pp = function
  | Var i -> pp_print_string pp "x"; pp_print_int pp i

let print_bracket pp cont = pp_print_string pp "("; force cont; pp_print_string pp ")"

let rec print_term pp =
  let p_term t = print_term pp t in
  let p_bracket cont = print_bracket pp cont in
  let p_string str = pp_print_string pp str in
  let p_var v = print_var pp v in
  let p_space () = pp_print_space pp () in
  let k str = p_string str in
  let sk str = p_space (); p_string str in
  let ks str = p_string str; p_space () in
  let sks str = p_space (); p_string str; p_space () in
  function
  | Unit -> pp_print_string pp "()"
  | Float f -> pp_print_float pp f
  | FromVar v -> p_var v
  | Abs (v, _, t) -> p_bracket (lazy (p_string "\\"; p_var v; sks "->"; p_term t))
  | App (f, x) -> p_bracket (lazy (p_term f; p_space (); p_term x))
  | Let (var, v, b) -> p_bracket (lazy (
      ks "let"; p_var var; sks "=";
      p_term v; sks "in"; p_term b))
  | Add (l, r) -> p_bracket (lazy (p_term l; sks "+"; p_term r))
  | Mult (l, r) -> p_bracket (lazy (p_term l; sks "*"; p_term r))
  | MkRef r -> p_bracket (lazy (ks "ref"; p_term r))
  | MkProd (l, r) -> p_bracket (lazy (p_term l; ks ","; p_term r))
  | Zro e -> p_bracket (lazy (p_term e; k ".0"))
  | Fst e -> p_bracket (lazy (p_term e; k ".1"))
  | GetRef e -> p_bracket (lazy (k "!"; p_term e))
  | SetRef (r, v) -> p_bracket (lazy (p_term r; sks ":="; p_term v))
  | Left (x, _) -> p_bracket (lazy (ks "left"; p_term x))
  | Right (_, y) -> p_bracket (lazy (ks "right"; p_term y))
  | Match (s, l, r) -> p_bracket (lazy (ks "match"; p_term s; p_space(); p_term l; p_space(); p_term r));;

#install_printer print_term;;

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
                           (ref (emptyStore))
                           (extend e v (dynamic (FromVar (Var v))))
                           l
                           b).dynVal))))

let pe x = withLetList (fun l -> (peAux (ref emptyStore) emptyStore l x).dynVal)

let rec wellform_aux (set: int -> bool) =
  let bind (Var v) e =
    if set v
    then false
    else wellform_aux (fun i -> if i == v then true else set v) e in
  function
  | FromVar _ -> true
  | Unit -> true
  | Float _ -> true
  | Add (l, r) -> wellform_aux set l && wellform_aux set r
  | Mult (l, r) -> wellform_aux set l && wellform_aux set r
  | MkRef e -> wellform_aux set e
  | GetRef e -> wellform_aux set e
  | SetRef (r, e) -> wellform_aux set r && wellform_aux set e
  | Zro e -> wellform_aux set e
  | Fst e -> wellform_aux set e
  | MkProd (l, r) -> wellform_aux set l && wellform_aux set r
  | Left (e, _) -> wellform_aux set e
  | Right (_, e) -> wellform_aux set e
  | Match (s, l, r) -> wellform_aux set s && wellform_aux set l && wellform_aux set r
  | App (f, x) -> wellform_aux set f && wellform_aux set x
  | Abs (v, _, b) -> bind v b
  | Let (v, _, b) -> bind v b

let wellform = wellform_aux (fun _ -> false)

let false =
  let v = Var (freshVar()) in
  wellform (Let (v, Unit, Let (v, Unit, FromVar v)))

let peref = pe (GetRef (MkRef (Float 1.0)))

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
                           (fun _ -> seq action (App(bpv, Unit))))))

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

let iad = ad 1 (lam (makeDynType FloatRep) (fun x -> x))

let peiad = pe iad

let sad = ad 1 (lam (makeDynType FloatRep) (fun x -> Mult (x, x)))

(* After some manual inspection, this does indeed fuse away reference and closure.
 * However it generate tons of unused binding,
 * which can be removed by dead code elimination.
 * Note that escape analysis is needed to remove some dead code,
 * as they might update a dead reference.
 *)
let pesad = pe sad
