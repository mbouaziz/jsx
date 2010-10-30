
open LambdaJS.Prelude
open MyPervasives
open SymbolicState
open JS.Syntax

module ResHelpers =
struct
  let resl_v s v = [{ s with res = SValue v }]
  let resl_rv_if s v_c rv_t rv_e =
    let sl = match PathCondition.add (PredVal v_c) s.pc, rv_t with
    | None, _ -> []
    | Some pc, SValue _ -> [{ s with pc ; res = rv_t }]
    | Some pc, SExn e -> [{ s with pc ; exn = Some e ; res = rv_t }]
    in match PathCondition.add (PredNotVal v_c) s.pc, rv_e with
    | None, _ -> sl
    | Some pc, SValue _ -> { s with pc ; res = rv_e }::sl
    | Some pc, SExn e -> { s with pc ; exn = Some e ; res = rv_e }::sl
  let resl_v_if s v_c v_t v_e = resl_rv_if s v_c (SValue v_t) (SValue v_e)
  let res_e s e = { s with exn = Some e ; res = SExn e }
  let resl_e s e = [res_e s e]
  let resl_io s io = [{ s with io }]
  let resl_f s f = resl_io s (f s.io)
  let err s msg =
    if !Options.opt_fatal then
      failwith msg
    else
      res_e s (SError msg)
  let errl s msg = [err s msg]
end

open ResHelpers

let state_pretty_error ~pos s = match s with
  | { res = SExn (SError msg) ; _ } -> err s (sprintf "%s\n%s" (pretty_position pos) msg)
  | _ -> s


let (|^) sl f =
  let f' s = match s.exn with
  | None -> f s |> List.map (fun s' -> match s'.exn with
			     | None -> { s' with res = SValue (s.res, s'.res) }
			     | Some e -> { s' with res = SExn e })
  | Some e -> [{ s with res = SExn e }]
  in
  sl |> List.map f' |> List.flatten

let xdelta2 f1 f2 g sl =
  let g' s = match s.res with
  | SValue (v1, v2) -> g v1 v2 s
  | SExn _ as res -> [{ s with res }]
  in
  sl |> List.map f1 |> List.flatten |^ f2 |> List.map g' |> List.flatten

let bool b = SConst (CBool b)
let num f = SConst (CNum f)
let str x = SConst (CString x)

let to_float x s = match x with
| SConst (CInt n) -> resl_v s (float_of_int n)
| SConst (CNum n) -> resl_v s n
| _ -> resl_e s (SThrow (str (sprintf "expected number, got %s" (ToString.svalue s x))))


let float_str = LambdaJS.Delta.float_str


(* Unary operators *)

let prim_to_str v s = match v with
| SConst c ->
    let resl_str str_v = resl_v s (str str_v) in
    begin match c with
    | CUndefined -> resl_str "undefined"
    | CNull -> resl_str "null"
    | CString x -> resl_str x
    | CNum n -> resl_str (float_str n)
    | CInt n -> resl_str (string_of_int n)
    | CBool b -> resl_str (string_of_bool b)
    | CRegexp _ -> errl s "Error [prim_to_str] regexp NYI"
    end
| SId _ -> resl_v s (SOp1("prim->str", v))
| _ -> resl_e s (SThrow (str "prim_to_str"))

let is_callable v s = match v with
| SHeapLabel label ->
    let { attrs ; _ } = SHeap.find label s.heap in
    begin match IdMap.find_opt "code" attrs with
    | Some (SClosure _) -> resl_v s strue
    | _ -> resl_v s sfalse
    end
| SId _ -> resl_v s (SOp1("is-callable", v))
| _ -> resl_v s sfalse

let is_primitive v s = match v with
| SConst _ -> resl_v s strue
| SId _ -> resl_v_if s (SOp1("primitive?", v)) strue sfalse
| _ -> resl_v s sfalse

let print v s = resl_f s (SIO.print v)

let symbol v s = match v with
| SConst (CString sid) -> resl_v s (SId (SId.from_string sid))
| SConst (CInt n) -> resl_v s (SId (SId.from_string (string_of_int n)))
| _ -> errl s "Error [symbol] Please, don't do stupid thing with symbolic id"


let err_op1 ~op _ s = errl s (sprintf "Error [xeval] No implementation of unary operator \"%s\"" op)

let op1 ~pos op v s =
  let f = match op with
  | "is-callable" -> is_callable
  | "prim->str" -> prim_to_str
  | "primitive?" -> is_primitive
  | "print" -> print
  | "symbol" -> symbol
  | op -> err_op1 ~op
  in
  s |> f v |> List.map (state_pretty_error ~pos)

(* Binary operators *)

let arith_lt x y s =
  let make x y s = resl_v s (bool (x < y)) in
  xdelta2 (to_float x) (to_float y) make [s]

let err_op2 ~op _ _ s = errl s (sprintf "Error [xeval] No implementation of binary operator \"%s\"" op)

let op2 ~pos op v1 v2 s =
  let f = match op with
  | "<" -> arith_lt
  | op -> err_op2 ~op
  in
  s |> f v1 v2 |> List.map (state_pretty_error ~pos)

(* Ternary operators *)

let err_op3 ~op _ _ _ s = errl s (sprintf "Error [xeval] No ternary operators yet, so what's this \"%s\"" op)

let op3 ~pos op v1 v2 v3 s =
  let f = match op with
  | op -> err_op3 ~op
  in
  s |> f v1 v2 v3 |> List.map (state_pretty_error ~pos)
