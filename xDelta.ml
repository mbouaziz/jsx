
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

let print v s = [{ s with io = SIO.print v s.io }]

let err_op1 ~pos ~op _ s = errl s (sprintf "%s\nError [xeval] No implementation of unary operator \"%s\"" (pretty_position pos) op)

let op1 ~pos = function
  | "print" -> print
  | op -> err_op1 ~pos ~op

(* Binary operators *)

let err_op2 ~pos ~op _ _ s = errl s (sprintf "%s\nError [xeval] No implementation of binary operator \"%s\"" (pretty_position pos) op)

let op2 ~pos = function
  | op -> err_op2 ~pos ~op

(* Ternary operators *)

let err_op3 ~pos ~op _ _ _ s = errl s (sprintf "%s\nError [xeval] No ternary operators yet, so what's this \"%s\"" (pretty_position pos) op)

let op3 ~pos = function
  | op -> err_op3 ~pos ~op
