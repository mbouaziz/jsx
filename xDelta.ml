
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
  let res_e ~pos s ev =
    let e = (pos, s.callstack), ev in
    { s with exn = Some e ; res = SExn e }
  let resl_e ~pos s e = [res_e ~pos s e]
  let resl_io s io = [{ s with io }]
  let resl_f s f = resl_io s (f s.io)
  let err ~pos s msg =
    if !Options.opt_fatal then
      failwith msg
    else
      res_e ~pos s (SError msg)
  let errl ~pos s msg = [err ~pos s msg]

  module Mk =
  struct
    let bool b = SConst (CBool b)
    let int i = SConst (CInt i)
    let num f = SConst (CNum f)
    let str x = SConst (CString x)
    let sop1 o v = SSymb (SOp1(o, v))
    let sop2 o v1 v2 = SSymb (SOp2(o, v1, v2))
    let sop3 o v1 v2 v3 = SSymb (SOp3(o, v1, v2, v3))
    let sapp v vl = SSymb (SApp(v, vl))
    let sid id = SSymb (SId id)
    let serr ~pos s msg = (pos, s.callstack), SError msg
    let sthrow ~pos s msg = (pos, s.callstack), SThrow msg
    let sbreak ~pos s l v = (pos, s.callstack), SBreak (l, v)
  end

  open Mk

  let resl_undef s = resl_v s sundefined
  let resl_bool s b = resl_v s (bool b)
  let resl_int s i = resl_v s (int i)
  let resl_num s n = resl_v s (num n)
  let resl_str s x = resl_v s (str x)

  let throwl ~pos s v = resl_e ~pos s (SThrow v)
  let throwl_str ~pos s msg = throwl ~pos s (str msg)
end

open ResHelpers
open Mk

let state_pretty_error ~pos s = match s with
  | { res = SExn ((_, cs), ev) ; _ } -> { s with res = SExn ((pos, cs), ev) }
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

let to_float x s = match x with
| SConst (CInt n) -> resl_v s (float_of_int n)
| SConst (CNum n) -> resl_v s n
| _ -> throwl_str ~pos:dummy_pos s (sprintf "expected number, got %s" (ToString.svalue s x))


let float_str = LambdaJS.Delta.float_str


(* Unary operators *)

let assume v s =
  match PathCondition.add_assumption (PredVal v) s.pc with
  | None -> errl ~pos:dummy_pos s "This assumption is surely false!"
  | Some pc -> [{ s with res = SValue strue; pc }]

let fail v s = resl_bool s false (* no such thing in my implementation *)

let is_callable v s = match v with
| SHeapLabel label ->
    let { attrs ; _ } = SHeap.find label s.heap in
    begin match IdMap.find_opt "code" attrs with
    | Some (SClosure _) -> resl_v s strue
    | _ -> resl_v s sfalse
    end
| SSymb _ -> resl_v s (sop1 "is-callable" v)
| _ -> resl_v s sfalse

let prim_to_num v s = match v with
| SConst c ->
    begin match c with
    | CUndefined -> resl_num s nan
    | CNull
    | CBool false -> resl_num s 0.0
    | CBool true -> resl_num s 1.0
    | CNum n -> resl_num s n
    | CInt i -> resl_num s (float_of_int i)
    | CString x -> resl_num s (try float_of_string x with Failure "float_of_string" -> nan)
    | CRegexp _ -> errl ~pos:dummy_pos s "prim_to_num of regexp"
    end
| SSymb _ -> resl_v s (sop1 "prim->num" v)
| _ -> throwl_str ~pos:dummy_pos s "prim_to_num"

let prim_to_str v s = match v with
| SConst c ->
    begin match c with
    | CUndefined -> resl_str s "undefined"
    | CNull -> resl_str s "null"
    | CString x -> resl_str s x
    | CNum n -> resl_str s (float_str n)
    | CInt n -> resl_str s (string_of_int n)
    | CBool b -> resl_str s (string_of_bool b)
    | CRegexp _ -> errl ~pos:dummy_pos s "Error [prim_to_str] regexp NYI"
    end
| SSymb _ -> resl_v s (sop1 "prim->str" v)
| _ -> throwl_str ~pos:dummy_pos s "prim_to_str"

let is_primitive v s = match v with
| SConst _ -> resl_v s strue
| SSymb _ -> resl_v s (sop1 "primitive?" v)
| _ -> resl_v s sfalse

let print v s = resl_f s (SIO.print v)

let symbol v s = match v with
| SConst (CString id) -> resl_v s (sid (SId.from_string id))
| SConst (CInt n) -> resl_v s (sid (SId.from_string (string_of_int n)))
| _ -> errl ~pos:dummy_pos s "Error [symbol] Please, don't do stupid things with symbolic id"

let typeof v s = match v with
| SConst c ->
    begin match c with
    | CUndefined -> resl_str s "undefined"
    | CNull -> resl_str s "null"
    | CString _ -> resl_str s "string"
    | CNum _
    | CInt _ -> resl_str s "number"
    | CBool _ -> resl_str s "boolean"
    | CRegexp _ -> errl ~pos:dummy_pos s "Error [typeof] regexp NYI"
    end
| SHeapLabel _ -> resl_str s "object"
| SClosure _ -> resl_str s "lambda"
| SSymb _ -> resl_v s (sop1 "typeof" v)

let err_op1 ~op _ s = errl ~pos:dummy_pos s (sprintf "Error [xeval] No implementation of unary operator \"%s\"" op)

let op1 ~pos op v s =
  let f = match op with
  | "assume" -> assume
  | "fail?" -> fail
  | "is-callable" -> is_callable
  | "prim->num" -> prim_to_num
  | "prim->str" -> prim_to_str
  | "primitive?" -> is_primitive
  | "print" -> print
  | "symbol" -> symbol
  | "typeof" -> typeof
  | op -> err_op1 ~op
  in
  s |> f v |> List.map (state_pretty_error ~pos)

(* Binary operators *)

let arith op2_op i_op f_op v1 v2 s = match v1, v2 with
| SConst (CInt i1), SConst (CInt i2) -> resl_int s (i_op i1 i2)
| SConst (CNum f1), SConst (CNum f2) -> resl_num s (f_op f1 f2)
| SConst (CNum f1), SConst (CInt i2) -> resl_num s (f_op f1 (float_of_int i2))
| SConst (CInt i1), SConst (CNum f2) -> resl_num s (f_op (float_of_int i1) f2)
| SSymb _, _
| _, SSymb _ -> resl_v s (sop2 op2_op v1 v2)
| _ -> throwl_str ~pos:dummy_pos s "arithmetic operator"

let arith_sum v1 v2 s = arith "+" (+) (+.) v1 v2 s

let arith_sub v1 v2 s = arith "-" (-) (-.) v1 v2 s

let arith_mul v1 v2 s = arith "*" ( * ) ( *. ) v1 v2 s

let arith0 op2_op i_op f_op def v1 v2 s = match v2 with
| SConst (CInt 0)
| SConst (CNum 0.0) -> resl_num s def (* Simplified: no thrown error if v1 is not ok *)
| SSymb _ -> resl_rv_if s (sop2 "=" v2 (num 0.0)) (SValue (num def)) (SValue (sop2 op2_op v1 v2))
| _ -> arith op2_op i_op f_op v1 v2 s

let arith_div v1 v2 s = arith0 "/" (/) (/.) infinity v1 v2 s

let arith_mod v1 v2 s = arith0 "%" (mod) mod_float nan v1 v2 s

let arith_lt v1 v2 s =
  let make v1 v2 s = resl_v s (bool (v1 < v2)) in
  xdelta2 (to_float v1) (to_float v2) make [s]

let abs_eq v1 v2 s = match v1, v2 with
  (* TODO: check if it's ok with null, undefined, nan, +/- 0.0, ... *)
| v1, v2 when v1 == v2 || v1 = v2 -> resl_bool s true
| SSymb _, _
| _, SSymb _ -> resl_v s (sop2 "abs=" v1 v2)
| SConst c1, SConst c2 ->
    let b = match c1, c2 with
    | CNull, CUndefined
    | CUndefined, CNull -> true
    | CString x, CNum n
    | CNum n, CString x -> (try n = float_of_string x with Failure "float_of_string" -> false)
    | CString x, CInt n
    | CInt n, CString x -> (try float_of_int n = float_of_string x with Failure _ -> false)
    | CNum n, CBool b
    | CBool b, CNum n -> n = (if b then 1.0 else 0.0)
    | CInt n, CBool b
    | CBool b, CInt n -> n = (if b then 1 else 0)
    | CNum f, CInt i
    | CInt i, CNum f -> float_of_int i = f
    | _ -> false
    in resl_bool s b
| _ -> throwl_str ~pos:dummy_pos s "expected primitive constant"

let stx_eq v1 v2 s = match v1, v2 with
  (* TODO: check if it's ok with null, undefined, nan, +/- 0.0, ... *)
| v1, v2 when v1 == v2 || v1 = v2 -> resl_bool s true 
| SConst (CNum n), SConst (CInt i)
| SConst (CInt i), SConst (CNum n) -> resl_bool s (float_of_int i = n)
| SSymb _, _
| _, SSymb _ -> resl_v s (sop2 "stx=" v1 v2)
| _, _ -> resl_bool s false

let err_op2 ~op _ _ s = errl ~pos:dummy_pos s (sprintf "Error [xeval] No implementation of binary operator \"%s\"" op)

let op2 ~pos op v1 v2 s =
  let f = match op with
  | "+" -> arith_sum
  | "-" -> arith_sub
  | "*" -> arith_mul
  | "/" -> arith_div
  | "%" -> arith_mod
  | "<" -> arith_lt
  | "abs=" -> abs_eq
  | "stx=" -> stx_eq
  | op -> err_op2 ~op
  in
  s |> f v1 v2 |> List.map (state_pretty_error ~pos)

(* Ternary operators *)

let err_op3 ~op _ _ _ s = errl ~pos:dummy_pos s (sprintf "Error [xeval] No ternary operators yet, so what's this \"%s\"" op)

let op3 ~pos op v1 v2 v3 s =
  let f = match op with
  | op -> err_op3 ~op
  in
  s |> f v1 v2 v3 |> List.map (state_pretty_error ~pos)
