
open LambdaJS.Prelude
open MyPervasives
open SymbolicState
open JS.Syntax
open LambdaJS.Syntax

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
  let resl_false s = resl_bool s false
  let resl_true s = resl_bool s true
  let resl_int s i = resl_v s (int i)
  let resl_num s n = resl_v s (num n)
  let resl_str s x = resl_v s (str x)

  let throwl ~pos s v = resl_e ~pos s (SThrow v)
  let throwl_str ~pos s msg = throwl ~pos s (str msg)
end

open ResHelpers
open Mk


let _xeval = ref (fun _ _ -> failwith "xeval not initialized yet")
let xeval e s = !_xeval e s

let to_int ~pos x s = match x with
| SConst (CInt n) -> SValue n
| SConst (CNum n) -> SValue (int_of_float n)
| _ -> SExn (throwl_str ~pos s (sprintf "expected number, got %s" (ToString.svalue s x)))

let to_float ~pos x s = match x with
| SConst (CInt n) -> SValue (float_of_int n)
| SConst (CNum n) -> SValue n
| _ -> SExn (throwl_str ~pos s (sprintf "expected number, got %s" (ToString.svalue s x)))


let float_str = LambdaJS.Delta.float_str

let const_typeof ~fname ~pos c s = match c with
| CUndefined -> resl_str s "undefined"
| CNull -> resl_str s "null"
| CString _ -> resl_str s "string"
| CNum _
| CInt _ -> resl_str s "number"
| CBool _ -> resl_str s "boolean"
| CRegexp _ -> errl ~pos s (sprintf "Error [%s] regexp NYI" fname)

(* Unary operators *)

let assume ~pos v s =
  match PathCondition.add_assumption (PredVal v) s.pc with
  | None -> errl ~pos s "This assumption is surely false!"
  | Some pc -> [{ s with res = SValue strue; pc }]

let eval ~pos v s = match v with
| SConst (CString x) ->
    begin match s.callstack with
    | [] -> errl ~pos s "I don't know from where eval is called"
    | { call_pos ; call_state ; _ }::_ ->
	let fname = sprintf "eval@%s" (string_of_position call_pos) in
	let lexbuf = Lexing.from_string x in
	lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = fname };
	let parsed = try SValue (JS.Parser.program JS.Lexer.token lexbuf) with
	| Failure "lexing: empty token" -> SExn (throwl_str ~pos s "Lexical error")
	| JS.Parser.Error -> SExn (throwl_str ~pos s (sprintf "Parse error: unexpected token \"%s\"" (Lexing.lexeme lexbuf)))
	in
	match parsed with
	| SExn sl -> sl
	| SValue parsed_js ->
	    let fine_ljs = parsed_js |> JS.Interm.from_javascript |> LambdaJS.Desugar.ds_top |> LambdaJS.Desugar.desugar in
	    { s with env = call_state.env }
	    |> xeval fine_ljs
	    |> List.map (fun s' -> { s' with env = s.env })
    end
| SSymb _ -> resl_v s (sop1 "eval" v)
| _ -> throwl_str ~pos s "eval"

let fail ~pos v s = resl_false s (* no such thing in my implementation *)

let get_proto ~pos v s = match v with
| SHeapLabel label ->
    let { attrs ; _ } = SHeap.find label s.heap in
    begin match IdMap.find_opt "proto" attrs with
    | Some proto -> resl_v s proto
    | None -> resl_undef s
    end
| SSymb _ -> resl_v s (sop1 "get-proto" v)
| _ -> throwl_str ~pos s "get-proto"

let is_array ~pos v s = match v with
| SHeapLabel label ->
    let { attrs ; _ } = SHeap.find label s.heap in
    begin match IdMap.find_opt "class" attrs with
    | Some (SConst (CString "Array")) -> resl_true s
    | Some (SSymb _ as c) -> resl_v s (sop2 "stx=" (SConst (CString "Array")) c)
    | Some _ -> resl_false s
    | None -> throwl_str ~pos s "is-array"
    end
| SSymb _ -> resl_v s (sop1 "is-array" v)
| _ -> throwl_str ~pos s "is-array"

let is_callable ~pos v s = match v with
| SHeapLabel label ->
    let { attrs ; _ } = SHeap.find label s.heap in
    begin match IdMap.find_opt "code" attrs with
    | Some (SClosure _) -> resl_v s strue
    | _ -> resl_v s sfalse
    end
| SSymb _ -> resl_v s (sop1 "is-callable" v)
| _ -> resl_v s sfalse

let is_extensible ~pos v s = match v with
| SHeapLabel label ->
    let { attrs ; _ } = SHeap.find label s.heap in
    begin match IdMap.find_opt "extensible" attrs with
    | Some (SConst (CBool _) as c)
    | Some (SSymb _ as c) -> resl_v s c
    | Some _
    | None -> resl_false s
    end
| SSymb _ -> resl_v s (sop1 "is-extensible" v)
| _ -> throwl_str ~pos s "is-extensible"

let object_to_string ~pos v s = match v with
| SHeapLabel label ->
    let { attrs ; _ } = SHeap.find label s.heap in
    begin match IdMap.find_opt "class" attrs with
    | Some (SConst (CString x)) -> resl_str s (sprintf "[object %s]" x)
    | Some (SSymb _ as v) -> resl_v s (sop2 "string+" (str "[object ") (sop2 "string+" v (str "]")))
    | Some _ -> throwl_str ~pos s "object-to-string, class wasn't a string"
    | None -> throwl_str ~pos s "object-to-string, didn't find class"
    end
| SSymb _ -> resl_v s (sop1 "object-to-string" v)
| _ -> throwl_str ~pos s "object-to-string, wasn't given object"


let get_own_property_names ~pos v s = match v with
| SHeapLabel label ->
    let { props ; _ } = SHeap.find label s.heap in
    let add_name name _ (i, m) =
      let m = IdMap.add (string_of_int i) (AttrMap.singleton Value (str name)) m in
      i + 1, m
    in
    let _, props = IdMap.fold add_name props (0, IdMap.empty) in
    let label = HeapLabel.fresh () in
    [{ s with heap = SHeap.add label { props ; attrs = IdMap.empty } s.heap; res = SValue (SHeapLabel label) }]
| SSymb _ -> resl_v s (sop1 "own-property-names" v)
| _ -> throwl_str ~pos s "own-property-names"

let prevent_extensions ~pos v s = match v with
| SHeapLabel label ->
    let { attrs ; _ } as o = SHeap.find label s.heap in
    let o = { o with attrs = IdMap.add "extensible" sfalse attrs } in
    [{ s with heap = SHeap.add label o s.heap; res = SValue v }]
| SSymb _ -> resl_v s (sop1 "prevent-extensions" v)
| _ -> throwl_str ~pos s "prevent-extensions"

let prim_to_bool ~pos v s = match v with
| SConst c ->
    begin match c with
    | CUndefined
    | CNull -> resl_false s
    | CBool b -> resl_bool s b
    | CInt i -> resl_bool s (i <> 0)
    | CNum f -> resl_bool s (f != nan && f <> 0.0 && f <> -0.0)
    | CString x -> resl_bool s (String.length x <> 0)
    | CRegexp _ -> resl_true s
    end
| SSymb _ -> resl_v s (sop1 "prim->bool" v)
| _ -> resl_true s

let prim_to_num ~pos v s = match v with
| SConst c ->
    begin match c with
    | CUndefined -> resl_num s nan
    | CNull
    | CBool false -> resl_num s 0.0
    | CBool true -> resl_num s 1.0
    | CNum n -> resl_num s n
    | CInt i -> resl_num s (float_of_int i)
    | CString x -> resl_num s (try float_of_string x with Failure "float_of_string" -> nan)
    | CRegexp _ -> errl ~pos s "prim_to_num of regexp"
    end
| SSymb _ -> resl_v s (sop1 "prim->num" v)
| _ -> throwl_str ~pos s "prim_to_num"

let prim_to_str ~pos v s = match v with
| SConst c ->
    begin match c with
    | CUndefined -> resl_str s "undefined"
    | CNull -> resl_str s "null"
    | CString x -> resl_str s x
    | CNum n -> resl_str s (float_str n)
    | CInt n -> resl_str s (string_of_int n)
    | CBool b -> resl_str s (string_of_bool b)
    | CRegexp _ -> errl ~pos s "Error [prim_to_str] regexp NYI"
    end
| SSymb _ -> resl_v s (sop1 "prim->str" v)
| _ -> throwl_str ~pos s "prim_to_str"

let is_primitive ~pos v s = match v with
| SConst _ -> resl_v s strue
| SSymb _ -> resl_v s (sop1 "primitive?" v)
| _ -> resl_v s sfalse

let print ~pos v s = resl_f s (SIO.print v)

let surface_typeof ~pos v s = match v with
| SConst c -> const_typeof ~fname:"surface-typeof" ~pos c s
| SHeapLabel label ->
    let { attrs ; _ } = SHeap.find label s.heap in
    resl_str s (if IdMap.mem "code" attrs then "function" else "object")
| SSymb _ -> resl_v s (sop1 "surface-typeof" v)
| SClosure _ -> throwl_str ~pos s "surface-typeof"

let get_property_names ~pos v s = match v with
| SHeapLabel _ ->
    let rec all_protos_props = function (* Return None if there is a symbolic value that can contribute to the protos *)
      | SHeapLabel label ->
	  let { attrs ; props } = SHeap.find label s.heap in
	  begin match IdMap.find_opt "proto" attrs with
	  | Some proto ->
	      begin match all_protos_props proto with
	      | Some l -> Some (props::l)
	      | None -> None
	      end
	  | None -> Some [props]
	  end
      | SSymb _ -> None
      | _ -> Some []
    in
    let rec collect_names set_opt props = match set_opt with
    | Some _ ->
	let add_prop k v set_opt = match set_opt with
	| None -> set_opt
	| Some set -> match AttrMap.find_opt Enum v with
	  | Some (SSymb _) -> None (* here we should add a conditional fork *)
	  | Some (SConst (CBool true)) -> Some (IdSet.add k set)
	  | None
	  | Some _ -> set_opt
	in
	IdMap.fold add_prop props set_opt
    | None -> set_opt
    in	
    begin match all_protos_props v with
    | None -> resl_v s (sop1 "property-names" v)
    | Some protos_props -> match List.fold_left collect_names (Some IdSet.empty) protos_props with
      | None -> resl_v s (sop1 "property-names" v)
      | Some name_set ->
	  let add_name name (i, m) =
	    let m = IdMap.add (string_of_int i) (AttrMap.singleton Value (str name)) m in
	    i + 1, m
	  in
	  let _, props = IdSet.fold add_name name_set (0, IdMap.empty) in
	  let label = HeapLabel.fresh () in
	  [{ s with heap = SHeap.add label { props ; attrs = IdMap.empty } s.heap; res = SValue (SHeapLabel label) }]
    end
| SSymb _ -> resl_v s (sop1 "property-names" v)
| _ -> throwl_str ~pos s "get-property-names"

let symbol ~pos v s = if !Options.opt_symbols then match v with
| SConst (CString id) -> resl_v s (sid (SId.from_string id))
| SConst (CInt n) -> resl_v s (sid (SId.from_string (string_of_int n)))
| _ -> errl ~pos s "Error [symbol] Please, don't do stupid things with symbolic id"
else
  failwith "Primitive \"symbol\" used with -no-symb option"

let to_int32 ~pos v s = match v with
| SConst (CInt _) -> resl_v s v
| SConst (CNum f) -> resl_int s (int_of_float f)
| SSymb _ -> resl_v s (sop1 "to-int32" v)
| _ -> throwl_str ~pos s "to-int"

let typeof ~pos v s = match v with
| SConst c -> const_typeof ~fname:"typeof" ~pos c s
| SHeapLabel _ -> resl_str s "object"
| SClosure _ -> resl_str s "lambda"
| SSymb _ -> resl_v s (sop1 "typeof" v)

let err_op1 ~op ~pos _ s = errl ~pos s (sprintf "Error [xeval] No implementation of unary operator \"%s\"" op)

let op1 ~pos op v s =
  let f = match op with
  | "assume" -> assume
  | "eval" -> eval
  | "fail?" -> fail
  | "get-proto" -> get_proto
  | "is-array" -> is_array
  | "is-callable" -> is_callable
  | "is-extensible" -> is_extensible
  | "object-to-string" -> object_to_string
  | "own-property-names" -> get_own_property_names
  | "prevent-extensions" -> prevent_extensions
  | "prim->bool" -> prim_to_bool
  | "prim->num" -> prim_to_num
  | "prim->str" -> prim_to_str
  | "primitive?" -> is_primitive
  | "print" -> print
  | "property-names" -> get_property_names
  | "surface-typeof" -> surface_typeof
  | "symbol" -> symbol
  | "to-int32" -> to_int32
  | "typeof" -> typeof
  | op -> err_op1 ~op
  in
  f ~pos v s

(* Binary operators *)

let arith ~pos op2_op i_op f_op v1 v2 s = match v1, v2 with
| SConst (CInt i1), SConst (CInt i2) -> resl_int s (i_op i1 i2)
| SConst (CNum f1), SConst (CNum f2) -> resl_num s (f_op f1 f2)
| SConst (CNum f1), SConst (CInt i2) -> resl_num s (f_op f1 (float_of_int i2))
| SConst (CInt i1), SConst (CNum f2) -> resl_num s (f_op (float_of_int i1) f2)
| SSymb _, _
| _, SSymb _ -> resl_v s (sop2 op2_op v1 v2)
| _ -> throwl_str ~pos s "arithmetic operator"

let arith_sum ~pos v1 v2 s = arith ~pos "+" (+) (+.) v1 v2 s

let arith_sub ~pos v1 v2 s = arith ~pos "-" (-) (-.) v1 v2 s

let arith_mul ~pos v1 v2 s = arith ~pos "*" ( * ) ( *. ) v1 v2 s

let arith0 ~pos op2_op i_op f_op def v1 v2 s = match v2 with
| SConst (CInt 0)
| SConst (CNum 0.0) -> resl_num s def (* Simplified: no thrown error if v1 is not ok *)
| SSymb _ -> resl_rv_if s (sop2 "=" v2 (num 0.0)) (SValue (num def)) (SValue (sop2 op2_op v1 v2))
| _ -> arith ~pos op2_op i_op f_op v1 v2 s

let arith_div ~pos v1 v2 s = arith0 ~pos "/" (/) (/.) infinity v1 v2 s

let arith_mod ~pos v1 v2 s = arith0 ~pos "%" (mod) mod_float nan v1 v2 s

let bitwise op2_op i_op ~pos v1 v2 s = match v1, v2 with
| SSymb _, _
| _, SSymb _ -> resl_v s (sop2 op2_op v1 v2)
| _ -> match to_int ~pos v1 s with
  | SExn sl -> sl
  | SValue i1 -> match to_int ~pos v2 s with
    | SExn sl -> sl
    | SValue i2 -> resl_int s (i_op i1 i2)

let bitwise_and ~pos v1 v2 s = bitwise "&" (land) ~pos v1 v2 s

let bitwise_or ~pos v1 v2 s = bitwise "|" (lor) ~pos v1 v2 s

let bitwise_xor ~pos v1 v2 s = bitwise "^" (lxor) ~pos v1 v2 s

let bitwise_shiftl ~pos v1 v2 s = bitwise "<<" (lsl) ~pos v1 v2 s

let bitwise_zfshiftr ~pos v1 v2 s = bitwise ">>>" (lsr) ~pos v1 v2 s

let bitwise_shiftr ~pos v1 v2 s = bitwise ">>" (asr) ~pos v1 v2 s

let arith_cmp op2_op f_cmp ~pos v1 v2 s = match v1, v2 with
| SSymb _, _
| _, SSymb _ -> resl_v s (sop2 op2_op v1 v2)
| _ -> match to_float ~pos v1 s with
  | SExn sl -> sl
  | SValue f1 -> match to_float ~pos v2 s with
    | SExn sl -> sl
    | SValue f2 -> resl_bool s (f_cmp f1 f2)

let arith_lt ~pos v1 v2 s = arith_cmp "<" (<) ~pos v1 v2 s

let arith_le ~pos v1 v2 s = arith_cmp "<=" (<=) ~pos v1 v2 s

let arith_gt ~pos v1 v2 s = arith_cmp ">" (>) ~pos v1 v2 s

let arith_ge ~pos v1 v2 s = arith_cmp ">=" (>=) ~pos v1 v2 s

let abs_eq ~pos v1 v2 s = match v1, v2 with
  (* TODO: check if it's ok with null, undefined, nan, +/- 0.0, ... *)
| v1, v2 when v1 == v2 || v1 = v2 -> resl_true s
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
| _ -> throwl_str ~pos s "expected primitive constant"

let stx_eq ~pos v1 v2 s = match v1, v2 with
  (* TODO: check if it's ok with null, undefined, nan, +/- 0.0, ... *)
| v1, v2 when v1 == v2 || v1 = v2 -> resl_true s 
| SConst (CNum n), SConst (CInt i)
| SConst (CInt i), SConst (CNum n) -> resl_bool s (float_of_int i = n)
| SSymb _, _
| _, SSymb _ -> resl_v s (sop2 "stx=" v1 v2)
| _, _ -> resl_false s

let string_plus ~pos v1 v2 s = match v1, v2 with
| SConst (CString x1), SConst (CString x2) -> resl_str s (x1 ^ x2)
| SConst (CString _), SSymb _
| SSymb _, SConst (CString _)
| SSymb _, SSymb _ -> resl_v s (sop2 "string+" v1 v2)
| _ -> throwl_str ~pos s "string concatenation"

let has_own_property ~pos v1 v2 s = match v1, v2 with
| SHeapLabel label, SConst (CString prop) ->
    let { props ; _ } = SHeap.find label s.heap in
    resl_bool s (IdMap.mem prop props)
| SHeapLabel _, SSymb _
| SSymb _, SConst (CString _)
| SSymb _, SSymb _ -> resl_v s (sop2 "has-own-property?" v1 v2)
| _, _ -> throwl_str ~pos s "has-own-property?"

let has_property ~pos v1 v2 s = match v1, v2 with
| SHeapLabel _, SSymb _
| SSymb _, SConst (CString _)
| SSymb _, SSymb _ -> resl_v s (sop2 "has-propert?" v1 v2)
| SHeapLabel _, SConst (CString prop) ->
    let rec has_prop = function
      | SHeapLabel label ->
	  let { attrs ; props } = SHeap.find label s.heap in
	  if IdMap.mem prop props then
	    resl_true s
	  else begin match IdMap.find_opt "proto" attrs with
	  | None -> resl_false s
	  | Some proto -> has_prop proto
	  end
      | SSymb _ -> resl_v s (sop2 "has-property?" v1 v2)
      | _ -> resl_false s
    in
    has_prop v1
| _, _ -> resl_false s

let err_op2 ~op ~pos _ _ s = errl ~pos s (sprintf "Error [xeval] No implementation of binary operator \"%s\"" op)

let op2 ~pos op v1 v2 s =
  let f = match op with
  | "+" -> arith_sum
  | "-" -> arith_sub
  | "*" -> arith_mul
  | "/" -> arith_div
  | "%" -> arith_mod
  | "&" -> bitwise_and
  | "|" -> bitwise_or
  | "^" -> bitwise_xor
  | "<<" -> bitwise_shiftl
  | ">>" -> bitwise_shiftr
  | ">>>" -> bitwise_zfshiftr
  | "<" -> arith_lt
  | "<=" -> arith_le
  | ">" -> arith_gt
  | ">=" -> arith_ge
  | "abs=" -> abs_eq
  | "stx=" -> stx_eq
  | "string+" -> string_plus
  | "has-own-property?" -> has_own_property
  | "has-property?" -> has_property
  | op -> err_op2 ~op
  in
  s |> f ~pos v1 v2

(* Ternary operators *)

let err_op3 ~op ~pos _ _ _ s = errl ~pos:dummy_pos s (sprintf "Error [xeval] No ternary operators yet, so what's this \"%s\"" op)

let op3 ~pos op v1 v2 v3 s =
  let f = match op with
  | op -> err_op3 ~op
  in
  s |> f ~pos v1 v2 v3
