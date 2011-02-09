
open LambdaJS.Prelude
open MyPervasives
open SymbolicValue
open SymbolicState
open JS.Syntax
open LambdaJS.Syntax


let _xeval = ref (fun _ _ -> failwith "xeval not initialized yet")
let xeval e s = !_xeval e s

let float_str = LambdaJS.Delta.float_str

let const_typeof ~fname ~pos c s = match c with
| CUndefined -> SState.res_str "undefined" s
| CNull -> SState.res_str "null" s
| CString _ -> SState.res_str "string" s
| CNum _
| CInt _ -> SState.res_str "number" s
| CBool _ -> SState.res_str "boolean" s
| CRegexp _ -> SState.err ~pos s (sprintf "Error [%s] regexp NYI" fname)

(* Unary operators *)

let bool_neg ~pos v s = match v with
| SConst (CBool b) -> SState.res_bool (not b) s
| SSymb (TV (TP TBool), _) -> SState.res_op1 ~typ:tBool "bool!" v s
| SSymb ((TV (TP TPAny | TVAny) | TA), _) -> SState.res_op1 ~typ:tA "bool!" v s
| _ -> SState.throw_str ~pos s "bool!"

let eval ~pos v s = match v with
| SConst (CString x) ->
    begin match SState.CallStack.top s with
    | None -> SState.err ~pos s "I don't know from where eval is called"
    | Some call ->
	let call_pos = SState.CallStack.call_pos call in
	let call_env = SState.CallStack.call_env call in
	let fname = sprintf "eval@%s" (string_of_position call_pos) in
	let lexbuf = Lexing.from_string x in
	lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = fname };
	let parsed = try SValue (JS.Parser.program JS.Lexer.token lexbuf) with
	| Failure "lexing: empty token" -> SExn (SState.throw_str ~pos s "Lexical error")
	| JS.Parser.Error -> SExn (SState.throw_str ~pos s (sprintf "Parse error: unexpected token \"%s\"" (Lexing.lexeme lexbuf)))
	in
	match parsed with
	| SExn sl -> sl
	| SValue parsed_js ->
	    let fine_ljs = parsed_js |> JS.Interm.from_javascript |> LambdaJS.Desugar.ds_top |> LambdaJS.Desugar.desugar in
	    s
	    |> SState.Env.push call_env
	    |> xeval fine_ljs
	    |> SState.map_unit SState.Env.pop
    end
| SSymb (TV (TP TStr), _)
| SSymb ((TV (TP TPAny | TVAny) | TA), _) -> SState.err ~pos s "Eval of a symbolic value"
| _ -> SState.throw_str ~pos s "eval"

let fail ~pos v s = SState.res_false s (* no such thing in my implementation *)

let get_proto ~pos v s = match v with
| SHeapLabel label ->
    let { proto ; _ } = SState.Heap.find_ip label s in
    begin match proto with
    | Some proto -> SState.res_heaplabel proto s
    | None -> SState.res_undef s
    end
| SSymb (TV TRef, _) -> SState.res_op1 ~typ:tVAny "get-proto" v s
| SSymb ((TV TVAny | TA), _) -> SState.res_op1 ~typ:tA "get-proto" v s
| _ -> SState.throw_str ~pos s "get-proto"

let is_array ~pos v s = match v with
| SHeapLabel label ->
    let { _class ; _ } = SState.Heap.find_ip label s in
    SState.res_bool (_class = "Array") s
| SSymb (TV TRef, _) -> SState.res_op1 ~typ:tBool "is-array" v s
| SSymb ((TV TVAny | TA), _) -> SState.res_op1 ~typ:tA "is-array" v s
| _ -> SState.throw_str ~pos s "is-array"

let is_callable ~pos v s = match v with
| SHeapLabel label ->
    let { code ; _ } = SState.Heap.find_ip label s in
    SState.res_bool (code <> None) s
| SSymb (TV TRef, _) -> SState.res_op1 ~typ:tBool "ref-is-callable" v s
| SSymb (TV TVAny, _) -> SState.res_op1 ~typ:tBool "is-callable" v s
| SSymb (TA, _) -> SState.res_op1 ~typ:tA "is-callable" v s
| _ -> SState.res_false s

let is_extensible ~pos v s = match v with
| SHeapLabel label ->
    let { extensible ; _ } = SState.Heap.find_ip label s in
    SState.res_bool extensible s
| SSymb (TV TRef, _) -> SState.res_op1 ~typ:tBool "is-extensible" v s
| SSymb ((TV TVAny | TA), _) -> SState.res_op1 ~typ:tA "is-extensible" v s
| _ -> SState.throw_str ~pos s "is-extensible"

let object_to_string ~pos v s = match v with
| SHeapLabel label ->
    let { _class ; _ } = SState.Heap.find_ip label s in
    SState.res_str (sprintf "[object %s]" _class) s
| SSymb (TV TRef, _) -> SState.res_op1 ~typ:tStr "object-to-string" v s
| SSymb ((TV TVAny | TA), _) -> SState.res_op1 ~typ:tA "object-to-string" v s
| _ -> SState.throw_str ~pos s "object-to-string, wasn't given object"


let get_own_property_names ~pos v s = match v with
| SHeapLabel label ->
    let props = SState.Heap.find_p label s in
    if props.more_but_fields <> None then
      SState.res_op1 ~typ:tRef "own-property-names" v s
    else
      let add_name name _ (i, m) =
	let m = IdMap.add (string_of_int i) (Mk.data_prop (Mk.str name)) m in
	i + 1, m
      in
      let _, fields = IdMap.fold add_name props.fields (0, IdMap.empty) in
      SState.res_heap_add_fresh ({ fields; more_but_fields = None }, Mk.internal_props) s
| SSymb (TV TRef, _) -> SState.res_op1 ~typ:tRef "own-property-names" v s
| SSymb ((TV TVAny | TA), _) -> SState.res_op1 ~typ:tA "own-property-names" v s
| _ -> SState.throw_str ~pos s "own-property-names"

let prevent_extensions ~pos v s = match v with
| SHeapLabel label ->
    let internal_props = SState.Heap.find_ip label s in
    let s = SState.Heap.update_ip label { internal_props with extensible = false } s in
    SState.res_v v s
| SSymb (TV TRef, _) -> SState.res_op1 ~typ:tRef "prevent-extensions" v s
| SSymb ((TV TVAny | TA), _) -> SState.res_op1 ~typ:tA "prevent-extensions" v s
| _ -> SState.throw_str ~pos s "prevent-extensions"

let prim_to_bool ~pos v s = match v with
| SConst c ->
    begin match c with
    | CUndefined
    | CNull -> SState.res_false s
    | CBool b -> SState.res_bool b s
    | CInt i -> SState.res_bool (i <> 0) s
    | CNum f -> SState.res_bool (f != nan && f <> 0.0 && f <> -0.0) s
    | CString x -> SState.res_bool (String.length x <> 0) s
    | CRegexp _ -> SState.res_true s
    end
| SSymb (TV (TP TBool), _) -> SState.res_v v s
| SSymb (TV (TP (TN TInt)), _) -> SState.res_op1 ~typ:tBool "int->bool" v s
| SSymb (TV (TP (TN TNum)), _) -> SState.res_op1 ~typ:tBool "num->bool" v s
| SSymb (TV (TP TStr), _) -> SState.res_op1 ~typ:tBool "str->bool" v s
| SSymb (TV (TP _), _) -> SState.res_op1 ~typ:tBool "prim->bool" v s
| SSymb ((TV TVAny | TA), _) -> SState.res_op1 ~typ:tA "prim->bool" v s
| _ -> SState.res_true s

let prim_to_num ~pos v s = match v with
| SConst c ->
    begin match c with
    | CUndefined -> SState.res_num nan s
    | CNull
    | CBool false -> SState.res_int 0 s (* SState.res_num 0.0 s *)
    | CBool true -> SState.res_int 1 s (* SState.res_num 1.0 s *)
    | CNum _(* n -> SState.res_num n s *)
    | CInt _ -> SState.res_v v s (* i -> SState.res_num (float_of_int i) s *)
    | CString x -> SState.res_num (try float_of_string x with Failure "float_of_string" -> nan) s
    | CRegexp _ -> SState.err ~pos s "prim_to_num of regexp"
    end
| SSymb (TV (TP TBool), _) -> SState.res_op1 ~typ:tInt "prim->num" v s
| SSymb (TV (TP (TN _)), _) -> SState.res_v v s
| SSymb (TV (TP TStr), _) -> SState.res_op1 ~typ:tNAny "prim->num" v s
| SSymb ((TV (TP TPAny | TVAny) | TA), _) -> SState.res_op1 ~typ:tA "prim->num" v s
| _ -> SState.throw_str ~pos s "prim_to_num"

let prim_to_str ~pos v s = match v with
| SConst c ->
    begin match c with
    | CUndefined -> SState.res_str "undefined" s
    | CNull -> SState.res_str "null" s
    | CString x -> SState.res_str x s
    | CNum n -> SState.res_str (float_str n) s
    | CInt n -> SState.res_str (string_of_int n) s
    | CBool b -> SState.res_str (string_of_bool b) s
    | CRegexp _ -> SState.err ~pos s "Error [prim_to_str] regexp NYI"
    end
| SSymb (TV (TP TBool), _) -> SState.res_op1 ~typ:tStr "bool->str" v s
| SSymb (TV (TP (TN TInt)), _) -> SState.res_op1 ~typ:tStr "int->str" v s
| SSymb (TV (TP (TN TNum)), _) -> SState.res_op1 ~typ:tStr "num->str" v s
| SSymb (TV (TP TStr), _) -> SState.res_v v s
| SSymb (TV (TP _), _) -> SState.res_op1 ~typ:tStr "prim->str" v s
| SSymb ((TV TVAny | TA), _) -> SState.res_op1 ~typ:tA "prim->str" v s
| _ -> SState.throw_str ~pos s "prim_to_str"

let is_primitive ~pos v s = match v with
| SConst _ -> SState.res_true s
| SSymb (TV (TP _), _) -> SState.res_true s
| SSymb (TV TVAny, _) -> SState.res_op1 ~typ:tBool "primitive?" v s
| SSymb (TA, _) -> SState.res_op1 ~typ:tA "primitive?" v s
| _ -> SState.res_false s

let print ~pos v s = s |> SState.Output.print v |> SState.singleton

let surface_typeof ~pos v s = match v with
| SConst c -> const_typeof ~fname:"surface-typeof" ~pos c s
| SHeapLabel label ->
    let { code; _ } = SState.Heap.find_ip label s in
    SState.res_str (if code = None then "object" else "function") s
| SSymb (TV (TP TBool), _) -> SState.res_str "boolean" s
| SSymb (TV (TP (TN _)), _) -> SState.res_str "number" s
| SSymb (TV (TP TStr), _) -> SState.res_str "string" s
| SSymb (TV TRef, _) -> SState.res_op1 ~typ:tStr "surface-typeof" v s
| SSymb (TV _, _) -> SState.res_op1 ~typ:tStr "surface-typeof" v s
| SSymb (TA, _) -> SState.res_op1 ~typ:tA "surface-typeof" v s
| SClosure _ -> SState.throw_str ~pos s "surface-typeof"

let get_property_names ~pos v s = match v with
| SHeapLabel label ->
    let rec all_protos_props label = (* Return None if there is a symbolic value that can contribute to the protos props *)
      let { fields; more_but_fields } = SState.Heap.find_p label s in
      if more_but_fields <> None then
	None
      else
	let { proto; _ } = SState.Heap.find_ip label s in
	match proto with
	| Some lab ->
	    begin match all_protos_props lab with
	    | Some l -> Some (fields::l)
	    | None -> None
	    end
	| None -> Some [fields]
    in
    let rec collect_names set_opt props = match set_opt with
    | Some _ ->
	let add_prop k v set_opt = match set_opt with
	| Some set when v.enum -> Some (IdSet.add k set)
	| _ -> set_opt
	in
	IdMap.fold add_prop props set_opt
    | None -> set_opt
    in	
    begin match all_protos_props label with
    | None -> SState.res_op1 ~typ:tRef "property-names" v s
    | Some protos_props -> match List.fold_left collect_names (Some IdSet.empty) protos_props with
      | None -> SState.res_op1 ~typ:tRef "property-names" v s
      | Some name_set ->
	  let add_name name (i, m) =
	    let m = IdMap.add (string_of_int i) (Mk.data_prop (Mk.str name)) m in
	    i + 1, m
	  in
	  let _, fields = IdSet.fold add_name name_set (0, IdMap.empty) in
	  SState.res_heap_add_fresh ({ fields; more_but_fields = None }, Mk.internal_props) s
    end
| SSymb (TV TRef, _) -> SState.res_op1 ~typ:tRef "property-names" v s
| SSymb ((TV TVAny | TA), _) -> SState.res_op1 ~typ:tA "property-names" v s
| _ -> SState.throw_str ~pos s "get-property-names"

let _symbol f_name typ ~pos v s =
  if !Options.opt_symbols then match v with
  | SConst (CString id) -> SState.res_id ~typ (SId.from_string id) s
  | SConst (CInt n) -> SState.res_id ~typ (SId.from_string (string_of_int n)) s
  | _ -> SState.err ~pos s (sprintf "Error [%s] Please, don't do stupid things with symbolic id" f_name)
  else
    failwith (sprintf "Primitive \"%s\" used with -no-symb option" f_name)

let symbol_bool = _symbol "symbol_bool" tBool
let symbol_int = _symbol "symbol_int" tInt
let symbol_num = _symbol "symbol_num" tNum
let symbol_number = _symbol "symbol_number" tNAny
let symbol_string = _symbol "symbol_string" tStr
let symbol_prim = _symbol "symbol_prim" tPAny
let symbol_ref = _symbol "symbol_ref" tRef
let symbol = _symbol "symbol" tVAny

let to_int32 ~pos v s = match v with
| SSymb (TV (TP (TN TInt)), _)
| SConst (CInt _) -> SState.res_v v s
| SConst (CNum f) -> SState.res_int (int_of_float f) s
| SSymb (TV (TP (TN TNum)), _) -> SState.res_op1 ~typ:tInt "num->int32" v s
| SSymb (TV (TP (TN _)), _) -> SState.res_op1 ~typ:tInt "to-int32" v s
| SSymb ((TV (TP TPAny | TVAny) | TA), _) -> SState.res_op1 ~typ:tA "to-int32" v s
| _ -> SState.throw_str ~pos s "to-int"

let typeof ~pos v s = match v with
| SConst c -> const_typeof ~fname:"typeof" ~pos c s
| SHeapLabel _ -> SState.res_str "object" s
| SClosure _ -> SState.res_str "lambda" s
| SSymb (TV (TP TBool), _) -> SState.res_str "boolean" s
| SSymb (TV (TP (TN _)), _) -> SState.res_str "number" s
| SSymb (TV (TP TStr), _) -> SState.res_str "string" s
| SSymb (TV TRef, _) -> SState.res_str "object" s
| SSymb (TV _, _) -> SState.res_op1 ~typ:tStr "typeof" v s
| SSymb (_, _) -> SState.res_op1 ~typ:tA "typeof" v s

let err_op1 ~op ~pos _ s = SState.err ~pos s (sprintf "Error [xeval] No implementation of unary operator \"%s\"" op)

let op1 ~pos op v s =
  let f = match op with
  | "assert" -> SState.PathCondition._assert
  | "assume" -> SState.PathCondition.assume
  | "bool!" -> bool_neg
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
  | "symbol_bool" -> symbol_bool
  | "symbol_int" -> symbol_int
  | "symbol_num" -> symbol_num
  | "symbol_number" -> symbol_number
  | "symbol_string" -> symbol_string
  | "symbol_prim" -> symbol_prim
  | "symbol_ref" -> symbol_ref
  | "symbol" -> symbol
  | "to-int32" -> to_int32
  | "typeof" -> typeof
  | op -> err_op1 ~op
  in
  f ~pos v s

(* Binary operators *)

(* the type informations are good for +, -, * only. TODO *)
let arith ~pos op2_op i_op f_op v1 v2 s = match v1, v2 with
| SConst (CInt i1), SConst (CInt i2) -> SState.res_int (i_op i1 i2) s
| SConst (CNum f1), SConst (CNum f2) -> SState.res_num (f_op f1 f2) s
| SConst (CNum f1), SConst (CInt i2) -> SState.res_num (f_op f1 (float_of_int i2)) s
| SConst (CInt i1), SConst (CNum f2) -> SState.res_num (f_op (float_of_int i1) f2) s
| (SConst (CInt _) | SSymb (TV (TP (TN TInt)), _)), (SConst (CInt _) | SSymb (TV (TP (TN TInt)), _)) ->
    SState.res_op2 ~typ:tInt op2_op v1 v2 s
| (SConst (CInt _) | SSymb (TV (TP (TN (TInt | TNAny))), _)), (SConst (CInt _) | SSymb (TV (TP (TN (TInt | TNAny))), _)) ->
    SState.res_op2 ~typ:tNAny op2_op v1 v2 s
| (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)), (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)) ->
    SState.res_op2 ~typ:tNum op2_op v1 v2 s
| (SConst (CInt _ | CNum _) | SSymb ((TV (TP (TN _ | TPAny) | TVAny) | TA), _)), (SConst (CInt _ | CNum _) | SSymb ((TV (TP (TN _ | TPAny) | TVAny) | TA), _)) ->
    SState.res_op2 ~typ:tA op2_op v1 v2 s
| _ -> SState.throw_str ~pos s "arithmetic operator"

let arith_sum ~pos v1 v2 s = arith ~pos "+" (+) (+.) v1 v2 s

let arith_sub ~pos v1 v2 s = arith ~pos "-" (-) (-.) v1 v2 s

let arith_mul ~pos v1 v2 s = arith ~pos "*" ( * ) ( *. ) v1 v2 s

let arith0 ~pos op2_op i_op f_op def v1 v2 s = match v1, v2 with
| (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)), SConst (CInt 0 | CNum 0.0) ->
    SState.res_num def s
| SSymb ((TV (TP TPAny | TVAny) | TA), _), SConst (CInt 0 | CNum 0.0) ->
    SState.res_num def s (* simplified: no thrown error is v1 is not a number *)
(* | SSymb _ -> resl_rv_if s (Mk.sop2 "=" v2 (num 0.0)) (SValue (num def)) (SValue (Mk.sop2 op2_op v1 v2)) *)
| _ -> arith ~pos op2_op i_op f_op v1 v2 s

let arith_div ~pos v1 v2 s = arith0 ~pos "/" (/) (/.) infinity v1 v2 s

let arith_mod ~pos v1 v2 s = arith0 ~pos "%" (mod) mod_float nan v1 v2 s

let bitwise op2_op i_op ~pos v1 v2 s = match v1, v2 with
| SConst (CInt i1), SConst (CInt i2) -> SState.res_int (i_op i1 i2) s
| SConst (CInt i1), SConst (CNum n2) -> SState.res_int (i_op i1 (int_of_float n2)) s
| SConst (CNum n1), SConst (CInt i2) -> SState.res_int (i_op (int_of_float n1) i2) s
| SConst (CNum n1), SConst (CNum n2) -> SState.res_int (i_op (int_of_float n1) (int_of_float n2)) s
| (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)), (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)) ->
    SState.res_op2 ~typ:tInt op2_op v1 v2 s
| (SConst (CInt _ | CNum _) | SSymb ((TV (TP (TN _ | TPAny) | TVAny) | TA), _)), (SConst (CInt _ | CNum _) | SSymb ((TV (TP (TN _ | TPAny) | TVAny) | TA), _)) ->
    SState.res_op2 ~typ:tA op2_op v1 v2 s
| _ -> SState.throw_str ~pos s (sprintf "expected numbers, got %s and %s" (ToString.svalue s v1) (ToString.svalue s v2))

let bitwise_and ~pos v1 v2 s = bitwise "&" (land) ~pos v1 v2 s

let bitwise_or ~pos v1 v2 s = bitwise "|" (lor) ~pos v1 v2 s

let bitwise_xor ~pos v1 v2 s = bitwise "^" (lxor) ~pos v1 v2 s

let bitwise_shiftl ~pos v1 v2 s = bitwise "<<" (lsl) ~pos v1 v2 s

let bitwise_zfshiftr ~pos v1 v2 s = bitwise ">>>" (lsr) ~pos v1 v2 s

let bitwise_shiftr ~pos v1 v2 s = bitwise ">>" (asr) ~pos v1 v2 s

let arith_cmp op2_op i_cmp f_cmp ~pos v1 v2 s = match v1, v2 with
| SConst (CInt i1), SConst (CInt i2) -> SState.res_bool (i_cmp i1 i2) s
| SConst (CInt i1), SConst (CNum n2) -> SState.res_bool (f_cmp (float_of_int i1) n2) s
| SConst (CNum n1), SConst (CInt i2) -> SState.res_bool (f_cmp n1 (float_of_int i2)) s
| SConst (CNum n1), SConst (CNum n2) -> SState.res_bool (f_cmp n1 n2) s
| (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)), (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)) ->
    SState.res_op2 ~typ:tBool op2_op v1 v2 s
| (SConst (CInt _ | CNum _) | SSymb ((TV (TP (TN _ | TPAny) | TVAny) | TA), _)), (SConst (CInt _ | CNum _) | SSymb ((TV (TP (TN _ | TPAny) | TVAny) | TA), _)) ->
    SState.res_op2 ~typ:tA op2_op v1 v2 s
| _ -> SState.throw_str ~pos s (sprintf "expected numbers, got %s and %s" (ToString.svalue s v1) (ToString.svalue s v2))

let arith_lt ~pos v1 v2 s = arith_cmp "<" (<) (<) ~pos v1 v2 s

let arith_le ~pos v1 v2 s = arith_cmp "<=" (<=) (<=) ~pos v1 v2 s

let arith_gt ~pos v1 v2 s = arith_cmp ">" (>) (>) ~pos v1 v2 s

let arith_ge ~pos v1 v2 s = arith_cmp ">=" (>=) (>=) ~pos v1 v2 s

let abs_eq ~pos v1 v2 s = match v1, v2 with
| SClosure _, _ | _, SClosure _ -> assert false
| SConst (CNum n), _
| _, SConst (CNum n) when n == nan -> SState.res_false s
| v1, v2 when v1 == v2 || v1 = v2 -> SState.res_true s
| SHeapLabel _, SHeapLabel _ -> SState.res_false s
| SConst c1, SConst c2 ->
    let b = match c1, c2 with
    | CNull, CUndefined
    | CUndefined, CNull -> true
    | CString x, CNum n
    | CNum n, CString x -> (try n = float_of_string x with Failure "float_of_string" -> false)
    | CString x, CInt n
    | CInt n, CString x -> (try float_of_int n = float_of_string x with Failure _ -> false)
    | CNum n, CBool b
    | CBool b, CNum n -> n = if b then 1.0 else 0.0
    | CInt n, CBool b
    | CBool b, CInt n -> n = if b then 1 else 0
    | CNum f, CInt i
    | CInt i, CNum f -> float_of_int i = f
    | CBool b, CString s
    | CString s, CBool b -> (try float_of_string s = if b then 1.0 else 0.0 with Failure "float_of_string" -> false)
    | _ -> false
    in SState.res_bool b s
| (SConst (CBool _) | SSymb (TV (TP TBool), _)), (SConst (CBool _) | SSymb (TV (TP TBool), _))
| (SConst (CInt _) | SSymb (TV (TP (TN TInt)), _)), (SConst (CInt _) | SSymb (TV (TP (TN TInt)), _))
| (SConst (CString _) | SSymb (TV (TP TStr), _)), (SConst (CString _) | SSymb (TV (TP TStr), _))
| (SHeapLabel _ | SSymb (TV TRef, _)), (SHeapLabel _ | SSymb (TV TRef, _)) (* -> *)
    (* SState.res_op2 ~typ:tBool "=" v1 v2 s *)
| (SConst (CNum _) | SSymb (TV (TP (TN TNum)), _)), (SConst (CNum _) | SSymb (TV (TP (TN TNum)), _)) (* -> *)
    (* SState.res_op2 ~typ:tBool "num=" v1 v2 s *)
| (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)), (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)) ->
    SState.res_op2 ~typ:tBool "stx=" v1 v2 s
(* some cases could be optimized here but it would be very long to enumerate them *)
| (SHeapLabel _ | SSymb (TV TRef, _)), (SConst _ | SSymb (TV (TP _), _))
| (SConst _ | SSymb (TV (TP _), _)), (SHeapLabel _ | SSymb (TV TRef, _)) ->
    SState.res_false s
| (SConst _ | SHeapLabel _ | SSymb (TV _, _)), (SConst _ | SHeapLabel _ | SSymb (TV _, _)) ->
    SState.res_op2 ~typ:tBool "abs=" v1 v2 s
| _, _ -> SState.res_op2 ~typ:tA "abs=" v1 v2 s

let stx_eq ~pos v1 v2 s = match v1, v2 with
| SClosure _, _ | _, SClosure _ -> assert false
  (* TODO: check if it's ok with null, undefined, nan, +/- 0.0, ... *)
| SConst (CNum n), _
| _, SConst (CNum n) when n == nan -> SState.res_false s
| v1, v2 when v1 == v2 || v1 = v2 -> SState.res_true s 
| SConst (CNum n), SConst (CInt i)
| SConst (CInt i), SConst (CNum n) -> SState.res_bool (float_of_int i = n) s
| (SConst _ | SHeapLabel _), (SConst _ | SHeapLabel _) -> SState.res_false s
| (SConst (CBool _) | SSymb (TV (TP TBool), _)), (SConst (CBool _) | SSymb (TV (TP TBool), _))
| (SConst (CInt _) | SSymb (TV (TP (TN TInt)), _)), (SConst (CInt _) | SSymb (TV (TP (TN TInt)), _))
| (SConst (CString _) | SSymb (TV (TP TStr), _)), (SConst (CString _) | SSymb (TV (TP TStr), _))
| (SHeapLabel _ | SSymb (TV TRef, _)), (SHeapLabel _ | SSymb (TV TRef, _)) (* -> *)
    (* SState.res_op2 ~typ:tBool "=" v1 v2 s *)
| (SConst (CNum _) | SSymb (TV (TP (TN TNum)), _)), (SConst (CNum _) | SSymb (TV (TP (TN TNum)), _)) (* -> *)
    (* SState.res_op2 ~typ:tBool "num=" v1 v2 s *)
| (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)), (SConst (CInt _ | CNum _) | SSymb (TV (TP (TN _)), _)) ->
    SState.res_op2 ~typ:tBool "stx=" v1 v2 s
| (SConst _ | SSymb (TV (TP _), _)), SSymb (TV (TP TPAny | TVAny), _)
| SSymb (TV (TP TPAny | TVAny), _), (SConst _ | SSymb (TV (TP _), _))
| (SHeapLabel _ | SSymb (TV TRef, _)), SSymb (TV TVAny, _)
| SSymb (TV TVAny, _), (SHeapLabel _ | SSymb (TV TRef, _))
| SSymb (TV TVAny, _), SSymb (TV TVAny, _) ->
    SState.res_op2 ~typ:tBool "stx=" v1 v2 s
| SSymb (TA, _), _
| _, SSymb (TA, _) ->
    SState.res_op2 ~typ:tA "stx=" v1 v2 s
| _ -> SState.res_false s

let string_plus ~pos v1 v2 s = match v1, v2 with
| SConst (CString x1), SConst (CString x2) -> SState.res_str (x1 ^ x2) s
| (SConst (CString _) | SSymb (TV (TP TStr), _)), (SConst (CString _) | SSymb (TV (TP TStr), _)) ->
    SState.res_op2 ~typ:tStr "string+" v1 v2 s
| (SConst (CString _) | SSymb ((TV (TP (TStr | TPAny) | TVAny) | TA), _)), (SConst (CString _) | SSymb ((TV (TP (TStr | TPAny) | TVAny) | TA), _)) ->
    SState.res_op2 ~typ:tA "string+" v1 v2 s
| _ -> SState.throw_str ~pos s "string concatenation"

let symbol_object ~pos v1 v2 s = match v1, v2 with
| SConst (CString _ | CInt _), SHeapLabel label ->
    let props = SState.Heap.find_p label s in
    if props.more_but_fields = None then
      let props = { props with more_but_fields = Some IdSet.empty } in
      let s = SState.Heap.update_p label props s in
      SState.res_heaplabel label s
    else
      SState.err ~pos s "object can already have more fields"
| _ -> SState.err ~pos s "symbol_object, bad parameters"

let has_own_property ~pos v1 v2 s = match v1, v2 with
| SHeapLabel label, SConst (CString field) ->
    let { fields; more_but_fields } as props = SState.Heap.find_p label s in
    if IdMap.mem field fields then
      SState.res_true s
    else begin match more_but_fields with
    | None -> SState.res_false s
    | Some but_fields when IdSet.mem field but_fields -> SState.res_false s
    | Some but_fields ->
	let has s = (* todo: more_fields initializer instead of symbol_any *)
	  let sid = SId.from_string ~fresh:true field in
	  let prop = Mk.data_prop ~b:true (Mk.sid ~typ:tVAny sid) in
	  let props = { props with fields = IdMap.add field prop fields } in
	  let s = SState.Heap.update_p label props s in
	  SState.res_true s
	in
	let has_not s =
	  let props = { props with more_but_fields = Some (IdSet.add field but_fields) } in
	  let s = SState.Heap.update_p label props s in
	  SState.res_false s
	in
	SState.PathCondition.branch has has_not (Mk.sop2 ~typ:tBool "has-own-property?" v1 v2) s
    end
| (SHeapLabel _ | SSymb (TV TRef, _)), (SConst (CString _) | SSymb (TV (TP TStr), _)) ->
    SState.res_op2 ~typ:tBool "has-own-property?" v1 v2 s
| (SHeapLabel _ | SSymb ((TV (TRef | TVAny) | TA), _)), (SConst (CString _) | SSymb ((TV (TP (TStr | TPAny) | TVAny) | TA), _)) ->
    SState.res_op2 ~typ:tA "has-own-property?" v1 v2 s
| _ -> SState.throw_str ~pos s "has-own-property?"

(*
  concrete_has_prop returns
  Some true if has-property would return true
  Some false if has-property would return false
  None if there is some extensible object in the prototype chain of the object
*)
let rec concrete_has_prop label field s =
  let { fields; more_but_fields } = SState.Heap.find_p label s in
  if IdMap.mem field fields then
    Some true
  else
    let proto_concrete_has_prop () =
      let { proto; _ } = SState.Heap.find_ip label s in
      match proto with
      | None -> Some false
      | Some lab -> concrete_has_prop lab field s
    in
    match more_but_fields with
    | None -> proto_concrete_has_prop ()
    | Some but_fields when IdSet.mem field but_fields -> Some false
    | Some but_fields -> match proto_concrete_has_prop () with
      | Some true -> Some true
      | _ -> None

let has_property ~pos v1 v2 s = match v1, v2 with
| SHeapLabel label, SConst (CString field) ->
    let rec symbolic_has_prop label =
      match concrete_has_prop label field s with
      | Some b -> SState.res_bool b s
      | None ->
	  let { fields; more_but_fields } as props = SState.Heap.find_p label s in
	  match more_but_fields with
	  | None ->
	      let { proto; _ } = SState.Heap.find_ip label s in
	      begin match proto with
	      | None -> assert false (* already treated in concrete_has_prop *)
	      | Some lab -> symbolic_has_prop lab
	      end
	  | Some but_fields ->
	      let has s = (* todo: cf todo of has_own_property *)
		let sid = SId.from_string ~fresh:true field in
		let prop = Mk.data_prop ~b:true (Mk.sid ~typ:tVAny sid) in
		let props = { props with fields = IdMap.add field prop fields } in
		let s = SState.Heap.update_p label props s in
		SState.res_true s
	      in
	      let has_not s =
		let { proto; _ } = SState.Heap.find_ip label s in
		match proto with
		| None ->
		    let props = { props with more_but_fields = Some (IdSet.add field but_fields) } in
		    let s = SState.Heap.update_p label props s in
		    SState.res_false s
		| Some lab -> symbolic_has_prop lab
	      in
	      SState.PathCondition.branch has has_not (Mk.sop2 ~typ:tBool "has-own-property?" v1 v2) s
    in
    symbolic_has_prop label
| (SHeapLabel _ | SSymb (TV (TRef | TVAny), _)), (SConst (CString _) | SSymb (TV (TP (TStr | TPAny) | TVAny), _)) ->
    SState.res_op2 ~typ:tBool "has-property?" v1 v2 s
| (SHeapLabel _ | SSymb ((TV (TRef | TVAny) | TA), _)), (SConst (CString _) | SSymb ((TV (TP (TStr | TPAny) | TVAny) | TA), _)) ->
    SState.res_op2 ~typ:tA "has-property?" v1 v2 s
| _ -> SState.res_false s

let err_op2 ~op ~pos _ _ s = SState.err ~pos s (sprintf "Error [xeval] No implementation of binary operator \"%s\"" op)

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
  | "symbol_object" -> symbol_object
  | "has-own-property?" -> has_own_property
  | "has-property?" -> has_property
  | op -> err_op2 ~op
  in
  s |> f ~pos v1 v2

(* Ternary operators *)

let err_op3 ~op ~pos _ _ _ s = SState.err ~pos:dummy_pos s (sprintf "Error [xeval] No ternary operators yet, so what's this \"%s\"" op)

let op3 ~pos op v1 v2 v3 s =
  let f = match op with
  | op -> err_op3 ~op
  in
  s |> f ~pos v1 v2 v3
