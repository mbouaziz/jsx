
open MyPervasives

module Env =
struct
  open Z3Env

  let env =
    run_under_backtrace (
      fun () ->
	let cfg = Z3.mk_config () in
	Z3.set_param_value cfg "MODEL" "true";
	(* Z3.set_param_value cfg ... ... (\* see z3 -ini? *\) *)
	let ctx = Z3.mk_context cfg in
	Options.OtherOptions._get_ctx := (fun () -> ctx);
	at_exit (fun () -> Z3.del_context ctx; Z3.del_config cfg);
	Z3.set_ast_print_mode ctx Z3.PRINT_SMTLIB2_COMPLIANT;
	let env = LoadSMTEnv.load (empty_env ctx) in
	env
    ) Options.check_print_backtrace

  let ctx = env.context

  let env_find ~kind m x = match StringMmap.find_opt x m with
  | Some v -> v
  | None -> failwith (sprintf "Unable to find \"%s\" in the %s of \"%s\"" x kind Z3Env.env_filename)

  module S = (* sorts *)
  struct
    let z = env_find ~kind:"sorts" env.sorts

    let sInt = z "int"
    let sNum = z "num"
    let sString = z "string"
    let sHeapLabel = z "heaplabel"
    let jsNumber = z "jsNumber"
    let jsPrim = z "jsPrim"
    let jsVal = z "jsVal"
  end

  module F = (* functions *)
  struct
    type deduction_kind = HighToLow | LowToHigh
    type f_type = SymbolicValue.Typ.f_type
    type deduction = { ded_kind : deduction_kind ; pres : f_type list ; abs : f_type list ; ded_macro : Z3Env.macro_ex ; ded_priority : int }

    let typ_char = let open SymbolicValue in let open Typ in ['R', T tA; 'V', T tVAny; 'P', T tPAny; 'B', T tBool; 'M', T tNAny; 'I', T tInt; 'N', T tNum; 'S', T tStr; 'O', T tRef; 'U', TUndef; 'L', TNull]
    let string_of_typ =
      let char_typ = List.assoc_flip typ_char in
      let char_of_typ t = List.assoc t char_typ in
      function ftyp ->
	ftyp |> Array.map char_of_typ |> String.of_array

    let op_map =
      let open SymbolicValue.Typ in
      let op_conv = ["|","js-or";"bool!","bool_neg"] in
      let typ_chars = List.map fst typ_char in
      let typ_of_char ~loc c = try List.assoc c typ_char with
	Not_found -> failwith (sprintf "In %s, %C is not a valid type character" loc c) in
      let typ_of_str ~loc = String.to_array @> Array.map (typ_of_char ~loc) in
      let add_op_to_map name f op_map =
	let basename, s_typ = String.split2 '~' name in
	if String.length s_typ < 1 then op_map
	else
	  let basename = match List.assoc_opt basename op_conv with
	    None -> basename | Some basename -> basename in
	  let m = try StringMap.find basename op_map with
	    Not_found -> TypMap.empty in
	  let loc = sprintf "operator %S" name in
	  let m = TypMap.add (typ_of_str ~loc s_typ) f m in
	  StringMap.add basename m op_map
      in
      let add_ded_to_map name f ded_map =
	let basename, ded_rule = String.split2 '.' name in
	if basename <> "deduce" then ded_map
	else match f with
	| MacroEx ded_macro ->
	    let ded_kind, sep =
	      if String.contains ded_rule '<' then HighToLow, '<'
	      else if String.contains ded_rule '>' then LowToHigh, '>'
	      else failwith (sprintf "Deduction rule %S badly formatted" name)
	    in
	    let p_star = String.index_or_length ded_rule '*' in
	    let ded_priority = String.length ded_rule - p_star in
	    let ded_rule = String.left ded_rule p_star in
	    let typ_ded = String.before_char ded_rule sep in
	    let typ_pres = String.nsplit_char '+' (String.between_chars ded_rule sep '-') in
	    let typ_abs = String.nsplit_char '-' (String.between_chars ded_rule '-' '*') in
	    let arity = String.length typ_ded in
	    let bad_arity = List.exists (fun t -> String.length t <> arity) in
	    if bad_arity typ_pres || bad_arity typ_abs then
	      failwith (sprintf "Deduction rule %S badly formatted" name);
	    let var_list = List.filter (String.contains ded_rule) ['X'; 'Y'; 'Z'] in
	    let ded_instances ded_list =
	      let ded_instance ded_list var =
		let ded_repl (inst, (t, (tl1, tl2))) =
		  let repl = String.repl_char var inst in
		  repl t, (List.map repl tl1, List.map repl tl2)
		in
		List.map ded_repl (List.product typ_chars ded_list)
	      in
	      List.fold_left ded_instance ded_list var_list
	    in
	    let ded_str_list = ded_instances [typ_ded, (typ_pres, typ_abs)] in
	    let loc = sprintf "deduction rule %S" name in
	    let add_ded ded_map (typ_ded, (typ_pres, typ_abs)) =
	      let typ_ded = typ_of_str ~loc typ_ded in
	      let deduction = {
		pres = List.map (typ_of_str ~loc) typ_pres ;
		abs = List.map (typ_of_str ~loc) typ_abs ;
		ded_kind ; ded_macro ; ded_priority } in
	      let ded_list = try TypMap.find typ_ded ded_map with
		Not_found -> [] in
	      TypMap.add typ_ded (deduction::ded_list) ded_map
	    in
	    List.fold_left add_ded ded_map ded_str_list
	| _ -> failwith (sprintf "Deduction rule %S is not a macro" name)
      in
      let ded_map = StringMmap.fold add_ded_to_map env.funs TypMap.empty in
      let gen_types =
	let h = Hashtbl.create 1 in
	let rec aux = function
	  | 0 -> [[]]
	  | n -> assert (n > 0);
	      aux (n-1)
	      |> List.map (fun ft -> List.rev_map (fun t -> t::ft) ex_types)
	      |> List.flatten
	in
	function arity -> try Hashtbl.find h arity with
	  Not_found ->
	    let l = aux arity |> List.map Array.of_list in
	    let t = l, List.rev l in
	    Hashtbl.add h arity t;
	    t
      in
      let use_deductions name m op_map =
	let arity = Array.length (fst (TypMap.choose m)) - 1 in
	let use_deds ded_kind types m =
	  let use_ded m ded_type =
	    if TypMap.mem ded_type m then m
	    else
	      let ded_list = match TypMap.find_opt ded_type ded_map with
	      | None -> []
	      | Some ded_list -> ded_list in
	      let apply_ded ded =
		let pres t = TypMap.mem t m in
		if ded.ded_kind <> ded_kind || not (List.for_all pres ded.pres) || List.exists pres ded.abs then None
		else
		  let args = ded.pres |> Array.of_list |> Array.map (fun t -> TypMap.find t m) in
		  let n = Array.length args in
		  let f_arity = n + arity in
		  Z3Env._log (lazy (sprintf "; deduced %s~%s from %s\n" name (string_of_typ ded_type) (String.concat ", " (List.map (fun t -> sprintf "%s~%s" name (string_of_typ t)) ded.pres))));
		  let f ast_args =
		    if Array.length ast_args <> arity then
		      failwith (sprintf "Generated define %s~%s called with %d arguments instead of %d\n" name (string_of_typ ded_type) (Array.length ast_args) arity)
		    else
		      let args = Array.init f_arity (fun i -> if i < n then args.(i) else Z3Env.ConstAst ast_args.(i-n)) in
		      ded.ded_macro args
		  in
		  Some ((ded.ded_priority, ded.pres), Z3Env.MacroAst f)
	      in
	      let cmp_fst (x,_) (y,_) = Pervasives.compare x y in
	      match List.sort cmp_fst (List.filter_map apply_ded ded_list) with
	      | [] -> m
	      | [_, f] -> TypMap.add ded_type f m
	      | ((p0, _), f)::((p1, _), _)::_ when p0 < p1 -> TypMap.add ded_type f m
	      | (((p0, _), _)::_) as l -> failwith (sprintf "More than one deduction rule with the same priority applicable for %s~%s : %s" name (string_of_typ ded_type) (l |> List.map fst |> List.filter (fst @> ((=) p0)) |> List.map (snd @> List.map string_of_typ @> String.concat ", " @> sprintf "(%s)") |> String.concat "; "))
	  in
	  List.fold_left use_ded m types
	in
	let types, rev_types = gen_types (arity+1) in
	StringMap.add name (m |> use_deds HighToLow types |> use_deds LowToHigh rev_types) op_map
      in
      let op_map = StringMmap.fold add_op_to_map env.funs StringMap.empty in
      StringMap.fold use_deductions op_map StringMap.empty

    let op name typ = match StringMap.find_opt name op_map with
    | None -> failwith (sprintf "Unable to find operator %S in %S" name Z3Env.env_filename)
    | Some m -> match SymbolicValue.Typ.TypMap.find_opt typ m with
      | None -> failwith (sprintf "Operator %s~%s cannot be found or deduced" name (string_of_typ typ))
      | Some f -> f

    let z = env_find ~kind:"functions" env.funs

    let nReal = z "NReal"
    let nNaN = z "NNaN"
    let nInfty = z "NInfty"
    let vUndefined = z "VUndefined"
    let vNull = z "VNull"
    let vBool = z "VBool"
    let vInt = z "VInt"
    let vNum = z "VNum"
    let vNumber = z "VNumber"
    let vString = z "VString"
    let vRef = z "VRef"
    let vPrim = z "VPrim"
    let rVal = z "RVal"
    let rErr = z "RErr"
    let mk_string = z "mk-string"
  end
end

type lbool = L_TRUE | L_FALSE | L_UNDEF

module SMT =
struct
  type ast = Z3.ast
  type model = Z3.model

  let ctx = Env.ctx

  let f_eq fd = function
    | Z3Env.FuncDecl fd0 -> Z3.is_eq_func_decl ctx fd fd0
    | _ -> false

  module Model =
  struct
    open Env

    let constants model =
      let of_fd fd =
	let symb = Z3.get_decl_name ctx fd in
	match Z3.symbol_refine ctx symb with
	| Z3.Symbol_string symb_str ->
	    let b, ast = Z3.eval_func_decl ctx model fd in
	    assert b;
	    Some (symb_str, ast)
	| _ -> None
      in
      Z3.get_model_constants ctx model
      |> Array.to_list
      |> List.filter_map of_fd

    let get_constant model name =
      let of_fd fd =
	let symb = Z3.get_decl_name ctx fd in
	match Z3.symbol_refine ctx symb with
	| Z3.Symbol_string symb_str when symb_str = name ->
	    let b, ast = Z3.eval_func_decl ctx model fd in
	    assert b;
	    Some ast
	| _ -> None
      in
      Z3.get_model_constants ctx model
      |> Array.find_map of_fd

    let rec ast_to_string ast =
      match Z3.get_ast_kind ctx ast with
      | Z3.NUMERAL_AST -> Z3.get_numeral_string ctx ast
      | Z3.APP_AST -> app_to_string (Z3.to_app ctx ast)
      | _ -> Z3.ast_to_string ctx ast
    and ast_to_bool ast =
      match Z3.get_bool_value ctx ast with
      | Z3.L_TRUE -> true
      | Z3.L_FALSE -> false
      | Z3.L_UNDEF -> assert false
    and app_to_string app =
      let fd = Z3.get_app_decl ctx app in
      let args = Z3.get_app_args ctx app in
      if f_eq fd F.mk_string then
	let args_str = Array.map ast_to_string args in
	let len_str = args_str.(0) in
	let bi = Big_int.big_int_of_string (args_str.(1)) in
	let s = String.of_big_int bi in
	sprintf "%S[%s]" s len_str
      else if f_eq fd F.vUndefined then
	"undefined"
      else if f_eq fd F.vNull then
	"null"
      else if f_eq fd F.vRef then
	sprintf "heap[%s]" (ast_to_string args.(0))
      else if f_eq fd F.nNaN then
	"NaN"
      else if f_eq fd F.nInfty then
	sprintf "%cInfinity" (if ast_to_bool args.(0) then '+' else '-')
      else if f_eq fd F.vBool
	   || f_eq fd F.vInt
           || f_eq fd F.nReal
           || f_eq fd F.vNum
	   || f_eq fd F.vNumber
           || f_eq fd F.vString
	   || f_eq fd F.vPrim
           || f_eq fd F.rVal
	   || f_eq fd F.rErr then
	ast_to_string args.(0)
      else
	let ast = Z3.app_to_ast ctx app in
	Z3.ast_to_string ctx ast
  end

  let lbool_of_lbool = function
    | Z3.L_TRUE -> L_TRUE
    | Z3.L_FALSE -> L_FALSE
    | Z3.L_UNDEF -> L_UNDEF

  let to_string ast = Z3.ast_to_string ctx ast
  let model_to_string m = Z3.model_to_string ctx m

  module Cmd =
  struct
    let push () =
      Z3Env._log (lazy "(push)\n");
      Z3.push ctx
    let pop ?(n=1) () =
      Z3Env._log (lazy (sprintf "(pop %d)\n" n));
      Z3.pop ctx n
    let assert_cnstr ast =
      Z3Env._log (lazy (sprintf "(assert\n  %s)\n" (String.interline "  " (Z3.ast_to_string ctx ast))));
      Z3.assert_cnstr ctx ast
    let check () =
      Z3Env._log (lazy "(check-sat)\n");
      lbool_of_lbool (Z3.check ctx)
    let check_and_get_model () =
      Z3Env._log (lazy "(check-sat)\n(get-info model)\n");
      let lbool, m = Z3.check_and_get_model ctx in
      (lbool_of_lbool lbool, m)
  end

  let bool_sort = Z3.mk_bool_sort ctx
  let int_sort = Z3.mk_int_sort ctx
  let real_sort = Z3.mk_real_sort ctx

  let mk_true () = Z3.mk_true ctx
  let mk_false () = Z3.mk_false ctx
  let mk_not = Z3.mk_not ctx
  let mk_eq = Z3.mk_eq ctx
  let mk_app = Z3.mk_app ctx
  let mk_appf = function
    | Z3Env.FuncDecl f -> Z3.mk_app ctx f
    | Z3Env.MacroAst m -> m
    | Z3Env.MacroEx m -> (Array.map (fun a -> Z3Env.ConstAst a)) @> m
    | Z3Env.ConstAst a -> fun _ -> a

  let mk_bv_of_str bv_size s = Z3.mk_numeral ctx s (Z3.mk_bv_sort ctx bv_size)
  let mk_bv_of_int bv_size i = Z3.mk_int ctx i (Z3.mk_bv_sort ctx bv_size)
  let mk_int_of_int i = Z3.mk_int ctx i int_sort
  let mk_real s =
    let h, l = String.split2 '.' s in
    Z3Env.Helpers.ast_of_decimal ctx h l

  let mk_var name sort = Z3.mk_const ctx (Z3.mk_string_symbol ctx name) sort

  module ToSValue =
  struct
    open SymbolicValue
    open JS.Syntax
    open Env

    let rec ast_to_svalue ast =
      let sort = Z3.get_sort ctx ast in
      match Z3.get_ast_kind ctx ast with
      | Z3.NUMERAL_AST ->
	  begin match Z3.get_sort_kind ctx sort with
	  | Z3.REAL_SORT -> SConst (CNum (float_of_string (Z3.get_numeral_string ctx ast)))
	  | Z3.BV_SORT -> let ok, i = Z3.get_numeral_int ctx ast in
	    assert ok; SConst (CInt i)
	  | _ -> assert false
	  end
      | Z3.APP_AST -> app_to_svalue (Z3.to_app ctx ast)
      | Z3.VAR_AST -> assert false
      | Z3.QUANTIFIER_AST -> assert false
      | Z3.UNKNOWN_AST -> assert false
    and app_to_svalue app =
      let fd = Z3.get_app_decl ctx app in
      let args = Z3.get_app_args ctx app in
      if f_eq fd F.mk_string then
	let ok, len = Z3.get_numeral_int ctx args.(0) in
	assert (ok && len <= 16);
	let str = Z3.get_numeral_string ctx args.(1) in
	let bi = Big_int.big_int_of_string str in
	let s = String.of_big_int bi in
	let l = String.length s in
	assert (l <= len);
	let s = String.pad_left '\000' len s in
	SConst (CString s)
      else if f_eq fd F.vUndefined then
	SConst CUndefined
      else if f_eq fd F.vNull then
	SConst CNull
      else if f_eq fd F.vBool
           || f_eq fd F.vInt
	   || f_eq fd F.vNum
	   || f_eq fd F.vString then
	ast_to_svalue args.(0)
      else if f_eq fd F.vRef then
	let ok, heaplabel = Z3.get_numeral_int ctx args.(0) in
	assert ok;
	SHeapLabel (HeapLabel.of_int heaplabel)
      else if f_eq fd F.rErr then
	failwith "NYI: RErr to svalue"
  (* problem: with macros/defines, we lost all traces of functions *)
      else match Z3.get_decl_kind ctx fd with
      | Z3.OP_TRUE -> SConst (CBool true)
      | Z3.OP_FALSE -> SConst (CBool false)
      | _ -> assert false
  end

  let to_svalue = ToSValue.ast_to_svalue
end

type 'a _predicate =
  | PredVal of 'a
  | PredNotVal of 'a
type pred_kind = PPath | PAssume | PAssert
type 'a _pathcomponent = { pred : 'a _predicate ; pred_kind : pred_kind }
type 'a _pathcondition = { big_and : 'a _pathcomponent list ; sat : lbool ; smt : bool ; model : SMT.model option }

type ('t, 's) predicate = ('t, 's) SymbolicValue._svalue _predicate
type ('t, 's) pathcomponent = ('t, 's) SymbolicValue._svalue _pathcomponent
type ('t, 's) pathcondition = ('t, 's) SymbolicValue._svalue _pathcondition

module VC :
sig
  module Symbols :
  sig
    val of_pathcomponent : string StringMap.t -> ('t, 's) pathcomponent -> string StringMap.t
  end

  val assert_pathcomponent : ('t, 's) pathcomponent -> unit
  val check_sat : ('t, 's) pathcomponent list -> lbool
  val check_sat_model : ('t, 's) pathcomponent list -> lbool * SMT.model
  val check_pred_sat : ('t, 's) predicate -> lbool
  val check_pred_sat_model : ('t, 's) predicate -> lbool * SMT.model
end =
struct
  module ToSMT =
  struct
    open Env
    open SymbolicValue

    module Symbols =
    struct
      let bool sid = "sB" ^ (SId.to_string sid)
      let int sid = "sI" ^ (SId.to_string sid)
      let num sid = "sN" ^ (SId.to_string sid)
      let number sid = "sM" ^ (SId.to_string sid)
      let str sid = "sS" ^ (SId.to_string sid)
      let prim sid = "sP" ^ (SId.to_string sid)
      let _ref sid = "sO" ^ (SId.to_string sid)
      let vany sid = "sV" ^ (SId.to_string sid)
      let fields sid = "sF" ^ (SId.to_string sid)
    end

    module IntRepr =
    struct (* int as BitVec[32] *)
      let bv_size = 32

      let sort = S.sInt
      let mk i = SMT.mk_bv_of_int bv_size i
    end

    module NumRepr =
    struct
      let sort = S.sNum
      let mk n = SMT.mk_real (sprintf "%012.12f" n)
    end

    module StrRepr =
    struct
      let sort = S.sString
      let mk s =
	let l = SMT.mk_bv_of_int 32 (String.length s) in
	let bi = String.to_big_int (String.left s 16) in
	let b = SMT.mk_bv_of_str 128 (Big_int.string_of_big_int bi) in
	SMT.mk_appf F.mk_string [| l ; b |]
    end

    module RefRepr =
    struct
      let sort = S.sHeapLabel
      let mk heaplabel = SMT.mk_int_of_int (HeapLabel.to_int heaplabel)
    end

    let mk_bool = function
      | true -> SMT.mk_true ()
      | false -> SMT.mk_false ()

    let of_const = let open JS.Syntax in function
      | CUndefined -> tPAny, SMT.mk_appf F.vUndefined [||]
      | CNull -> tPAny, SMT.mk_appf F.vNull [||]
      | CBool b -> tBool, mk_bool b
      | CInt i -> tInt, IntRepr.mk i
      | CNum n -> tNum, NumRepr.mk n
      | CString s -> tStr, StrRepr.mk s
      | CRegexp _ -> assert false

    let _t t = SymbolicValue.Typ.T t
    let of_op1 op tout (tx, x) = SMT.mk_appf (F.op op [|_t tx; _t tout|]) [| x |]
    let of_opF1 op tout tp (tx, x) = SMT.mk_appf (F.op op [| SymbolicValue.Typ.TFields; _t tx; _t tout|]) [| tp; x |]
    let of_op2 op tout (tx, x) (ty, y) = SMT.mk_appf (F.op op [|_t tx; _t ty; _t tout|]) [| x ; y |]
    let of_op3 op tout x y z = failwith (sprintf "No SMT implementation for ternary operator \"%s\"" op)
    let of_app v tout l = failwith "No SMT implementation for symbolic applications"

    let sid_bool_var sid = SMT.mk_var (Symbols.bool sid) SMT.bool_sort
    let sid_int_var sid = SMT.mk_var (Symbols.int sid) IntRepr.sort
    let sid_num_var sid = SMT.mk_var (Symbols.num sid) NumRepr.sort
    let sid_number_var sid = SMT.mk_var (Symbols.number sid) S.jsNumber
    let sid_str_var sid = SMT.mk_var (Symbols.str sid) StrRepr.sort
    let sid_prim_var sid = SMT.mk_var (Symbols.prim sid) S.jsPrim
    let sid_ref_var sid = SMT.mk_var (Symbols._ref sid) RefRepr.sort
    let sid_val_var sid = SMT.mk_var (Symbols.vany sid) S.jsVal

    let rec of_typed_symb = function
      | TV (TP TBool), SId sid -> tBool, sid_bool_var sid
      | TV (TP (TN TInt)), SId sid -> tInt, sid_int_var sid
      | TV (TP (TN TNum)), SId sid -> tNum, sid_num_var sid
      | TV (TP (TN TNAny)), SId sid -> tNAny, sid_number_var sid
      | TV (TP TStr), SId sid -> tStr, sid_str_var sid
      | TV (TP TPAny), SId sid -> tPAny, sid_prim_var sid
      | TV TRef, SId sid -> tRef, sid_ref_var sid
      | TV TVAny, SId sid -> tVAny, sid_val_var sid
      | _, SId _ -> assert false
      | typ, SOp1 (o, x) -> typ, of_op1 o typ (of_svalue x)
      | typ, SOpF1 (o, p, x) -> typ, of_opF1 o typ (of_props p) (of_svalue x)
      | typ, SOp2 (o, x, y) -> typ, of_op2 o typ (of_svalue x) (of_svalue y)
      | typ, SOp3 (o, x, y, z) -> typ, of_op3 o typ (of_svalue x) (of_svalue y) (of_svalue z)
      | typ, SApp (v, l) -> typ, of_app typ (of_svalue v) (List.map of_svalue l)
    and of_svalue = function
      | SConst c -> of_const c
      | SHeapLabel heaplabel -> tRef, RefRepr.mk heaplabel
      | SSymb ts -> of_typed_symb ts
      | SClosure _ -> assert false (* really shouldn't happen, really?? *)
    and of_props { pure_actions; symb_fields; concrete_fields } =
      failwith "ToSMT.of_props"

    let of_predicate = function
      | PredVal v -> of_op1 "val->bool" tBool (of_svalue v)
      | PredNotVal v -> of_op1 "not-val->bool" tBool (of_svalue v)
  end

  module Symbols =
  struct
    open SymbolicValue
    open ToSMT.Symbols

    let rec of_svalue v m = match v with
    | SSymb ts -> of_typed_symb ts m
    | _ -> m
    and of_typed_symb ts m = match ts with
    | TV (TP TBool), SId sid -> StringMap.add (SId.to_string sid) (bool sid) m
    | TV (TP (TN TInt)), SId sid -> StringMap.add (SId.to_string sid) (int sid) m
    | TV (TP (TN TNum)), SId sid -> StringMap.add (SId.to_string sid) (num sid) m
    | TV (TP (TN TNAny)), SId sid -> StringMap.add (SId.to_string sid) (number sid) m
    | TV (TP TStr), SId sid -> StringMap.add (SId.to_string sid) (str sid) m
    | TV (TP TPAny), SId sid -> StringMap.add (SId.to_string sid) (prim sid) m
    | TV TRef, SId sid -> StringMap.add (SId.to_string sid) (_ref sid) m
    | TV TVAny, SId sid -> StringMap.add (SId.to_string sid) (vany sid) m
    | _, SId _ -> assert false
    | _, SOp1 (_, v) -> of_svalue v m
    | _, SOpF1 (_, p, v) -> m |> of_sprops p |> of_svalue v
    | _, SOp2 (_, v1, v2) -> m |> of_svalue v1 |> of_svalue v2
    | _, SOp3 (_, v1, v2, v3) -> m |> of_svalue v1 |> of_svalue v2 |> of_svalue v3
    | _, SApp (v, l) -> m |> of_svalue v |> List.fold_leftr of_svalue l
    and of_sprops { pure_actions; concrete_fields; symb_fields} m = m |> of_pure_actions pure_actions |> of_concrete_fields concrete_fields |> of_symb_fields symb_fields
    and of_pure_actions pa m = List.fold_left of_pure_action m pa
    and of_pure_action m = function
      | UpdateField(f, v) -> m |> of_loc_field f |> of_svalue v
      | DeleteField f -> of_loc_field f m
    and of_loc_field f m = of_svalue f m
    and of_concrete_fields cf m = IdMap.fold of_prop cf m
    and of_prop _ prop m = match prop with
    | { value = Some v; _ } -> of_svalue v m
    | { value = None; _ } -> m
    and of_symb_fields sf m = match sf with
    | Some sid -> StringMap.add (SId.to_string sid) (fields sid) m
    | None -> m

    let of_pathcomponent m { pred ; _ } = match pred with
    | PredVal v | PredNotVal v -> of_svalue v m
  end

  let assert_predicate pred =
    let ast = ToSMT.of_predicate pred in
    SMT.Cmd.assert_cnstr ast

  let assert_pathcomponent { pred ; _ } = assert_predicate pred

  let _gen_check ~_check ~_assert _x =
    SMT.Cmd.push ();
    _assert _x;
    let res = _check () in
    SMT.Cmd.pop ();
    res

  let _check ~_assert _x = _gen_check ~_check:SMT.Cmd.check ~_assert _x
  let _check_model ~_assert _x = _gen_check ~_check:SMT.Cmd.check_and_get_model ~_assert _x

  let check_pred_sat pred = _check ~_assert:assert_predicate pred
  let check_sat pcl = _check ~_assert:(List.iter assert_pathcomponent) pcl
  let check_pred_sat_model pred = _check_model ~_assert:assert_predicate pred
  let check_sat_model pcl = _check_model ~_assert:(List.iter assert_pathcomponent) pcl

end

module PC =
struct
  let pc_true = { big_and = []; sat = L_TRUE; smt = false; model = None }

  let opp = function
    | PredVal x -> PredNotVal x
    | PredNotVal x -> PredVal x

  let predval = function
    | PredVal v
    | PredNotVal v -> v

  let values { big_and ; _ } =
    let rec aux = function
      | [] -> []
      | { pred }::pcl -> (predval pred)::(aux pcl)
    in aux big_and

  let mem_pred p pcl =
    let eq_p { pred } = pred = p in
    List.exists eq_p pcl

  let reduce_const = let open JS.Syntax in function
    | CUndefined
    | CNull -> Some false
    | CBool b -> Some b
    | CInt n -> Some (n <> 0)
    | CNum n -> Some (n != nan && n <> 0.0 && n <> -0.0)
    | CString s -> Some (String.length s <> 0)
    | CRegexp _ -> Some true

  let reduce_val v pcl = let open SymbolicValue in match v with
  | SConst c -> reduce_const c
  | SHeapLabel _
  | SSymb(TV TRef, _) -> Some true
  | _ -> None

  let not_opt = function
    | None -> None
    | Some b -> Some (not b)

  let reduce p pcl = match p with
  | PredVal v -> reduce_val v pcl
  | PredNotVal v -> reduce_val v pcl |> not_opt

  let simplify_add p pc =
    match reduce p pc.big_and with
    | Some true -> Some (Some pc)
    | Some false -> Some None
    | None ->
	if mem_pred p pc.big_and then (* redundant *)
	  Some (Some pc)
	else if mem_pred (opp p) pc.big_and then (* we already have the opposite! *)
	  Some None
	else
	  None

  let check_sat_model_opt pcl =
    if !Options.opt_model then let sat, model = VC.check_sat_model pcl in sat, Some model
    else let sat = VC.check_sat pcl in sat, None

  let check_pred_sat_model_opt pred =
    if !Options.opt_model then let sat, model = VC.check_pred_sat_model pred in sat, Some model
    else let sat = VC.check_pred_sat pred in sat, None

  let smt_add_pred ?(pred_kind=PPath) pred pc =
    let sat, model = check_pred_sat_model_opt pred in
    if sat = L_FALSE then
      None
    else
      let big_and = { pred ; pred_kind }::pc.big_and in
      Some { big_and; sat; smt = true; model }

  let nosmt_add_pred ?(pred_kind=PPath) pred pc =
    let big_and = { pred ; pred_kind }::pc.big_and in
    Some { big_and; sat = L_UNDEF; smt = false; model = None }

  let add ?(pred_kind=PPath) pred pc =
    match simplify_add pred pc with
    | Some pc_opt -> pc_opt
    | None ->
	if !Options.opt_smt then begin
	  (* use the SMT solver to check the satisfiability *)
	  let big_and = { pred; pred_kind }::pc.big_and in
	  let sat, model_opt = check_sat_model_opt big_and in
	  if sat = L_FALSE then None
	  else Some { big_and; sat; smt = true; model = model_opt }
	end else
	  nosmt_add_pred ~pred_kind pred pc

  let add_assumption v pc = add ~pred_kind:PAssume (PredVal v) pc

  (* add_assertion returns
     (_, None) if the assertion is surely false
     (L_FALSE, Some pc) if the assertion is surely true (pc unchanged)
     (L_UNDEF, Some pc) if the assertion cannot be checked (assumption added to pc)
     (L_TRUE, Some pc) if the assertion can be true (assumption added to pc)
  *)
  let add_assertion v pc =
    match simplify_add (PredVal v) pc with
    | Some pc_opt -> L_FALSE, pc_opt
    | None ->
	if !Options.opt_smt then begin
	  (* use the SMT solver to check the validity *)
	  SMT.Cmd.push ();
	  List.iter VC.assert_pathcomponent pc.big_and;
	  let unsat = VC.check_pred_sat (PredNotVal v) in
	  let pc_opt =
	    if unsat = L_FALSE then Some pc
	    else smt_add_pred ~pred_kind:PAssert (PredVal v) pc
	  in
	  SMT.Cmd.pop ();
	  unsat, pc_opt
	end else
	  L_UNDEF, nosmt_add_pred ~pred_kind:PAssert (PredVal v) pc

  let branch v pc =
    match simplify_add (PredVal v) pc with
    | Some None -> None, (Some pc)
    | Some (Some pc) -> (Some pc), None
    | None ->
	if !Options.opt_smt then begin
	  SMT.Cmd.push ();
	  List.iter VC.assert_pathcomponent pc.big_and;
	  let res = smt_add_pred (PredVal v) pc, smt_add_pred (PredNotVal v) pc in
	  SMT.Cmd.pop ();
	  res
	end else
	  nosmt_add_pred (PredVal v) pc, nosmt_add_pred (PredNotVal v) pc
end

module ToString =
struct
  let sat { sat; smt; _ } =
    let c = match sat with
    | L_TRUE -> "S"
    | L_UNDEF -> "U"
    | L_FALSE -> "N"
    in
    if smt then c else String.lowercase c

  let predicate ~brackets ~string_of_svalue s = function
    | PredVal v -> string_of_svalue ~brackets s v
    | PredNotVal v -> sprintf "Not(%s)" (string_of_svalue ~brackets:false s v)

  let pathcomponent ~brackets ~pred_kind ~string_of_svalue s = function
    | { pred_kind = pk ; pred } when pk = pred_kind -> Some (predicate ~brackets ~string_of_svalue s pred)
    | _ -> None

  let generic_pc ~pred_kind opt ~string_of_svalue s { big_and ; _ } =
    if !opt then
      String.concat " /\\ " (List.rev_filter_map (pathcomponent ~brackets:true ~pred_kind ~string_of_svalue s) big_and)
    else
      ""

  let pathcondition ~string_of_svalue s = generic_pc ~pred_kind:PPath Options.opt_pathcondition ~string_of_svalue s
  let assumptions ~string_of_svalue s = generic_pc ~pred_kind:PAssume Options.opt_assumptions ~string_of_svalue s
  let assertions ~string_of_svalue s = generic_pc ~pred_kind:PAssert Options.opt_assertions ~string_of_svalue s

  let no_model ~smt = sprintf "NO MODEL (SMT solver %sabled, models %sabled)" (if smt then "en" else "dis") (if !Options.opt_model then "en" else "dis")

  let model { model; smt; _ } = match model with
  | None -> no_model ~smt
  | Some m -> SMT.model_to_string m

  let short_model { model; smt; big_and; _ } = match model with
  | None -> no_model ~smt
  | Some m ->
      let constants = StringMap.from_list (SMT.Model.constants m) in
      let string_of_symbol (sid, smt_name) =
	let str_smt = match StringMap.find_opt smt_name constants with
	| Some ast -> SMT.Model.ast_to_string ast
	| None -> "not in model ???"
	in
	sprintf "%s -> %s" sid str_smt
      in
      big_and
      |> List.fold_left VC.Symbols.of_pathcomponent StringMap.empty
      |> StringMap.to_list
      |> List.map string_of_symbol
      |> String.concat "\n"

end
