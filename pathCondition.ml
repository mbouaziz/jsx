
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
    let jsVal = z "jsVal"
  end

  module F = (* functions *)
  struct
    let conv = StringMap.from_list ["+","js+";"-","js-";"*","js*";"/","js/";"%","js%";"|","js-or";"&","js-and";"^","js-xor";"<<","js-shl";">>","js-ashr";">>>","js-lshr";"<","js<";"<=","js<=";">","js>";">=","js>=";"bool!","bool_neg";"=","smt="]
    let c x = match StringMap.find_opt x conv with
    | Some x -> x | None -> x
    let z = c @> env_find ~kind:"functions" env.funs

    let vUndefined = z "VUndefined"
    let vNull = z "VNull"
    let vBool = z "VBool"
    let vInt = z "VInt"
    let vNum = z "VNum"
    let vString = z "VString"
    let vRef = z "VRef"
    let vErr = z "VErr"
    let mk_string = z "mk-string"

    let isUndefined = z "is_VUndefined"
    let isNull = z "is_VNull"
    let isBool = z "is_VBool"
    let isInt = z "is_VInt"
    let isNum = z "is_VNum"
    let isString = z "is_VString"
    let isErr = z "is_VErr"

    let valToBool = z "ValToBool"
    let notValToBool = z "NotValToBool"
    let is_callable = z "is-callable"
    let is_primitive = z "primitive?"
    let int_to_bool = z "int->bool"
    let num_to_bool = z "num->bool"
    let str_to_bool = z "str->bool"
    let prim_to_bool = z "prim->bool"
    let prim_to_num = z "prim->num"
    let prim_to_str = z "prim->str"
    let surface_typeof = z "surface-typeof"
    let typeof = z "typeof"

    let abs_eq = z "abs="
    let stx_eq = z "stx="
    let string_plus = z "string+"
    let add = z "js+"
    let sub = z "js-"
    let get_field = z "get-field"
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
    and app_to_string app =
      let fd = Z3.get_app_decl ctx app in
      let args = Z3.get_app_args ctx app in
      if f_eq fd F.mk_string then
	let args_str = Array.map ast_to_string args in
	let len = int_of_string (args_str.(0)) in
	let bi = Big_int.big_int_of_string (args_str.(1)) in
	let s = String.of_big_int bi in
	sprintf "%S[%d]" s len
      else if f_eq fd F.vUndefined then
	"undefined"
      else if f_eq fd F.vNull then
	"null"
      else if f_eq fd F.vBool
	   || f_eq fd F.vInt
           || f_eq fd F.vNum
           || f_eq fd F.vString then
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
    let pop () =
      Z3Env._log (lazy "(pop)\n");
      Z3.pop ctx 1
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
    let simplify ast =
      Z3Env._log (lazy (sprintf "(simplify\n  %s)\n" (String.interline "  " (Z3.ast_to_string ctx ast))));
      Z3.simplify ctx ast
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
    | Z3Env.Macro m -> m
    | Z3Env.MacroConst a -> fun _ -> a

  let mk_bv_of_str bv_size s = Z3.mk_numeral ctx s (Z3.mk_bv_sort ctx bv_size)
  let mk_bv_of_int bv_size i = Z3.mk_int ctx i (Z3.mk_bv_sort ctx bv_size)
  let mk_int_of_int i = Z3.mk_int ctx i int_sort
  let mk_real s =
    let h, l = String.split2 '.' s in
    Z3Env.Helpers.ast_of_decimal ctx h l

  let mk_var name sort = Z3.mk_const ctx (Z3.mk_string_symbol ctx name) sort

  let simplify = Cmd.simplify

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
      else if f_eq fd F.vErr then
	failwith "NYI: VErr to svalue"
  (* problem: with macros, we lost all traces of functions *)
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
  module Simplify :
  sig
    val svalue : ('t, 's) SymbolicValue._svalue -> ('t, 's) SymbolicValue._svalue
  end

  val check_sat : ('t, 's) pathcomponent list -> lbool
  val check_sat_model : ('t, 's) pathcomponent list -> lbool * SMT.model
end =
struct
  module ToSMT =
  struct
    open Env
    open SymbolicValue

    module Symbols =
    struct
      let any sid = "sA" ^ (SId.to_string sid)
      let bool sid = "sB" ^ (SId.to_string sid)
      let int sid = "sI" ^ (SId.to_string sid)
      let num sid = "sN" ^ (SId.to_string sid)
      let str sid = "sS" ^ (SId.to_string sid)
      let _ref sid = "sR" ^ (SId.to_string sid)
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
      | CUndefined -> SMT.mk_appf F.vUndefined [||]
      | CNull -> SMT.mk_appf F.vNull [||]
      | CBool b -> SMT.mk_appf F.vBool [| mk_bool b |]
      | CInt i -> SMT.mk_appf F.vInt [| IntRepr.mk i |]
      | CNum n -> SMT.mk_appf F.vNum [| NumRepr.mk n |]
      | CString s -> SMT.mk_appf F.vString [| StrRepr.mk s |]
      | CRegexp _ -> assert false

    let of_op1 op x =
      SMT.mk_appf (F.z op) [| x |]
 (* match op with *)
    (* | "is-callable" -> SMT.mk_appf F.is_callable [| x |] *)
    (* | "primitive?" -> SMT.mk_appf F.is_primitive [| x |] *)
    (* | "prim->num" -> SMT.mk_appf F.prim_to_num [| x |] *)
    (* | "prim->str" -> SMT.mk_appf F.prim_to_str [| x |] *)
    (* | "surface-typeof" -> SMT.mk_appf F.surface_typeof [| x |] *)
    (* | "typeof" -> SMT.mk_appf F.typeof [| x |] *)
    (* | _ -> failwith (sprintf "No SMT implementation for unary operator \"%s\"" op) *)

    let of_op2 op x y =
      SMT.mk_appf (F.z op) [| x ; y |]
 (* match op with *)
    (* | "abs=" -> SMT.mk_appf F.abs_eq [| x ; y |] *)
    (* | "stx=" -> SMT.mk_appf F.stx_eq [| x ; y |] *)
    (* | "string+" -> SMT.mk_appf F.string_plus [| x ; y |] *)
    (* | "+" -> SMT.mk_appf F.add [| x ; y |] *)
    (* | "-" -> SMT.mk_appf F.sub [| x ; y |] *)
    (* | "get-field" -> SMT.mk_appf F.get_field [| x ; y |] *)
    (* | _ -> failwith (sprintf "No SMT implementation for binary operator \"%s\"" op) *)

    let of_op3 op x y z = match op with
    | _ -> failwith (sprintf "No SMT implementation for ternary operator \"%s\"" op)

    let of_app v l = failwith "No SMT implementation for symbolic applications"

    let sid_var sid = SMT.mk_var (Symbols.any sid) S.jsVal
    let sid_bool_var sid = SMT.mk_var (Symbols.bool sid) SMT.bool_sort
    let sid_int_var sid = SMT.mk_var (Symbols.int sid) IntRepr.sort
    let sid_num_var sid = SMT.mk_var (Symbols.num sid) NumRepr.sort
    let sid_str_var sid = SMT.mk_var (Symbols.str sid) StrRepr.sort
    let sid_ref_var sid = SMT.mk_var (Symbols._ref sid) RefRepr.sort

    let rec of_typed_symb = function
      | TBool, SId sid -> SMT.mk_appf F.vBool [| sid_bool_var sid |]
      | TInt, SId sid -> SMT.mk_appf F.vInt [| sid_int_var sid |]
      | TNum, SId sid -> SMT.mk_appf F.vNum [| sid_num_var sid |]
      | TStr, SId sid -> SMT.mk_appf F.vString [| sid_str_var sid |]
      | TRef, SId sid -> SMT.mk_appf F.vRef [| sid_ref_var sid |]
      | TAny, SId sid -> sid_var sid
      | _, SOp1 (o, x) -> of_op1 o (of_svalue x)
      | _, SOp2 (o, x, y) -> of_op2 o (of_svalue x) (of_svalue y)
      | _, SOp3 (o, x, y, z) -> of_op3 o (of_svalue x) (of_svalue y) (of_svalue z)
      | _, SApp (v, l) -> of_app (of_svalue v) (List.map of_svalue l)
    and of_svalue = function
      | SConst c -> of_const c
      | SHeapLabel heaplabel -> SMT.mk_appf F.vRef [| RefRepr.mk heaplabel |]
      | SSymb ts -> of_typed_symb ts
      | SClosure _ -> assert false (* really shouldn't happen, really?? *)

    let mk_to_bool x = SMT.mk_appf F.valToBool [| x |]
    let mk_not_to_bool x = SMT.mk_appf F.notValToBool [| x |]

    let of_predicate = function
      | PredVal (SSymb (TBool, SId sid)) -> sid_bool_var sid
      | PredVal v -> mk_to_bool (of_svalue v)
      | PredNotVal (SSymb (TBool, SId sid)) -> SMT.mk_not (sid_bool_var sid)
      | PredNotVal v -> mk_not_to_bool (of_svalue v)
  end

  module Symbols =
  struct
    open SymbolicValue
    open ToSMT.Symbols

    let rec of_svalue v m = match v with
    | SSymb ts -> of_typed_symb ts m
    | _ -> m
    and of_typed_symb ts m = match ts with
    | TAny, SId sid -> StringMap.add (SId.to_string sid) (any sid) m
    | TBool, SId sid -> StringMap.add (SId.to_string sid) (bool sid) m
    | TInt, SId sid -> StringMap.add (SId.to_string sid) (int sid) m
    | TNum, SId sid -> StringMap.add (SId.to_string sid) (num sid) m
    | TStr, SId sid -> StringMap.add (SId.to_string sid) (str sid) m
    | TRef, SId sid -> StringMap.add (SId.to_string sid) (_ref sid) m
    | _, SOp1 (_, v) -> of_svalue v m
    | _, SOp2 (_, v1, v2) -> m |> of_svalue v1 |> of_svalue v2
    | _, SOp3 (_, v1, v2, v3) -> m |> of_svalue v1 |> of_svalue v2 |> of_svalue v3
    | _, SApp (v, l) -> m |> of_svalue v |> List.fold_leftr of_svalue l

    let of_pathcomponent m { pred ; _ } = match pred with
    | PredVal v | PredNotVal v -> of_svalue v m
  end

  let assert_predicate pred =
    let ast = ToSMT.of_predicate pred in
    SMT.Cmd.assert_cnstr ast

  let assert_pathcomponent { pred ; _ } = assert_predicate pred

  let check_sat pcl =
    SMT.Cmd.push ();
    List.iter assert_pathcomponent pcl;
    let res = SMT.Cmd.check () in
    SMT.Cmd.pop ();
    res

  let check_sat_model pcl =
    SMT.Cmd.push ();
    List.iter assert_pathcomponent pcl;
    let res, m = SMT.Cmd.check_and_get_model () in
    SMT.Cmd.pop ();
    res, m

  module Simplify =
  struct
    open SymbolicValue

    let svalue = function
      (* | SSymb (typ, symb) -> *)
      (* SMT.Cmd.push (); *)
      (* let sid = SId.from_string "_simplify_" in *)
      (* SMT.Cmd.assert_cnstr (SMT.mk_eq (ToSMT.sid_var sid) (ToSMT.of_svalue (SSymb symb))); *)
      (* let res, m = SMT.Cmd.check_and_get_model () in *)
      (* print_endline (Z3.model_to_string Env.ctx m); *)
      (* SMT.Cmd.pop (); *)
      (* if res = L_TRUE then *)
      (* 	let smt_sid = ToSMT.Symbols.any sid in *)
      (* 	match SMT.Model.get_constant m smt_sid with *)
      (* 	| None -> SSymb symb *)
      (* 	| Some ast -> try SMT.to_svalue ast with _ -> SSymb symb *)
      (* else *)
	(* SSymb symb *)
      (* try symb |> ToSMT.of_symb |> SMT.simplify |> SMT.to_svalue with *)
      (* 	_ -> SSymb symb *)
      | v -> v
  end

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
  | SHeapLabel _ -> Some true
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

  let add ?(pred_kind=PPath) p pc =
    match simplify_add p pc with
    | Some pc_opt -> pc_opt
    | None ->
	let pcl = { pred = p; pred_kind }::pc.big_and in
	if !Options.opt_smt then begin
	  (* use the SMT solver to check the satisfiability *)
	  let sat, model_opt = check_sat_model_opt pcl in
	  if sat = L_FALSE then None
	  else Some { big_and = pcl; sat; smt = true; model = model_opt }
	end else
	  Some { big_and = pcl; sat = L_UNDEF; smt = false; model = None }

  let add_assumption v pc = add ~pred_kind:PAssume (PredVal v) pc

  (* add_assertion returns
     None if the assertion is surely false
     Some (L_FALSE, pc) if the assertion is surely true (pc unchanged)
     Some (L_UNDEF, pc) if the assertion cannot be checked (assumption added to pc)
     Some (L_TRUE, pc) if the assertion can be true (assumption added to pc)
  *)
  let add_assertion v pc =
    match simplify_add (PredVal v) pc with
    | Some None -> None
    | Some (Some pc) -> Some (L_FALSE, pc)
    | None ->
	if !Options.opt_smt then begin
	  (* use the SMT solver to check the validity *)
	  let pcl_neg = { pred = PredNotVal v; pred_kind = PAssert }::pc.big_and in
	  let unsat = VC.check_sat pcl_neg in
	  if unsat = L_FALSE then
	    Some (L_FALSE, pc)
	  else
	    let pcl = { pred = PredVal v; pred_kind = PAssert }::pc.big_and in
	    let sat, model_opt = check_sat_model_opt pcl in
	    if sat = L_FALSE then None
	    else Some (unsat, { big_and = pcl; sat; smt = true; model = model_opt })
	end else
	  let pcl = { pred = PredVal v; pred_kind = PAssert }::pc.big_and in
	  Some (L_UNDEF, { big_and = pcl; sat = L_UNDEF; smt = false; model = None })

  let branch v pc = add (PredVal v) pc, add (PredNotVal v) pc (* TODO: do better *)
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
