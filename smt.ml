
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

    let jsVal = z "jsVal"
  end

  module F = (* functions *)
  struct
    let z = env_find ~kind:"functions" env.funs

    let vUndefined = z "VUndefined"
    let vNull = z "VNull"
    let vBool = z "VBool"
    let vInt = z "VInt"
    let vNum = z "VNum"
    let vString = z "VString"
    let vErr = z "VErr"

    let isUndefined = z "is_VUndefined"
    let isNull = z "is_VNull"
    let isBool = z "is_VBool"
    let isInt = z "is_VInt"
    let isNum = z "is_VNum"
    let isString = z "is_VString"
    let isErr = z "is_VErr"

    let valToBool = z "ValToBool"
    let is_primitive = z "primitive?"
  end
end

type lbool = L_TRUE | L_FALSE | L_UNDEF

module SMT =
struct
  let ctx = Env.ctx

  let lbool_of_lbool = function
    | Z3.L_TRUE -> L_TRUE
    | Z3.L_FALSE -> L_FALSE
    | Z3.L_UNDEF -> L_UNDEF

  let to_string ast = Z3.ast_to_string ctx ast

  let push () = Z3.push ctx
  let pop () = Z3.pop ctx 1
  let assert_cnstr = Z3.assert_cnstr ctx
  let check () = lbool_of_lbool (Z3.check ctx)
  let check_and_get_model () = let lbool, m = Z3.check_and_get_model ctx in
  (lbool_of_lbool lbool, Z3.model_to_string ctx m)

  let mk_true () = Z3.mk_true ctx
  let mk_false () = Z3.mk_false ctx
  let mk_not = Z3.mk_not ctx
  let mk_app = Z3.mk_app ctx

  let mk_bv_of_int bv_size i = Z3.mk_int ctx i (Z3.mk_bv_sort ctx bv_size)

  let mk_var name sort = Z3.mk_const ctx (Z3.mk_string_symbol ctx name) sort
end

module VC :
sig
  (* returns true if satisfiable or unknown *)
  val check_sat : SymbolicState.PathCondition.pred -> SymbolicState.PathCondition.t -> bool
end =
struct
  open SymbolicState

  module ToSMT =
  struct
    open Env

    module IntRepr =
    struct (* int as BitVec[32] *)
      let bv_size = 32

      let mk i = SMT.mk_bv_of_int bv_size i
    end

    module NumRepr =
    struct
      let mk n = assert false (* NYI *)
    end

    module StrRepr =
    struct
      let mk s = assert false (* NYI *)
    end

    let mk_bool = function
      | true -> SMT.mk_true ()
      | false -> SMT.mk_false ()

    let of_const = let open JS.Syntax in function
      | CUndefined -> SMT.mk_app F.vUndefined [||]
      | CNull -> SMT.mk_app F.vNull [||]
      | CBool b -> SMT.mk_app F.vBool [| mk_bool b |]
      | CInt i -> SMT.mk_app F.vInt [| IntRepr.mk i |]
      | CNum n -> SMT.mk_app F.vNum [| NumRepr.mk n |]
      | CString s -> SMT.mk_app F.vString [| StrRepr.mk s |]
      | CRegexp _ -> assert false

    let of_op1 op x = match op with
    | "primitive?" -> SMT.mk_app F.is_primitive [| x |]
    | _ -> failwith (sprintf "No SMT implementation for unary operator \"%s\"" op)

    let of_op2 op x y = match op with
    | _ -> failwith (sprintf "No SMT implementation for binary operator \"%s\"" op)

    let of_op3 op x y z = match op with
    | _ -> failwith (sprintf "No SMT implementation for ternary operator \"%s\"" op)

    let of_app v l = failwith "No SMT implementation for symbolic applications"

    let rec of_symb = function
      | SId sid -> SMT.mk_var ("symb" ^ (SId.to_string sid)) S.jsVal
      | SOp1 (o, x) -> of_op1 o (of_svalue x)
      | SOp2 (o, x, y) -> of_op2 o (of_svalue x) (of_svalue y)
      | SOp3 (o, x, y, z) -> of_op3 o (of_svalue x) (of_svalue y) (of_svalue z)
      | SApp (v, l) -> of_app (of_svalue v) (List.map of_svalue l)
    and of_svalue = function
      | SConst c -> of_const c
      | SClosure _ -> assert false (* really shouldn't happen *)
      | SHeapLabel _ -> assert false (* NYI, don't know what to do now *)
      | SSymb s -> of_symb s

    let mk_to_bool x = SMT.mk_app F.valToBool [| x |]

    let of_predicate = function
      | PredVal v -> mk_to_bool (of_svalue v)
      | PredNotVal v -> SMT.mk_not (mk_to_bool (of_svalue v))

  end

  let assert_predicate pred =
    let ast = ToSMT.of_predicate pred in
    print_endline (sprintf "AST<<%s>>\n" (SMT.to_string ast));
    SMT.assert_cnstr ast

  let assert_pathcomponent { pred ; _ } = assert_predicate pred

  let check_sat p pc =
    SMT.push ();
    List.iter assert_pathcomponent pc;
    assert_predicate p;
    let res, m = SMT.check_and_get_model () in
    SMT.pop ();
    match res with
    | L_FALSE -> print_endline "FALSE"; print_endline m; false
    | L_UNDEF -> print_endline "UNDEF"; print_endline m; true
    | L_TRUE -> print_endline "TRUE"; print_endline m; true

end

module PathCondition =
struct
  include SymbolicState.PathCondition

  open SymbolicState
  open JS.Syntax

  let mem_pred p pc =
    let eq_p { pred } = pred = p in
    List.exists eq_p pc

  let reduce_const = function
    | CUndefined
    | CNull -> Some false
    | CBool b -> Some b
    | CInt n -> Some (n <> 0)
    | CNum n -> Some (n != nan && n <> 0.0 && n <> -0.0)
    | CString s -> Some (String.length s <> 0)
    | CRegexp _ -> Some true

  let reduce_val v pc = match v with
    | SConst c -> reduce_const c
    | SHeapLabel _ -> Some true
    | _ -> None

  let not_opt = function
    | None -> None
    | Some b -> Some (not b)

  let reduce p pc = match p with
  | PredVal v -> reduce_val v pc
  | PredNotVal v -> reduce_val v pc |> not_opt

  let add ?(assumption=false) p pc =
    match reduce p pc with
    | Some true -> Some pc
    | Some false -> None
    | None ->
	if mem_pred p pc then (* redundant *)
	  Some pc
	else if mem_pred (opp p) pc then (* we already have the opposite! *)
	  None
	else if (not !Options.opt_smt) || (VC.check_sat p pc) then (* use the SMT solver to check the satisfiability *)
	  Some ({ pred = p; is_assumption = assumption }::pc)
	else
	  None

  let add_assumption = add ~assumption:true

end
