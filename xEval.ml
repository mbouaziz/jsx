
open LambdaJS.Prelude
open MyPervasives
open JS.Syntax
open LambdaJS.Syntax
open SymbolicState

open XDelta.ResHelpers


let apply ~pos func args s =
  match func with
  | SClosure c ->
      { s with callstack = (pos, args)::s.callstack }
      |> (c args |> make_closure)
      |> List.map (fun s -> { s with callstack = List.tl s.callstack })
  | _ -> errl ~pos s (sprintf "Error [xeval] Applied non-function, was actually %s" (ToString.svalue s func))


let apply_obj ~pos o this args s =
  match o with
  | SHeapLabel label ->
      let { attrs ; props } = SHeap.find label s.heap in
      begin match IdMap.find_opt "code" attrs with
      | Some code_attr -> apply ~pos code_attr [this; args] s
      | None -> errl ~pos s "Fail [xeval] Applying inapplicable object!"
      end
  | _ -> errl ~pos s "Fail [xeval] Applying non-object!"


let rec get_field ~pos obj1 obj2 field args s =
  match obj1 with
  | SConst CNull -> resl_undef s
  | SHeapLabel label ->
      let { attrs ; props } = SHeap.find label s.heap in
      begin match IdMap.find_opt field props with
      | Some prop_attrs ->
	  begin match AttrMap.find_opt Value prop_attrs with
	  | Some value -> resl_v s value
	  | None ->
	      begin match AttrMap.find_opt Getter prop_attrs with
	      | Some getter ->
		  let apply_getter rv s = apply_obj ~pos getter obj2 rv s in
		  s
	          |> apply ~pos args [getter]
		  |> List.map (do_no_exn apply_getter)
		  |> List.flatten
	      | None -> resl_undef s
	      end
	  end
      | None ->
	  begin match IdMap.find_opt "proto" attrs with
	  | Some proto -> get_field ~pos proto obj2 field args s
	  | None -> resl_undef s
	  end
      end
  | _ -> errl ~pos s (sprintf "Error [xeval] get_field received (or reached) a non-object. The expression was (get-field %s %s %s)" (ToString.svalue s obj1) (ToString.svalue s obj2) field)


let add_field ~pos obj field newval s =
  match obj with
  | SHeapLabel label ->
      let { attrs ; props } = SHeap.find label s.heap in
      if IdMap.mem_binding "extensible" strue attrs then
	let a = [Value, newval; Config, strue; Writable, strue; Enum, strue ] in
	let o = { attrs ; props = IdMap.add field (AttrMap.from_list a) props } in
	[{ s with heap = SHeap.add label o s.heap ; res = SValue newval }]
      else
	resl_undef s
  | _ -> errl ~pos s "Error [xeval] add_field given non-object"


let writable prop = AttrMap.mem_binding Writable strue prop


let rec update_field ~pos obj1 obj2 field newval args s =
  match obj1 with
  | SConst CNull -> add_field ~pos obj2 field newval s
  | SHeapLabel label ->
      let { attrs ; props } = SHeap.find label s.heap in
      begin match IdMap.find_opt field props with
      | Some prop ->
	  if writable prop then
	    if obj1 = obj2 then
	      let o = { attrs ; props = IdMap.add field (AttrMap.add Value newval prop) props } in
	      [{ s with heap = SHeap.add label o s.heap ; res = SValue newval }]
	    else
	      add_field ~pos obj2 field newval s
	  else
	    begin match AttrMap.find_opt Setter prop with
	    | Some setter ->
		let apply_setter rv s = apply_obj ~pos setter obj2 rv s in
		s
	        |> apply ~pos args [setter]
		|> List.map (do_no_exn apply_setter)
		|> List.flatten
	    | None -> errl ~pos s "Fail [xeval] Field not writable!" (* return s ? *)
	    end
      | None ->
	  begin match IdMap.find_opt "proto" attrs with
	  | Some proto -> update_field ~pos proto obj2 field newval args s
	  | None -> add_field ~pos obj2 field newval s
	  end
      end
  | _ -> errl ~pos s (sprintf "[xeval] set_field received (or found) a non-object. The call was (set-field %s %s %s %s)" (ToString.svalue s obj1) (ToString.svalue s obj2) field (ToString.svalue s newval))


let get_attr ~pos attr obj field s =
  match obj, field with
  | SHeapLabel label, SConst (CString f) ->
      let { attrs ; props } = SHeap.find label s.heap in
      begin match IdMap.find_opt f props with
      | Some prop ->
	  begin match AttrMap.find_opt attr prop with
	  | Some a -> resl_v s a
	  | None -> resl_undef s
	  end
      | None -> resl_undef s
      end
  | _ -> errl ~pos s (sprintf "Error [xeval] get-attr didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj) (ToString.svalue s field))


let attr_or_false ~pos attr prop =
  match AttrMap.find_opt attr prop with
  | Some (SConst (CBool b)) -> b
  | Some _ -> failwith (sprintf "%s\nBad Error [xeval] Writable or Configurable wasn't a boolean" (pretty_position pos))
  | None -> false


let to_acc = AttrMap.remove Value @> AttrMap.remove Writable


let to_data = AttrMap.remove Setter @> AttrMap.remove Getter


let is_data prop =
  AttrMap.mem Writable prop || AttrMap.mem Value prop &&
    not (AttrMap.mem Setter prop || AttrMap.mem Getter prop)


let fun_obj s = function (* TODO: using attrs named props in es5_eval.ml *)
  | SHeapLabel label ->
      let { attrs ; _ } = SHeap.find label s.heap in
      begin match IdMap.find_opt "code" attrs with
      | Some (SClosure _) -> true
      | _ -> false
      end
  | SConst CUndefined -> true
  | _ -> false


let set_attr ~pos attr obj field newval s =
  match obj, field with
  | SHeapLabel label, SConst (CString f) ->
      let { attrs ; props } = SHeap.find label s.heap in
      begin match IdMap.find_opt f props with
      | Some prop ->
	  let config = attr_or_false ~pos Config prop in
	  let writable = attr_or_false ~pos Writable prop in
	  let new_prop = match attr, newval, config, writable with
	  | Enum, SConst (CBool _), true, _ -> AttrMap.add Enum newval prop
	  | Config, SConst (CBool _), true, _ -> AttrMap.add Config newval prop
	  | Writable, SConst (CBool _), true, _ -> AttrMap.add Writable newval (to_data prop)
	  | Writable, SConst (CBool false), _, true when is_data prop -> AttrMap.add Writable newval prop
	  | Writable, SConst (CBool false), _, true -> prop
	  | Value, v, _, true -> AttrMap.add Value v (to_data prop)
	  | Setter, v, true, _ when fun_obj s v -> AttrMap.add Setter newval (to_acc prop)
	  | Setter, _, true, _ -> prop
	  | Getter, v, true, _ when fun_obj s v -> AttrMap.add Getter newval (to_acc prop)
	  | Getter, _, true, _ -> prop
	  | _ -> failwith (sprintf "%s\nWTF [xeval] set-attr don't know what to do with other values" (pretty_position pos))
	  in
	  let o = { attrs ; props = IdMap.add f new_prop props } in
	  [{ s with heap = SHeap.add label o s.heap ; res = SValue newval }]
      | None ->
	  begin match IdMap.find_opt "extensible" attrs with
	  | Some (SConst (CBool true)) ->
	      let new_prop = AttrMap.singleton attr newval in
	      let o = { attrs ; props = IdMap.add f new_prop props } in
	      [{ s with heap = SHeap.add label o s.heap ; res = SValue newval }]
	  | Some _ -> errl ~pos s "Error [xeval] Extensible not true on object to extend with an attr"
	  | None -> errl ~pos s "Error [xeval] No extensible property on object to extend with an attr"
	  end
      end
  | _ -> errl ~pos s (sprintf "Error [xeval] set-attr didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj) (ToString.svalue s field))


let lambda_set_arg arg x s = { s with env = IdMmap.push x arg s.env }

let arity_mismatch_err ~pos xl args s =
  errl ~pos s (sprintf "Error [xeval] Arity mismatch, supplied %d arguments and expected %d. Arg names were: %s. Values were: %s." (List.length args) (List.length xl) (String.concat " " xl) (String.concat " " (List.map (ToString.svalue ~brackets:true s) args)))


let rec xeval : 'a. fine_exp -> 'a sstate -> vsstate list = fun exp s ->
  let xeval_nocheck s = match exp with
  | EConst(_, c) -> resl_v s (SConst c)
  | EId(pos, x) ->
      begin match IdMmap.find_opt x s.env with
      | Some sval -> resl_v s sval
      | None -> errl ~pos s (sprintf "Error: [xeval] Unbound identifier: %s in identifier lookup%s" x (if !Options.opt_err_unbound_id_env then sprintf " in env:\n%s" (ToString.senv s s.env) else ""))
      end
  | ESet(pos, x, e) ->
      if IdMmap.mem x s.env then
	let unit_set v s = [{ s with env = IdMmap.replace x v s.env }] in
	xeval1 unit_set e s
      else
	errl ~pos s (sprintf "Error: [xeval] Unbound identifier: %s in set!" x)
  | EObject(pos, attrs, props) ->
      let xeval_obj_attr (name, e) sl =
	let unit_xeval_obj_attr s =
	  s
          |> xeval e
	  |> List.map (fun s' -> { s' with res = IdMap.add_opt name (value_opt s'.res) s.res })
	in
	sl |> List.map unit_xeval_obj_attr |> List.flatten
      in
      let xeval_prop_attr (name, e) sl =
	let unit_xeval_prop_attr s =
	  s
          |> xeval e
	  |> List.map (fun s' -> { s' with res = AttrMap.add_opt name (value_opt s'.res) s.res })
	in
	sl |> List.map unit_xeval_prop_attr |> List.flatten
      in
      let xeval_prop (name, attrs) sl =
	let unit_xeval_prop s =
	  [{s with res = AttrMap.empty}]
          |> List.fold_leftr xeval_prop_attr attrs
	  |> List.map (fun s' -> {s' with res = { s.res with props = IdMap.add name s'.res s.res.props }})
	in
	sl |> List.map unit_xeval_prop |> List.flatten
      in
      let make_object s =
	let label = HeapLabel.fresh () in
	[{ s with heap = SHeap.add label s.res s.heap ; res = SValue (SHeapLabel label) }]
      in
      [{ s with res = IdMap.empty }]
      |> List.fold_leftr xeval_obj_attr attrs
      |> List.map (fun s -> { s with res = { attrs = s.res ; props = IdMap.empty }})
      |> List.fold_leftr xeval_prop props
      |> List.map (check_exn make_object)
      |> List.flatten
  | EUpdateFieldSurface(pos, obj, f, v, args) ->
      let unit_update obj_value f_value v_value args_value s =
	match obj_value, f_value with
	| SHeapLabel _, SConst (CString f) ->
	    update_field ~pos obj_value obj_value f v_value args_value s
	| _ -> errl ~pos s (sprintf "Error [xeval] Update field didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj_value) (ToString.svalue s f_value))
      in
      xeval4 unit_update obj f v args s
  | EGetFieldSurface(pos, obj, f, args) ->
      let unit_get obj_value f_value args_value s =
	let make_err s = sprintf "Error [xeval] Get field didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj_value) (ToString.svalue s f_value) in
	match obj_value, f_value with
	| SHeapLabel _, SConst (CString f) ->
	    get_field ~pos obj_value obj_value f args_value s
	| SSymb _, SConst (CString _) ->
	    (* TODO: primitive? is not the opposite of obj? that should be used here *)
	    resl_rv_if s
              (Mk.sop1 "primitive?" obj_value)
	      (SExn (Mk.serr ~pos s (make_err s)))
              (SValue (Mk.sop2 "get_field" obj_value f_value))
	| _ -> errl ~pos s (make_err s)
      in
      xeval3 unit_get obj f args s
  | EDeleteField(pos, obj, f) ->
      let unit_delete obj_value f_value s =
	match obj_value, f_value with
	| SHeapLabel label, SConst (CString f) ->
	    let { attrs ; props } = SHeap.find label s.heap in
	    if IdMap.mem f props && IdMap.mem_binding "configurable" strue attrs then
	      let obj = { attrs ; props = IdMap.remove f props } in
	      [{ s with heap = SHeap.add label obj s.heap ; res = SValue strue }]
	    else
	      resl_bool s false
	| _ -> errl ~pos s (sprintf "Error [xeval] EDeleteField didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj_value) (ToString.svalue s f_value))
      in
      xeval2 unit_delete obj f s
  | EAttr(pos, attr, obj, field) -> xeval2 (get_attr ~pos attr) obj field s
  | ESetAttr(pos, attr, obj, field, newval) -> xeval3 (set_attr ~pos attr) obj field newval s
  | EOp1(pos, `Prim1 op, e) -> xeval1 (XDelta.op1 ~pos op) e s
  | EOp2(pos, `Prim2 op, e1, e2) -> xeval2 (XDelta.op2 ~pos op) e1 e2 s
  | EOp3(pos, `Prim3 op, e1, e2, e3) -> xeval3 (XDelta.op3 ~pos op) e1 e2 e3 s
  | EIf(pos, c, t, e) ->
      let unit_if rv s =
	let sl_t = match PathCondition.add (PredVal rv) s.pc with
	| Some pc -> xeval t { s with pc }
	| None -> []
	in
	let sl_e = match PathCondition.add (PredNotVal rv) s.pc with
	| Some pc -> xeval e { s with pc }
	| None -> []
	in
	sl_t@sl_e
      in
      xeval1 unit_if c s
  | EApp(pos, func, args) ->
      let xeval_arg sl arg =
	let unit_xeval_arg s =
	  let unit_add s' = match s'.res with
	  | SValue v -> { s' with res = v::s.res }
	  | SExn _ -> { s' with res = s.res }
	  in
	  s |> xeval arg |> List.map unit_add
	in
	sl |> List.map unit_xeval_arg |> List.flatten
      in
      let unit_apply func_value s =
	let args_values_rev = s.res in
	let args_values = List.rev args_values_rev in
	match func_value, args_values with
	| SHeapLabel _, [this; args] -> apply_obj ~pos func_value this args s
	| SClosure _, _ -> apply ~pos func_value args_values s
	| SHeapLabel _, _ -> errl ~pos s "Error [xeval] Need to provide this and args for a call to a function object"
	| SSymb _, _ -> resl_v s (Mk.sapp func_value args_values)
	| _, _ -> errl ~pos s (sprintf "Error [xeval] Inapplicable value: %s, applied to %s." (ToString.svalue s func_value) (ToString.svalue_list s args_values))
      in
      let unit_xeval_args_and_apply v s =
	List.fold_left xeval_arg [{ s with res = [] }] args
        |> List.map (check_exn (unit_apply v))
	|> List.flatten
      in
      xeval1 unit_xeval_args_and_apply func s
  | ESeq(pos, e1, e2) -> s |> xeval e1 |> List.map (xeval e2) |> List.flatten
  | ELet(pos, x, e, body) ->
      let unit_let rv s = xeval body { s with env = IdMmap.push x rv s.env } in
      s
      |> xeval1 unit_let e
      |> List.map (fun s -> { s with env = IdMmap.pop x s.env }) (* important: unbind x *)
  | ELabel(pos, l, e) ->
      let unit_check_label s = match s.res with
      | SExn (_, SBreak (l', v)) when l = l' -> { s with exn = None; res = SValue v }
      | _ -> s
      in
      s |> xeval e |> List.map unit_check_label
  | EBreak(pos, l, e) ->
      let unit_break v s =
	let exn = Mk.sbreak ~pos s l v in
	[{ s with exn = Some exn ; res = SExn exn }]
      in
      xeval1 unit_break e s
  | ETryCatch(pos, body, catch) ->
      let unit_catch s = match s.res with
      | SExn (_, SThrow msg) ->
	  let unit_apply_catch s = match s.res with
	  | SValue v -> apply ~pos v [msg] s
	  | SExn _ -> assert false
	  in
	  { s with exn = None } |> xeval catch |> List.map unit_apply_catch |> List.flatten
      | _ -> [s]
      in
      s |> xeval body |> List.map unit_catch |> List.flatten
  | ETryFinally(pos, body, fin) ->
      let unit_finally s =
	match s.res with
	| SValue _ -> xeval fin s
	| SExn (_, (SError _)) -> [s]
	| SExn _ ->
	    { s with exn = None ; res = () }
	    |> xeval fin
	    |> List.map (fun s' -> { s' with exn = s.exn ; res = s.res })
      in
      s |> xeval body |> List.map unit_finally |> List.flatten
  | EThrow(pos, e) ->
      let unit_throw v s =
	let exn = Mk.sthrow ~pos s v in
	[{ s with exn = Some exn ; res = SExn exn }]
      in
      xeval1 unit_throw e s
  | ELambda(pos, xl, e) ->
      let lambda args s_caller =
	if List.length args != List.length xl then
	  arity_mismatch_err ~pos xl args s_caller
	else
	  { s_caller with env = s.env } (* Otherwise we don't have capture *)
          |> List.fold_leftr2 lambda_set_arg args xl
	  |> xeval e
	      (* no need to unbind args because of next line *)
	  |> List.map (fun s -> { s with env = s_caller.env })
      in
      resl_v s (SClosure lambda)
  | EFix(_, x, ELambda(pos, xl, e)) ->
      let rec lambda args s_caller =
	if List.length args != List.length xl then
	  arity_mismatch_err ~pos xl args s_caller
	else
	  { s_caller with env = IdMmap.push x (SClosure lambda) s.env }
          |> List.fold_leftr2 lambda_set_arg args xl
	  |> xeval e
	  |> List.map (fun s -> { s with env = s_caller.env })
      in
      resl_v s (SClosure lambda)
  | EFix(pos, x, e) -> errl ~pos s "Error [xeval] Arbritrary EFix NYI"
  in
  check_exn xeval_nocheck s

and unit_xeval_push_res : 'a. fine_exp -> 'a sstate -> ('a * srvalue) sstate list = fun x s ->
  s |> xeval x |> List.map (fun s' -> { s' with res = s.res, s'.res })

and xeval_push_res : 'a. fine_exp -> 'a sstate list -> ('a * srvalue) sstate list = fun x sl ->
  sl |> List.map (unit_xeval_push_res x) |> List.flatten

and xeval1 : 'a. _ -> fine_exp -> 'a sstate -> vsstate list = fun f e1 s ->
  let f' s = match s.res with
  | SExn _ -> [s]
  | SValue v -> f v s
  in
  s |> xeval e1 |> List.map f' |> List.flatten

and xeval2 : 'a. _ -> fine_exp -> fine_exp -> 'a sstate -> vsstate list = fun f e1 e2 s ->
  let f' s = match s.res with
  | _, (SExn _ as rv) -> [{ s with res = rv }]
  | SValue v1, SValue v2 -> f v1 v2 s
  | _, _ -> assert false
  in
  s |> xeval e1 |> xeval_push_res e2 |> List.map f' |> List.flatten

and xeval3 : 'a. _ -> fine_exp -> fine_exp -> fine_exp -> 'a sstate -> vsstate list = fun f e1 e2 e3 s ->
  let f' s = match s.res with
  | _, (SExn _ as rv) -> [{ s with res = rv }]
  | (SValue v1, SValue v2), SValue v3 -> f v1 v2 v3 s
  | _ -> assert false
  in
  s |> xeval e1 |> xeval_push_res e2 |> xeval_push_res e3 |> List.map f' |> List.flatten

and xeval4 : 'a. _ -> fine_exp -> fine_exp -> fine_exp -> fine_exp -> 'a sstate -> vsstate list = fun f e1 e2 e3 e4 s ->
  let f' s = match s.res with
  | _, (SExn _ as rv) -> [{ s with res = rv }]
  | ((SValue v1, SValue v2), SValue v3), SValue v4 -> f v1 v2 v3 v4 s
  | _ -> assert false
  in
  s |> xeval e1 |> xeval_push_res e2 |> xeval_push_res e3 |> xeval_push_res e4 |> List.map f' |> List.flatten
