
open LambdaJS.Prelude
open MyPervasives
open JS.Syntax
open LambdaJS.Syntax
open SymbolicValue
open SymbolicState


let apply ~pos func args s =
  match func with
  | SClosure c ->
      s
      |> SState.CallStack.push (SState.CallStack.mk_call ~pos args s)
      |> (c args |> make_closure)
      |> SState.map_unit SState.CallStack.pop
  | _ -> SState.err ~pos s (sprintf "Error [xeval] Applied non-function, was actually %s" (ToString.svalue s func))


let apply_obj ~pos o this args s =
  match o with
  | SHeapLabel label ->
      let { attrs ; props } = SState.Heap.find label s in
      begin match IdMap.find_opt "code" attrs with
      | Some code_attr -> apply ~pos code_attr [this; args] s
      | None -> SState.err ~pos s "Fail [xeval] Applying inapplicable object!"
      end
  | _ -> SState.err ~pos s "Fail [xeval] Applying non-object!"


let rec get_field ~pos obj1 obj2 field args s =
  match obj1 with
  | SConst CNull -> SState.res_undef s
  | SHeapLabel label ->
      let { attrs ; props } = SState.Heap.find label s in
      begin match IdMap.find_opt field props with
      | Some prop_attrs ->
	  begin match AttrMap.find_opt Value prop_attrs with
	  | Some value -> SState.res_v value s
	  | None ->
	      begin match AttrMap.find_opt Getter prop_attrs with
	      | Some getter ->
		  let apply_getter rv s = apply_obj ~pos getter obj2 rv s in
		  s
	          |> apply ~pos args [getter]
		  |> SState.map (SState.do_no_exn apply_getter)
	      | None -> SState.res_undef s
	      end
	  end
      | None ->
	  begin match IdMap.find_opt "proto" attrs with
	  | Some proto -> get_field ~pos proto obj2 field args s
	  | None -> SState.res_undef s
	  end
      end
  | _ -> SState.err ~pos s (sprintf "Error [xeval] get_field received (or reached) a non-object. The expression was (get-field %s %s %s)" (ToString.svalue s obj1) (ToString.svalue s obj2) field)


let add_field ~pos obj field newval s =
  match obj with
  | SHeapLabel label ->
      let { attrs ; props } = SState.Heap.find label s in
      if IdMap.mem_binding "extensible" Mk.strue attrs then
	let a = [Value, newval; Config, Mk.strue; Writable, Mk.strue; Enum, Mk.strue ] in
	let o = { attrs ; props = IdMap.add field (AttrMap.from_list a) props } in
	s |> SState.Heap.add label o |>	SState.res_v newval
      else
	SState.res_undef s
  | _ -> SState.err ~pos s "Error [xeval] add_field given non-object"


let writable prop = AttrMap.mem_binding Writable Mk.strue prop


let rec update_field ~pos obj1 obj2 field newval args s =
  match obj1 with
  | SConst CNull -> add_field ~pos obj2 field newval s
  | SHeapLabel label ->
      let { attrs ; props } = SState.Heap.find label s in
      begin match IdMap.find_opt field props with
      | Some prop ->
	  if writable prop then
	    if obj1 = obj2 then
	      let o = { attrs ; props = IdMap.add field (AttrMap.add Value newval prop) props } in
	      s |> SState.Heap.add label o |> SState.res_v newval
	    else
	      add_field ~pos obj2 field newval s
	  else
	    begin match AttrMap.find_opt Setter prop with
	    | Some setter ->
		let apply_setter rv s = apply_obj ~pos setter obj2 rv s in
		s
	        |> apply ~pos args [setter]
		|> SState.map (SState.do_no_exn apply_setter)
	    | None -> SState.res_undef s (* What should be return here ?? *) (* SState.err ~pos s "Fail [xeval] Field not writable!" *)
	    end
      | None ->
	  begin match IdMap.find_opt "proto" attrs with
	  | Some proto -> update_field ~pos proto obj2 field newval args s
	  | None -> add_field ~pos obj2 field newval s
	  end
      end
  | _ -> SState.err ~pos s (sprintf "[xeval] set_field received (or found) a non-object. The call was (set-field %s %s %s %s)" (ToString.svalue s obj1) (ToString.svalue s obj2) field (ToString.svalue s newval))


let get_attr ~pos attr obj field s =
  match obj, field with
  | SHeapLabel label, SConst (CString f) ->
      let { attrs ; props } = SState.Heap.find label s in
      begin match IdMap.find_opt f props with
      | Some prop ->
	  begin match AttrMap.find_opt attr prop with
	  | Some a -> SState.res_v a s
	  | None -> SState.res_undef s
	  end
      | None -> SState.res_undef s
      end
  | _ -> SState.err ~pos s (sprintf "Error [xeval] get-attr didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj) (ToString.svalue s field))


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
      let { attrs ; _ } = SState.Heap.find label s in
      begin match IdMap.find_opt "code" attrs with
      | Some (SClosure _) -> true
      | _ -> false
      end
  | SConst CUndefined -> true
  | _ -> false


let set_attr ~pos attr obj field newval s =
  match obj, field with
  | SHeapLabel label, SConst (CString f) ->
      let { attrs ; props } = SState.Heap.find label s in
      begin match IdMap.find_opt f props with
      | Some prop ->
	  let config = attr_or_false ~pos Config prop in
	  let writable = attr_or_false ~pos Writable prop in
	  let new_prop = match attr, newval, config, writable with
	  | Enum, SConst (CBool _), true, _
	  | Enum, SSymb _, true, _ -> AttrMap.add Enum newval prop
	  | Config, SConst (CBool _), true, _
	  | Config, SSymb _, true, _ -> AttrMap.add Config newval prop
	  | Writable, SConst (CBool _), true, _
	  | Writable, SSymb _, true, _ -> AttrMap.add Writable newval (to_data prop)
	  | Writable, SConst (CBool false), _, true
	  | Writable, SSymb _, _, true when is_data prop -> AttrMap.add Writable newval prop
	  | Writable, SConst (CBool false), _, true
	  | Writable, SSymb _, _, true -> prop
	  | Value, v, _, true -> AttrMap.add Value v (to_data prop)
	  | Setter, v, true, _ when fun_obj s v -> AttrMap.add Setter newval (to_acc prop)
	  | Setter, _, true, _ -> prop
	  | Getter, v, true, _ when fun_obj s v -> AttrMap.add Getter newval (to_acc prop)
	  | Getter, _, true, _ -> prop
	  | _ -> prop (* failwith (sprintf "%s\nWTF [xeval] set-attr don't know what to do with other values" (pretty_position pos)) *)
	  in
	  let o = { attrs ; props = IdMap.add f new_prop props } in
	  s |> SState.Heap.add label o |> SState.res_v newval
      | None ->
	  begin match IdMap.find_opt "extensible" attrs with
	  | Some (SConst (CBool true)) ->
	      let new_prop = AttrMap.singleton attr newval in
	      let o = { attrs ; props = IdMap.add f new_prop props } in
	      s |> SState.Heap.add label o |> SState.res_v newval
	  | Some _ -> SState.err ~pos s "Error [xeval] Extensible not true on object to extend with an attr"
	  | None -> SState.err ~pos s "Error [xeval] No extensible property on object to extend with an attr"
	  end
      end
  | _ -> SState.err ~pos s (sprintf "Error [xeval] set-attr didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj) (ToString.svalue s field))


let arity_mismatch_err ~pos xl args s =
  SState.err ~pos s (sprintf "Error [xeval] Arity mismatch, supplied %d arguments and expected %d. Arg names were: %s. Values were: %s." (List.length args) (List.length xl) (String.concat " " xl) (String.concat " " (List.map (ToString.svalue ~brackets:true s) args)))


let rec xeval : 'a. fine_exp -> 'a SState.t -> SState.set = fun { p = pos ; e = exp } s ->
  let xeval_nocheck s = match exp with
  | EConst c -> SState.res_v (SConst c) s
  | EId x ->
      begin match SState.Env.find x s with
      | Some v -> SState.res_v v s
      | None -> SState.err ~pos s (sprintf "Error: [xeval] Unbound identifier: %s in identifier lookup%s" x (if !Options.opt_err_unbound_id_env then sprintf " in env:\n%s" (SState.Env.to_string s) else ""))
      end
  | ESet(x, e) ->
      let unit_set v s = match SState.Env.set x v s with
      | SValue s -> SState.singleton s
      | SExn s -> SState.err ~pos s (sprintf "Error: [xeval] Unbound identifier: %s in set!" x)
      in
      xeval1 unit_set e s
  | EObject(attrs, props) ->
      let xeval_obj_attr (name, e) sl =
	let unit_xeval_obj_attr idmap s =
	  s
          |> xeval e
	  |> SState.map_res_unit (fun x s -> SState.res (IdMap.add_opt name (value_opt x) idmap) s)
	in
	SState.map_res unit_xeval_obj_attr sl
      in
      let xeval_prop_attr (name, e) sl =
	let unit_xeval_prop_attr attrmap s =
	  s
          |> xeval e
	  |> SState.map_res_unit (fun x s -> SState.res (AttrMap.add_opt name (value_opt x) attrmap) s)
	in
	SState.map_res unit_xeval_prop_attr sl
      in
      let xeval_prop (name, attrs) sl =
	let unit_xeval_prop obj s =
	  s
          |> SState.res AttrMap.empty
	  |> SState.singleton
          |> List.fold_leftr xeval_prop_attr attrs
	  |> SState.map_res_unit (fun x s -> SState.res { obj with props = IdMap.add name x obj.props } s)
	in
	SState.map_res unit_xeval_prop sl
      in
      s
      |> SState.res IdMap.empty
      |> SState.singleton
      |> List.fold_leftr xeval_obj_attr attrs
      |> SState.map_res_unit (fun attrs s -> SState.res { attrs ; props = IdMap.empty } s)
      |> List.fold_leftr xeval_prop props
      |> SState.map (SState.check_exn_res SState.res_heap_add_fresh)
  | EUpdateFieldSurface(obj, f, v, args) ->
      let unit_update obj_value f_value v_value args_value s =
	match obj_value, f_value with
	| SHeapLabel _, SConst (CString f) ->
	    update_field ~pos obj_value obj_value f v_value args_value s
	| _ -> SState.err ~pos s (sprintf "Error [xeval] Update field didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj_value) (ToString.svalue s f_value))
      in
      xeval4 unit_update obj f v args s
  | EGetFieldSurface(obj, f, args) ->
      let unit_get obj_value f_value args_value s =
	let make_err s = sprintf "Error [xeval] Get field didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj_value) (ToString.svalue s f_value) in
	match obj_value, f_value with
	| SHeapLabel _, SConst (CString f) ->
	    get_field ~pos obj_value obj_value f args_value s
	| SSymb _, SConst (CString _) ->
	    (* TODO: primitive? is not the opposite of obj? that should be used here *)
	    (* resl_rv_if s *)
            (*   (Mk.sop1 "primitive?" obj_value) *)
	    (*   (SExn (Mk.serr ~pos s (make_err s))) *)
            (*   (SValue (Mk.sop2 "get-field" obj_value f_value)) *)
	    SState.res_v (Mk.sop2 "get-field" obj_value f_value) s
	| _ -> SState.err ~pos s (make_err s)
      in
      xeval3 unit_get obj f args s
  | EDeleteField(obj, f) ->
      let unit_delete obj_value f_value s =
	match obj_value, f_value with
	| SHeapLabel label, SConst (CString f) ->
	    let { attrs ; props } = SState.Heap.find label s in
	    if IdMap.mem f props && IdMap.mem_binding "configurable" Mk.strue attrs then
	      let obj = { attrs ; props = IdMap.remove f props } in
	      let s = SState.Heap.add label obj s in
	      SState.res_true s
	    else
	      SState.res_false s
	| _ -> SState.err ~pos s (sprintf "Error [xeval] EDeleteField didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj_value) (ToString.svalue s f_value))
      in
      xeval2 unit_delete obj f s
  | EAttr(attr, obj, field) -> xeval2 (get_attr ~pos attr) obj field s
  | ESetAttr(attr, obj, field, newval) -> xeval3 (set_attr ~pos attr) obj field newval s
  (* | EOp1(`Prim1 "envlab", { e = EId x ; _ }) -> resl_str s (EnvLabel.to_string (IdMmap.find x s.env)) *)
  | EOp1(`Prim1 op, e) -> xeval1 (XDelta.op1 ~pos op) e s
  | EOp2(`Prim2 op, e1, e2) -> xeval2 (XDelta.op2 ~pos op) e1 e2 s
  | EOp3(`Prim3 op, e1, e2, e3) -> xeval3 (XDelta.op3 ~pos op) e1 e2 e3 s
  | EIf(c, t, e) -> xeval1 (SState.PathCondition.branch (xeval t) (xeval e)) c s
  | EApp(func, args) ->
      let xeval_arg arg sl =
	let unit_xeval_arg r s =
	  let unit_add v s = match v with
	  | SValue v -> SState.res (v::r) s
	  | SExn _ -> SState.res r s
	  in
	  s |> xeval arg |> SState.map_res_unit unit_add
	in
	SState.map_res unit_xeval_arg sl
      in
      let unit_apply func_value args_values_rev s =
	let args_values = List.rev args_values_rev in
	match func_value, args_values with
	| SHeapLabel _, [this; args] -> apply_obj ~pos func_value this args s
	| SClosure _, _ -> apply ~pos func_value args_values s
	| SHeapLabel _, _ -> SState.err ~pos s "Error [xeval] Need to provide this and args for a call to a function object"
	| SSymb _, _ -> SState.err ~pos s (sprintf "NYI [xeval] Application of a symbolic value %s" (ToString.svalue s func_value)) (* SState.res_v (Mk.sapp func_value args_values) s *)
	| _, _ -> SState.err ~pos s (sprintf "Error [xeval] Inapplicable value: %s, applied to %s." (ToString.svalue s func_value) (ToString.svalue_list s args_values))
      in
      let unit_xeval_args_and_apply v s =
	s
        |> SState.res []
	|> SState.singleton
	|> List.fold_leftr xeval_arg args
        |> SState.map (SState.check_exn_res (unit_apply v))
      in
      xeval1 unit_xeval_args_and_apply func s
  | ESeq(e1, e2) -> s |> xeval e1 |> SState.map (xeval e2)
  | ELet(x, e, body) ->
      let unit_let v s = xeval body (SState.Env.bind x v s) in
      s
      |> xeval1 unit_let e
      |> SState.map_unit (SState.Env.unbind x)
  | ELabel(l, e) ->
      let unit_check_label res s = match res with
      | SExn (_, SBreak (l', v)) when l = l' -> s |> SState.clean_exn |> SState.res (SValue v)
      | _ -> s
      in
      s |> xeval e |> SState.map_res_unit unit_check_label
  | EBreak(l, e) ->
      let unit_break v s = SState.break ~pos l v s in
      xeval1 unit_break e s
  | ETryCatch(body, catch) ->
      let unit_catch res s = match res with
      | SExn (_, SThrow msg) ->
	  let unit_apply_catch res s = match res with
	  | SValue v -> apply ~pos v [msg] s
	  | SExn _ -> assert false
	  in
	  s |> SState.clean_exn |> xeval catch |> SState.map_res unit_apply_catch
      | _ -> SState.singleton s
      in
      s |> xeval body |> SState.map_res unit_catch
  | ETryFinally(body, fin) ->
      let unit_finally res s = match res with
      | SValue _ -> xeval fin s
      | SExn (_, (SError _)) -> SState.singleton s
      | SExn exn ->
	  s
          |> SState.clean_exn
          |> xeval fin
          |> SState.map_unit (SState.exn exn)
      in
      s |> xeval body |> SState.map_res unit_finally
  | EThrow e ->
      let unit_throw v s = SState.throw ~pos v s in
      xeval1 unit_throw e s
  | ELambda(xl, e) ->
      let capture_env = SState.Env.get s in
      let lambda args s =
	if List.length args != List.length xl then
	  arity_mismatch_err ~pos xl args s
	else
	  s
          |> SState.Env.push capture_env (* Otherwise we don't have capture *)
          |> List.fold_leftr2 SState.Env.bind xl args
	  |> xeval e
	      (* no need to unbind args because of next line *)
	      (* but we cannot unbind envlab because of capture... (todo GC ?) *)
	  |> SState.map_unit SState.Env.pop
      in
      SState.res_v (SClosure lambda) s
  | EFix(x, { p = pos ; e = ELambda(xl, e) }) ->
      let capture_env = SState.Env.get s in
      let envlab = SState.Env.fresh_label () in
      let rec lambda args s =
	if List.length args != List.length xl then
	  arity_mismatch_err ~pos xl args s
	else
	  s
          |> SState.Env.push capture_env
          |> SState.Env.repl x envlab (SClosure lambda)
          |> List.fold_leftr2 SState.Env.bind xl args
	  |> xeval e
	  |> SState.map_unit SState.Env.pop
      in
      SState.res_v (SClosure lambda) s
  | EFix(x, e) -> SState.err ~pos s "Error [xeval] Arbritrary EFix NYI"
  in
  SState.check_exn xeval_nocheck s

and xeval1 : 'a. _ -> fine_exp -> 'a SState.t -> SState.set =
  fun f e1 s -> SState.do1 xeval f e1 s
and xeval2 : 'a. _ -> fine_exp -> fine_exp -> 'a SState.t -> SState.set =
  fun f e1 e2 s -> SState.do2 xeval f e1 e2 s
and xeval3 : 'a. _ -> fine_exp -> fine_exp -> fine_exp -> 'a SState.t -> SState.set =
  fun f e1 e2 e3 s -> SState.do3 xeval f e1 e2 e3 s
and xeval4 : 'a. _ -> fine_exp -> fine_exp -> fine_exp -> fine_exp -> 'a SState.t -> SState.set =
  fun f e1 e2 e3 e4 s -> SState.do4 xeval f e1 e2 e3 e4 s

let _ =
  XDelta._xeval := xeval
