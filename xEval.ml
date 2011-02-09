
(* open LambdaJS.Prelude *)
open MyPervasives
open JS.Syntax
open LambdaJS.Syntax
open SymbolicValue
open SymbolicState


let apply_closure ~pos closure args s =
  s
  |> SState.CallStack.push (SState.CallStack.mk_call ~pos args s)
  |> (closure args |> make_closure)
  |> SState.map_unit SState.CallStack.pop
  
let apply ~pos func args s =
  match func with
  | SClosure c -> apply_closure ~pos c args s
  | _ -> SState.err ~pos s (sprintf "Error [xeval] Applied non-function, was actually %s" (ToString.svalue s func))


let apply_obj ~pos label this args s =
  let { code; _ } = SState.Heap.find_ip label s in
  match code with
  | Some closure -> apply_closure ~pos closure [this; args] s
  | None -> SState.err ~pos s "Fail [xeval] Applying inapplicable object!"


let rec concrete_get_field ~pos label obj_this field args s =
  let { fields; more_but_fields } as props = SState.Heap.find_p label s in
  match IdMap.find_opt field fields with
  | Some prop ->
      begin match prop.value with
      | Some value -> SState.res_v value s
      | None ->
	  match prop.getter with
	  | Some getter ->
	      let apply_getter rv s = apply_obj ~pos getter obj_this rv s in
	      s
	      |> apply ~pos args [SHeapLabel getter]
	      |> SState.map (SState.do_no_exn apply_getter)
	  | None -> SState.res_undef s
      end
  | None ->
      let proto_get_field () =
	let { proto; _ } = SState.Heap.find_ip label s in
	match proto with
	| Some lab -> concrete_get_field ~pos lab obj_this field args s
	| None -> SState.res_undef s
	in
      match XDelta.concrete_has_prop label field s with
      | Some false -> SState.res_undef s
      | Some true -> proto_get_field ()
      | None ->
	  match more_but_fields with
	  | None -> proto_get_field ()
	  | Some but_fields ->
	      let has s =
		let sid = SId.from_string ~fresh:true field in
		let prop = Mk.data_prop ~b:true (Mk.sid ~typ:tVAny sid) in
		let props = { props with fields = IdMap.add field prop fields } in
		let s = SState.Heap.update_p label props s in
		SState.res_id ~typ:tVAny sid s
	      in
	      let has_not s =
		let { proto; _ } = SState.Heap.find_ip label s in
		match proto with
		| None ->
		    let props = { props with more_but_fields = Some (IdSet.add field but_fields) } in
		    let s = SState.Heap.update_p label props s in
		    SState.res_undef s
		| Some lab -> concrete_get_field ~pos lab obj_this field args s
	      in
	      SState.PathCondition.branch has has_not (Mk.sop2 ~typ:tBool "has-own-property?" (SHeapLabel label) (SConst (CString field))) s


let concrete_add_field ~pos label field newval s =
  let { extensible; _ } = SState.Heap.find_ip label s in
  let { fields; more_but_fields } as props = SState.Heap.find_p label s in
  if extensible then
    let more_but_fields = match more_but_fields with
    | None -> None
    | Some but_fields -> Some (IdSet.remove field but_fields)
    in
    let props = { more_but_fields; fields = IdMap.add field (Mk.data_prop ~b:true newval) fields } in
    s |> SState.Heap.update_p label props |> SState.res_v newval
  else
    match more_but_fields with
    | None -> SState.res_undef s
    | Some but_fields when IdSet.mem field but_fields -> SState.res_undef s
    | Some but_fields ->
	let has s =
	  let prop = Mk.data_prop ~b:true newval in
	  let props = { props with fields = IdMap.add field prop fields } in
	  let s = SState.Heap.update_p label props s in
	  SState.res_v newval s
	in
	let has_not s =
	  let props = { props with more_but_fields = Some (IdSet.add field but_fields) } in
	  let s = SState.Heap.update_p label props s in
	  SState.res_undef s
	in
	SState.PathCondition.branch has has_not (Mk.sop2 ~typ:tBool "has-own-property?" (SHeapLabel label) (SConst (CString field))) s


let rec concrete_update_field ~pos label label_this field newval args s =
  let { fields; _  } as props = SState.Heap.find_p label s in
  match IdMap.find_opt field fields with
  | Some prop ->
      if prop.writable then
	if label = label_this then
	  let props = { props with fields = IdMap.add field { prop with value = Some newval } fields } in
	  s |> SState.Heap.update_p label props |> SState.res_v newval
	else
	  concrete_add_field ~pos label_this field newval s
      else
	begin match prop.setter with
	| Some setter ->
	    let apply_setter rv s = apply_obj ~pos setter (SHeapLabel label_this) rv s in
	    s
	    |> apply ~pos args [SHeapLabel setter]
	    |> SState.map (SState.do_no_exn apply_setter)
	| None -> SState.res_undef s (* What should be return here ?? *) (* SState.err ~pos s "Fail [xeval] Field not writable!" *)
	end
  | None ->
      let { proto; _ } = SState.Heap.find_ip label s in
      match proto with
      | Some label_proto -> concrete_update_field ~pos label_proto label_this field newval args s
      | None -> concrete_add_field ~pos label_this field newval s


let get_attr ~pos attr obj field s =
  match obj, field with
  | SHeapLabel label, SConst (CString f) ->
      let { fields; more_but_fields } as props = SState.Heap.find_p label s in
      begin match IdMap.find_opt f fields with
      | Some prop ->
	  begin match attr with
	  | Value -> (match prop.value with Some v -> SState.res_v v s | None -> SState.res_undef s)
	  | Getter -> (match prop.getter with Some l -> SState.res_heaplabel l s | None -> SState.res_undef s)
	  | Setter -> (match prop.setter with Some l -> SState.res_heaplabel l s | None -> SState.res_undef s)
	  | Writable -> SState.res_bool prop.writable s
	  | Config -> SState.res_bool prop.config s
	  | Enum -> SState.res_bool prop.enum s
	  end
      | None ->
	  match more_but_fields with
	  | None -> SState.res_undef s
	  | Some but_fields when IdSet.mem f but_fields || attr = Getter || attr = Setter -> SState.res_undef s
	  | Some but_fields ->
	      let has s =
		let sid = SId.from_string ~fresh:true f in
		let prop = Mk.data_prop ~b:true (Mk.sid ~typ:tVAny sid) in
		let props = { props with fields = IdMap.add f prop fields } in
		let s = SState.Heap.update_p label props s in
		match attr with
		| Value -> SState.res_id ~typ:tVAny sid s
		| Getter | Setter -> assert false
		| Writable | Config | Enum -> SState.res_true s
	      in
	      let has_not s =
		let props = { props with more_but_fields = Some (IdSet.add f but_fields) } in
		let s = SState.Heap.update_p label props s in
		SState.res_undef s
	      in
	      SState.PathCondition.branch has has_not (Mk.sop2 ~typ:tBool "has-own-property?" obj field) s
      end
  | _ -> SState.err ~pos s (sprintf "Error [xeval] get-attr didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj) (ToString.svalue s field))


let to_acc prop = { prop with value = None; writable = false }


let to_data prop = match prop.value with
| Some v -> { prop with setter = None; getter = None }
| None -> { prop with value = Some (SConst CUndefined); setter = None; getter = None }


let is_data prop = prop.value <> None


let fun_obj s label =
  let { code; _ } = SState.Heap.find_ip label s in
  code <> None


let prop_add_attr prop attr newval ~config ~writable s =
  match attr, newval with
  | Enum, SConst (CBool b) when config -> { prop with enum = b }
  | Enum, SSymb ((TV (TP (TBool | TPAny) | TVAny) | TA), _) when config -> failwith "NYI Symbolic value for set_attr<Enum>"
  | Config, SConst (CBool b) when config -> { prop with config = b }
  | Config, SSymb ((TV (TP (TBool | TPAny) | TVAny) | TA), _) when config -> failwith "NYI Symbolic value for set_attr<Config>"
  | Writable, SConst (CBool b) when config -> { prop with writable = b }
  | Writable, SSymb ((TV (TP (TBool | TPAny) | TVAny) | TA), _) when config -> failwith "NYI Symbolic value for set_attr<Writable>"
  | Writable, SConst (CBool false) when writable && is_data prop -> { prop with writable = false }
  | Writable, SSymb ((TV (TP (TBool | TPAny) | TVAny) | TA), _) when writable -> failwith "Symbolic value for set_attr<Writable>"
  | Value, v when writable -> { (to_data prop) with value = Some v }
  | Setter, SHeapLabel l when config && fun_obj s l -> { (to_acc prop) with setter = Some l }
  | Setter, SConst CUndefined when config -> { (to_acc prop) with setter = None }
  | Setter, SSymb ((TV (TRef | TVAny) | TA), _) when config -> failwith "NYI Symbolic value for set_attr<Setter>"
  | Getter, SHeapLabel l when config && fun_obj s l -> { (to_acc prop) with getter = Some l }
  | Getter, SConst CUndefined when config -> { (to_acc prop) with getter = None }
  | Getter, SSymb ((TV (TRef | TVAny) | TA), _) when config -> failwith "NYI Symbolic value for set_attr<Getter>"
  | _ -> prop


let prop_add_attr_opt prop attr newval_opt ~config ~writable s =
  match newval_opt with
  | Some newval -> prop_add_attr prop attr newval ~config ~writable s
  | None -> prop


let set_attr ~pos attr obj field newval s =
  match obj, field with
  | SHeapLabel label, SConst (CString f) ->
      let { fields; more_but_fields } as props = SState.Heap.find_p label s in
      let set_attr_existing_prop prop s =
	let new_prop = prop_add_attr prop attr newval ~config:prop.config ~writable:prop.writable s in
	let props = { props with fields = IdMap.add f new_prop fields } in
	s |> SState.Heap.update_p label props |> SState.res_v newval
      in
      let set_attr_non_existing_prop more_but_fields s =
	let { extensible; _ } = SState.Heap.find_ip label s in
	if extensible then
	  let new_prop = prop_add_attr Mk.empty_prop attr newval ~config:true ~writable:true s in
	  let props = { more_but_fields; fields = IdMap.add f new_prop fields } in
	  s |> SState.Heap.update_p label props |> SState.res_v newval
	else
	  SState.err ~pos s "Error [xeval] Extensible not true on object to extend with an attr"
      in
      begin match IdMap.find_opt f fields with
      | Some prop -> set_attr_existing_prop prop s
      | None ->
	  match more_but_fields with
	  | None -> set_attr_non_existing_prop None s
	  | Some but_fields when IdSet.mem f but_fields -> set_attr_non_existing_prop (Some (IdSet.remove f but_fields)) s
	  | Some but_fields ->
	      let has s =
		let prop =
		  if attr = Value then
		    Mk.empty_prop_true (* no need to create a symbol which will be overwritten *)
		  else
		    let sid = SId.from_string ~fresh:true f in
		    Mk.data_prop ~b:true (Mk.sid ~typ:tVAny sid)
		in
		set_attr_existing_prop prop s
	      in
	      let has_not s =
		set_attr_non_existing_prop (Some (IdSet.add f but_fields)) s
	      in
	      SState.PathCondition.branch has has_not (Mk.sop2 ~typ:tBool "has-own-property?" obj field) s
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
	let add_ip v ip = match name, v with
	| "proto", SConst (CUndefined | CNull) -> { ip with proto = None }
	| "proto", SHeapLabel label -> { ip with proto = Some label }
	| "proto", SSymb ((TV (TRef | TVAny) | TA), _) -> failwith (sprintf "%s\nNYI symbolic value for internal property \"proto\"" (pretty_position pos))
	| "proto", _ -> failwith (sprintf "%s\nInternal property \"proto\" must have type object or null" (pretty_position pos))
	| "class", SConst (CString _class) -> { ip with _class }
	| "class", SSymb ((TV (TP (TStr | TPAny) | TVAny) | TA), _) -> failwith (sprintf "%s\nNYI symbolic value for internal property \"class\"" (pretty_position pos))
	| "class", _ -> failwith (sprintf "%s\nInternal property \"class\" must have type string" (pretty_position pos))
	| "extensible", SConst (CBool extensible) -> { ip with extensible }
	| "extensible", SSymb ((TV (TP (TBool | TPAny) | TVAny) | TA), _) -> failwith (sprintf "%s\nNYI symbolic value for internal property \"extensible\"" (pretty_position pos))
	| "extensible", _ -> failwith (sprintf "%s\nInternal property \"extensible\" must have type boolean" (pretty_position pos))
	| "code", SConst (CUndefined | CNull) -> { ip with code = None }
	| "code", SClosure c -> { ip with code = Some c }
	| "code", SSymb _ -> failwith (sprintf "%s\nNYI symbolic value for internal property \"code\"" (pretty_position pos))
	| "code", _ -> failwith (sprintf "%s\nInternal property \"code\" must be a closure or undefined" (pretty_position pos))
	| _ -> failwith (sprintf "%s\nUnknown internal property %S" (pretty_position pos) name)
	in
	let unit_xeval_obj_attr ip s =
	  s
          |> xeval e
	  |> SState.map_res_unit (fun x s -> SState.res (match x with SValue v -> add_ip v ip | SExn e -> ip) s)
	in
	SState.map_res unit_xeval_obj_attr sl
      in
      let xeval_prop_attr (attr, e) sl =
	let unit_xeval_prop_attr prop s =
	  s
          |> xeval e
	  |> SState.map_res_unit (fun x s -> SState.res (prop_add_attr_opt prop attr (value_opt x) ~config:true ~writable:true s) s)
	in
	SState.map_res unit_xeval_prop_attr sl
      in
      let xeval_prop (name, attrs) sl =
	let unit_xeval_prop (props, ip) s =
	  s
          |> SState.res Mk.empty_prop
	  |> SState.singleton
          |> List.fold_leftr xeval_prop_attr attrs
	  |> SState.map_res_unit (fun prop s -> SState.res ({ props with fields = IdMap.add name prop props.fields }, ip) s)
	in
	SState.map_res unit_xeval_prop sl
      in
      s
      |> SState.res Mk.internal_props
      |> SState.singleton
      |> List.fold_leftr xeval_obj_attr attrs
      |> SState.map_res_unit (fun ip s -> SState.res (Mk.empty_props, ip) s)
      |> List.fold_leftr xeval_prop props
      |> SState.map (SState.check_exn_res SState.res_heap_add_fresh)
  | EUpdateFieldSurface(obj, f, v, args) ->
      let unit_update obj_value f_value v_value args_value s =
	match obj_value, f_value with
	| SHeapLabel label, SConst (CString f) ->
	    concrete_update_field ~pos label label f v_value args_value s
	| _ -> SState.err ~pos s (sprintf "Error [xeval] Update field didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj_value) (ToString.svalue s f_value))
      in
      xeval4 unit_update obj f v args s
  | EGetFieldSurface(obj, f, args) ->
      let unit_get obj_value f_value args_value s =
	let make_err s = sprintf "Error [xeval] Get field didn't get an object and a string. Instead it got %s and %s." (ToString.svalue s obj_value) (ToString.svalue s f_value) in
	match obj_value, f_value with
	| SHeapLabel label, SConst (CString f) ->
	    concrete_get_field ~pos label obj_value f args_value s
	| (SHeapLabel _ | SSymb (TV TRef, _)), (SConst (CString _) | SSymb (TV (TP TStr), _)) ->
	    SState.res_op2 ~typ:tVAny "get-field" obj_value f_value s
	| (SHeapLabel _ | SSymb ((TV (TRef | TVAny) | TA), _)), (SConst (CString _) | SSymb ((TV (TP (TStr | TPAny) | TVAny) | TA), _)) ->
	    SState.res_op2 ~typ:tA "get-field" obj_value f_value s
	| _ -> SState.err ~pos s (make_err s)
      in
      xeval3 unit_get obj f args s
  | EDeleteField(obj, f) ->
      let unit_delete obj_value f_value s =
	match obj_value, f_value with
	| SHeapLabel label, SConst (CString f) ->
	    let { fields; more_but_fields } = SState.Heap.find_p label s in
	    begin match IdMap.find_opt f fields with
	    | Some { config = true; _ } ->
		let fields = IdMap.remove f fields in
		let more_but_fields = match more_but_fields with
		| None -> None
		| Some but_fields -> Some (IdSet.add f but_fields)
		in
		let s = SState.Heap.update_p label { fields; more_but_fields } s in
		SState.res_true s
	    | Some { config = false; _ } -> SState.res_false s
	    | None ->
		match more_but_fields with
		| None -> SState.res_false s
		| Some but_fields when IdSet.mem f but_fields -> SState.res_false s
		| Some but_fields ->
		    let props = { fields; more_but_fields = Some (IdSet.add f but_fields) } in
		    let s = SState.Heap.update_p label props s in
		    SState.res_op2 ~typ:tBool "has-own-property?" obj_value f_value s
	    end
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
	| SHeapLabel lab, [this; args] -> apply_obj ~pos lab this args s
	| SClosure closure, _ -> apply_closure ~pos closure args_values s
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
      let s, envlab = SState.Env.fresh_label s in
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
