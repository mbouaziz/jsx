
open LambdaJS.Prelude
open MyPervasives
open JS.Syntax
open LambdaJS.Syntax
open SymbolicValue
open SymbolicState

let apply func args s =
  match func with
  | SClosure c -> (c args |> make_closure) s
  | _ -> failwith (sprintf "[xeval] Applied non-function, was actually %s" (pretty_svalue func))


let apply_obj o this args s =
  match o with
  | SHeapLabel label ->
      let { attrs ; props } = SHeap.find label s.heap in
      begin match IdMap.find_opt "code" attrs with
      | Some code_attr -> apply code_attr [this; args] s
      | None -> failwith "Fail [xeval] Applying inapplicable object!"
      end
  | _ -> failwith "Fail [xeval] Applying non-object!"


let add_field obj field newval s =
  match obj with
  | SHeapLabel label ->
      let { attrs ; props } = SHeap.find label s.heap in
      if IdMap.mem_binding "extensible" strue attrs then
	let a = [Value, newval; Config, strue; Writable, strue; Enum, strue ] in
	let o = { attrs ; props = IdMap.add field (AttrMap.from_list a) props } in
	[{ s with heap = SHeap.add label o s.heap ; res = newval }]
      else
	[{ s with res = sundefined }]
  | _ -> failwith "[xeval] add_field given non-object"


let writable prop = AttrMap.mem_binding Writable strue prop


let rec update_field obj1 obj2 field newval args s =
  match obj1 with
  | SConst CNull -> add_field obj2 field newval s
  | SHeapLabel label ->
      let { attrs ; props } = SHeap.find label s.heap in
      begin match IdMap.find_opt field props with
      | Some prop ->
	  if writable prop then
	    if obj1 = obj2 then
	      let o = { attrs ; props = IdMap.add field (AttrMap.add Value newval prop) props } in
	      [{ s with heap = SHeap.add label o s.heap ; res = newval }]
	    else
	      add_field obj2 field newval s
	  else
	    begin match AttrMap.find_opt Setter prop with
	    | Some setter ->
		let apply_setter s = apply_obj setter obj2 s.res s in
		s
	        |> apply args [setter]
		|> List.map apply_setter
		|> List.flatten
	    | None -> failwith "Fail [xeval] Field not writable!"
	    end
      | None ->
	  begin match IdMap.find_opt "proto" attrs with
	  | Some proto -> update_field proto obj2 field newval args s
	  | None -> add_field obj2 field newval s
	  end
      end
  | _ -> failwith (sprintf "[xeval] set_field received (or found) a non-object. The call was (set-field %s %s %s %s)" (pretty_svalue obj1) (pretty_svalue obj2) field (pretty_svalue newval))


let rec xeval : 'a. fine_exp -> 'a sstate -> vsstate list = fun exp s ->
  match exp with
  | EConst(_, c) -> [{ s with res = SConst c }]
  | EId(p, x) ->
      let sval = try IdMmap.find x s.env with
	Not_found -> failwith (sprintf "%s\nError: [xeval] Unbound identifier: %s in identifier lookup" (pretty_position p) x)
      in
      [{ s with res = sval }]
  | ESet(p, x, e) ->
      let _ = try IdMmap.find x s.env with
	Not_found -> failwith (sprintf "%s\nError: [xeval] Unbound identifier: %s in set!" (pretty_position p) x)
      in
      let unit_set s = { s with env = IdMmap.replace x s.res s.env} in
      s
      |> xeval e
      |> List.map unit_set
  | EObject(p, attrs, props) ->
      let xeval_obj_attr (name, e) sl =
	let unit_xeval_obj_attr s =
	  s
          |> xeval e
	  |> List.map (fun s' -> { s' with res = IdMap.add name s'.res s.res })
	in
	sl |> List.map unit_xeval_obj_attr |> List.flatten
      in
      let xeval_prop_attr (name, e) sl =
	let unit_xeval_prop_attr s =
	  s
          |> xeval e
          |> List.map (fun s' -> { s' with res = AttrMap.add name s'.res s.res })
	in
	sl |> List.map unit_xeval_prop_attr |> List.flatten
      in
      let xeval_prop (name, attrs) sl =
	let unit_xeval_prop s =
	  [{s with res = AttrMap.empty}]
          |> List.fold_right xeval_prop_attr attrs
	  |> List.map (fun s' -> {s' with res = { s.res with props = IdMap.add name s'.res s.res.props }})
	in
	sl |> List.map unit_xeval_prop |> List.flatten
      in
      let make_object s =
	let label = HeapLabel.fresh () in
	{ s with heap = SHeap.add label s.res s.heap ; res = SHeapLabel label }
      in
      [{ s with res = IdMap.empty }]
      |> List.fold_right xeval_obj_attr attrs
      |> List.map (fun s -> { s with res = { attrs = s.res ; props = IdMap.empty }})
      |> List.fold_right xeval_prop props
      |> List.map make_object
  | EUpdateFieldSurface(p, obj, f, v, args) ->
      let unit_update s =
	let ((obj_value, f_value), v_value), args_value = s.res in
	match obj_value, f_value with
	| SHeapLabel _, SConst (CString f) ->
	    update_field obj_value obj_value f v_value args_value s
	| _ -> failwith (sprintf "%s\nError [xeval] Update field didn't get an object and a string" (pretty_position p))
      in
      s
      |> xeval obj
      |> xeval_push_res f
      |> xeval_push_res v
      |> xeval_push_res args
      |> List.map unit_update
      |> List.flatten
  | _ -> failwith "[xeval] NYI"

and unit_xeval_push_res : 'a. fine_exp -> 'a sstate -> ('a * svalue) sstate list = fun x s ->
  s
  |> xeval x
  |> List.map (fun s' -> { s' with res = s.res, s'.res })
and xeval_push_res : 'a. fine_exp -> 'a sstate list -> ('a * svalue) sstate list = fun x sl ->
  sl
  |> List.map (unit_xeval_push_res x)
  |> List.flatten
