
open MyPervasives

module HeapLabel :
sig
  type t
  type state
  val compare : t -> t -> int
  val compare_state : state -> state -> int
  val empty : state
  val fresh : state -> state * t
  val to_string : t -> string
  val to_int : t -> int
  val of_int : int -> t
end =
struct
  type t = int
  type state = int
  let compare = Pervasives.compare
  let compare_state = Pervasives.compare
  let empty = 0
  let fresh s = (s+1), s
  let to_string l = sprintf "l%03d" l
  let to_int l = l
  let of_int l = l
end

module LabMap =
struct
  module type LabOrderedType =
  sig
    type t
    type state
    val compare : t -> t -> int
    val compare_state : state -> state -> int
    val empty : state
    val fresh : state -> state * t
  end
  module type S =
  sig
    type key
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val fresh : 'a t -> 'a t * key
    val add : key -> 'a -> 'a t -> 'a t
    val add_fresh : 'a -> 'a t -> 'a t * key
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end
  module Make (Ord: LabOrderedType) : S with type key = Ord.t =
  struct
    module M = Map.Make(Ord)
    type key = Ord.t
    type +'a t = { m : 'a M.t ; s : Ord.state }
    let empty = { m = M.empty ; s = Ord.empty }
    let is_empty t = M.is_empty t.m
    let fresh t = let s, k = Ord.fresh t.s in { t with s }, k
    let add k v t = { t with m = M.add k v t.m }
    let add_fresh v t =
      let s, k = Ord.fresh t.s in
      { m = M.add k v t.m ; s }, k
    let find k t = M.find k t.m
    let remove k t = { t with m = M.remove k t.m }
    let mem k t = M.mem k t.m
    let iter f t = M.iter f t.m
    let map f t = { t with m = M.map f t.m }
    let mapi f t = { t with m = M.mapi f t.m }
    let fold f t a = M.fold f t.m a
    let compare f t1 t2 =
      let c = Ord.compare_state t1.s t2.s in
      if c <> 0 then c
      else M.compare f t1.m t2.m
    let equal f t1 t2 =
      (Ord.compare_state t1.s t2.s = 0) && (M.equal f t1.m t2.m)
  end
end

module SId :
sig
  type t
  val from_string : ?fresh:bool -> string -> t
  val to_string : t -> string
end =
struct
  type t = string
  let fresh_cnts = Hashtbl.create 10
  let from_string ?(fresh=false) s =
    if fresh then begin
      let fresh_cnt = try Hashtbl.find fresh_cnts s with
	Not_found ->
	  let r = ref (-1) in
	  Hashtbl.add fresh_cnts s r;
	  r
      in
      incr fresh_cnt;
      sprintf "%s$%d" s !fresh_cnt
    end else
      s
  let to_string t = sprintf "@%s" t
end

type ssymb_type_number = TNAny | TInt | TNum
type ssymb_type_prim = TPAny | TBool | TN of ssymb_type_number | TStr
type ssymb_type_val = TVAny | TP of ssymb_type_prim | TRef
type ssymb_type = TA | TV of ssymb_type_val (* TA means TV or error *)

let tBool = TV (TP TBool)
let tInt = TV (TP (TN TInt))
let tNum = TV (TP (TN TNum))
let tNAny = TV (TP (TN TNAny))
let tStr = TV (TP TStr)
let tPAny = TV (TP TPAny)
let tRef = TV TRef
let tVAny = TV TVAny
let tA = TA

module Typ =
struct

  type ex_typ = TUndef | TNull | T of ssymb_type | THeap | TFields

  let prim_types = [ tBool; tInt; tNum; tStr; tRef ]
  let abs_types = [ tNAny; tPAny; tVAny; tA ] (* must respect the partial order *)
  let types = prim_types @ abs_types (* idem *)
  let ex_types = TUndef::TNull::THeap::TFields::(List.map (fun t -> T t) types)

  type f_type = ex_typ array

  module TypMap = Map.Make(struct
			     type t = f_type
			     let compare = Pervasives.compare
			   end)
end

type sconst = JS.Syntax.const
type sheaplabel = HeapLabel.t
type sid = SId.t

type 'a prop = {
  value : 'a option;
  getter : sheaplabel option;
  setter : sheaplabel option;
  writable : bool;
  config : bool;
  enum : bool;
}

type 'v loc_field = 'v
(* shouldn't be a SConst not CString, a SClosure, a SHeapLabel or a SSymb not tStr, tPAny, tVAny or tA *)

type 'v pure_action =
  | UpdateField of 'v loc_field * 'v
  | DeleteField of 'v loc_field
(* todo: SetAttr but not Getter/Setter *)

(* 'v is a svalue *)
type 'v props = {
  pure_actions : 'v pure_action list ;
  symb_fields : sid option ;
  concrete_fields : 'v prop IdMap.t ;
}
(* this record should be understood as the set:
   List.fold_left <apply_action> (concrete_fields UNION symb_fields) pure_actions
*)


(* 't is a state, 's is a state set *)
type ('t, 's) _closure = ('t, 's) _svalue list -> 't -> 's
and ('t, 's) _svalue =
  | SConst of sconst
  | SClosure of ('t, 's) _closure
  | SHeapLabel of sheaplabel
  | SSymb of (ssymb_type * ('t, 's) _ssymb)
and ('t, 's) _ssymb =
  | SId of sid
  | SOp1 of string * ('t, 's) _svalue
  | SOpF1 of string * ('t, 's) _svalue props * ('t, 's) _svalue
  | SOp2 of string * ('t, 's) _svalue * ('t, 's) _svalue
  | SOp3 of string * ('t, 's) _svalue * ('t, 's) _svalue * ('t, 's) _svalue
  | SApp of ('t, 's) _svalue * ('t, 's) _svalue list

type 'c internal_props = {
  proto : sheaplabel option;
  _class : string;
  extensible : bool;
  code : 'c option;
}


let props_is_empty = function
  | { pure_actions = []; symb_fields = None; concrete_fields } when IdMap.is_empty concrete_fields -> true
  | _ -> false


module Mk =
struct
  open JS.Syntax

  let sundefined = SConst CUndefined
  let strue = SConst (CBool true)
  let sfalse = SConst (CBool false)
  let bool b = SConst (CBool b)
  let int i = SConst (CInt i)
  let num f = SConst (CNum f)
  let str x = SConst (CString x)
  let sop1 ~typ o v = SSymb (typ, SOp1(o, v))
  let sopF1 ~typ o p v = SSymb (typ, (SOpF1(o, p, v)))
  let sop2 ~typ o v1 v2 = SSymb (typ, SOp2(o, v1, v2))
  let sop3 ~typ o v1 v2 v3 = SSymb (typ, SOp3(o, v1, v2, v3))
  let sapp ~typ v vl = SSymb (typ, SApp(v, vl))
  let sid ~typ id = SSymb (typ, SId id)

  let internal_props =
    { proto = None; _class = "Object";
      extensible = false; code = None }

  let concrete_props m =
    { pure_actions = []; symb_fields = None; concrete_fields = m }
  let empty_props = concrete_props IdMap.empty
  let empty_prop =
    { value = None; getter = None; setter = None;
      writable = false; config = false; enum = false }
  let empty_prop_true =
    { value = None; getter = None; setter = None;
      writable = true; config = true; enum = true }
  let data_prop ?(b=false) v =
    { value = Some v; getter = None; setter = None;
      writable = b; config = b; enum = b }
end

module Abs =
struct
  open JS.Syntax

  (* str_eq v1 v2
     returns an abstraction of v1 == v2 assuming that they should be strings
     Some true for true
     Some false for false
     None for maybe

     In str_eq_const, v1 is a concrete string
  *)
  let str_eq, str_eq_const =
    (* const_const_l s1 s2
       returns None if s1 if not a prefix of s2 and s2 is not a prefix of s1
       returns Some (s1', s2') if s1 is a strict prefix of s2 (s1' = "") or if s2 is a strict prefix of s1 (s2' = "")
    *)
    let const_const_l s1 s2 =
      let l1 = String.length s1 in
      let l2 = String.length s2 in
      let rec aux i =
	if i = l1 then Some ("", String.after s2 i)
	else if i = l2 then Some (String.after s1 i, "")
	else if s1.[i] <> s2.[i] then None
	else aux (i+1)
      in aux 0
    in
    let const_const_r s1 s2 =
      let l1 = String.length s1 in
      let l2 = String.length s2 in
      let rec aux i =
	if i = l1 then Some ("", String.left s2 (l2-i))
	else if i = l2 then Some (String.left s1 (l1-i), "")
	else if s1.[l1-1-i] <> s2.[l2-1-i] then None
	else aux (i+1)
      in aux 0
    in
    let const_const s1 s2 = Some (s1 = s2)
    in
    let rec const_symb s1 s2 = match s2 with
    | SOp2("string+", SConst (CString l2), r2) ->
	begin match const_const_l s1 l2 with
	| Some (r1, "") -> const_val r1 r2
	| _ -> Some false
	end
    | SOp2("string+", l2, SConst (CString r2)) ->
	begin match const_const_r s1 r2 with
	| Some (l1, "") -> const_val l1 l2
	| _ -> Some false
	end
    | SOp1("object-to-string", _) ->
	if String.left s1 8 = "[object " && String.right s1 1 = "]" then
	  None
	else
	  Some false
    | SOp1("prim->str", SSymb(t, _)) ->
	let may_eq = match t with
	| TV (TP TBool) -> s1 = "true" || s1 = "false"
	| TV (TP (TN TInt)) -> String.Numeric.is_signed_numeric s1
	| TV (TP (TN _)) -> String.Numeric.is_float s1
	| _ -> true
	in
	if may_eq then None else Some false
    | SOp1(("surface-typeof"|"typeof"), _) ->
	if List.mem s1 ["undefined";"null";"boolean";"number";"string";"object";"function"] then None else Some false
    | _ -> None
    and symb_symb s1 s2 = match s1, s2 with
    | _ when s1 = s2 -> Some true
    | SOp2("string+", l1, r1), SOp2("string+", l2, r2) ->
	begin match val_val l1 l2 with
	| Some true -> val_val r1 r2
	| eql ->
	    begin match val_val r1 r2 with
	    | Some true -> eql
	    | _ ->
		begin match l1, r1, l2, r2 with
		| SConst (CString l1), r1, SConst (CString l2), r2 ->
		    begin match const_const_l l1 l2 with
		    | Some ("", "") -> val_val r1 r2
		    | Some (l1, "") -> symb_val (SOp2("string+", SConst (CString l1), r1)) r2
		    | Some ("", l2) -> symb_val (SOp2("string+", SConst (CString l2), r2)) r1
		    | _ -> Some false
		    end
		| l1, SConst (CString r1), l2, SConst (CString r2) ->
		    begin match const_const_r r1 r2 with
		    | Some ("", "") -> val_val l1 l2
		    | Some (r1, "") -> symb_val (SOp2("string+", l1, SConst (CString r1))) l2
		    | Some ("", r2) -> symb_val (SOp2("string+", l2, SConst (CString r2))) l1
		    | _ -> Some false
		    end
		| _ -> None
		end
	    end
	end
    | SOp1("prim->str", SSymb(t, _)), s2
    | s2, SOp1("prim->str", SSymb(t, _)) ->
	begin match t with
	| TV (TP TBool) ->
	    begin match const_symb "true" s2, const_symb "false" s2 with
	    | Some false, Some false -> Some false
	    | _ -> None
	    end
	| _ -> None
	end
    | _ -> None
    and const_val s1 v2 = match v2 with
    | SConst (CString s2) -> const_const s1 s2
    | SSymb (_, s2) -> const_symb s1 s2
    | _ -> None
    and symb_val s1 v2 = match v2 with
    | SConst (CString s2) -> const_symb s2 s1
    | SSymb (_, s2) -> symb_symb s1 s2
    | _ -> None
    and val_val v1 v2 = match v1 with
    | _ when v1 = v2 -> Some true
    | SConst (CString s1) -> const_val s1 v2
    | SSymb (_, s1) -> symb_val s1 v2
    | _ -> None
    in val_val, const_val

  let rec simplify_props field props = match props with
  | { pure_actions = []; concrete_fields = m; _ } ->
      let filter_eq f _ = str_eq (SConst (CString f)) field <> Some false in
      let concrete_fields = IdMap.filter filter_eq m in
      { props with concrete_fields }
  | { pure_actions = ((UpdateField(f, _)) as a)::pa; _ }
  | { pure_actions = ((DeleteField f) as a)::pa; _ } ->
      if str_eq f field = Some false then
	simplify_props field { props with pure_actions = pa }
      else
	let props = simplify_props field { props with pure_actions = pa } in
	{ props with pure_actions = a::props.pure_actions }


  type 'a has_property_t =
    | ConcreteHasProperty of bool
    | SymbHasProperty of 'a

  (* has_own_property field props
     returns
     ConcreteHasProperty true if props has own property field
     ConcreteHasProperty false if props doesn't have own property field
     SymbHasProperty props' if it may have own property field with props' = props with only fields that can be equal to field
  *)
  let rec has_own_property field props = match props, field with
  | { pure_actions = []; symb_fields = None; concrete_fields = m }, SConst (CString f) ->
      ConcreteHasProperty (IdMap.mem f m)
  | { pure_actions = []; symb_fields = Some _; concrete_fields = m }, SConst (CString f) when IdMap.mem f m ->
      ConcreteHasProperty true
  | { pure_actions = []; _ }, _ ->
      SymbHasProperty (simplify_props field props)
  | { pure_actions = ((UpdateField(f, _)) as a)::pa; _ }, _ ->
      begin match str_eq f field with
      | Some true -> ConcreteHasProperty true
      | Some false -> has_own_property field { props with pure_actions = pa }
      | None ->
	  match has_own_property field { props with pure_actions = pa } with
	  | ConcreteHasProperty true -> ConcreteHasProperty true
	  | ConcreteHasProperty false -> SymbHasProperty { props with pure_actions = [a]; concrete_fields = IdMap.empty }
	  | SymbHasProperty props -> SymbHasProperty { props with pure_actions = a::props.pure_actions }
      end
  | { pure_actions = (DeleteField f)::pa; _ }, _ ->
      begin match str_eq f field with
      | Some true -> ConcreteHasProperty false
      | Some false -> has_own_property field { props with pure_actions = pa }
      | None -> SymbHasProperty (simplify_props field props)
      end

  (* has_property acts like has_own_property but
     it gets two functions find_p, find_ip corresponding
     to SState.Heap.find_p, find_ip for the current heap
     In case of SymbHasProperty, it returns a list of props
     (corresponding to the prototype chain)
  *)
  let has_property ~find_p ~find_ip field label =
    let rec aux_label label = aux_props (find_p label)
    and aux_props props = match props, field with
    | { pure_actions = []; symb_fields = _; concrete_fields = m }, SConst (CString f) when IdMap.mem f m ->
	ConcreteHasProperty true
    | { pure_actions = []; symb_fields; _ }, _ ->
	let { proto; _ } = find_ip label in
	begin match proto, symb_fields with
	| None, None -> ConcreteHasProperty false
	| None, Some _ -> SymbHasProperty [simplify_props field props]
	| Some label_proto, None -> aux_label label_proto
	| Some label_proto, Some _ ->
	    match aux_label label_proto with
	    | ConcreteHasProperty true -> ConcreteHasProperty true
	    | ConcreteHasProperty false -> SymbHasProperty [simplify_props field props]
	    | SymbHasProperty l_props -> SymbHasProperty ((simplify_props field props)::l_props)
	end
    | { pure_actions = ((UpdateField(f, _)) as a)::pa; _}, _ ->
	begin match str_eq f field with
	| Some true -> ConcreteHasProperty true
	| Some false -> aux_props { props with pure_actions = pa }
	| None ->
	    match aux_props { props with pure_actions = pa } with
	    | ConcreteHasProperty true -> ConcreteHasProperty true
	    | ConcreteHasProperty false -> SymbHasProperty [{ props with pure_actions = [a]; concrete_fields = IdMap.empty }]
	    | SymbHasProperty (props::l_props) -> SymbHasProperty ({ props with pure_actions = a::props.pure_actions }::l_props)
	    | SymbHasProperty [] -> assert false
	end
    | { pure_actions = ((DeleteField f) as a)::pa; _ }, _ ->
	begin match str_eq f field with
	| Some true -> ConcreteHasProperty false
	| Some false -> aux_props { props with pure_actions = pa }
	| None ->
	    match aux_props { props with pure_actions = pa } with
	    | ConcreteHasProperty true -> SymbHasProperty [{ pure_actions = [a; UpdateField(field, Mk.sundefined)]; symb_fields = None; concrete_fields = IdMap.empty }]
	    | ConcreteHasProperty false -> SymbHasProperty [{ pure_actions = [a]; symb_fields = None; concrete_fields = IdMap.empty }]
	    | SymbHasProperty (props::l_props) -> SymbHasProperty ({ props with pure_actions = a::props.pure_actions }::l_props)
	    | SymbHasProperty [] -> assert false
	end
    in
    aux_label label

end
