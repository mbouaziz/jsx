
open LambdaJS.Prelude
open MyPervasives
open SymbolicValue

module SOutput :
sig
  type 'a t
  val empty : 'a t
  val to_string : ('a -> string) -> 'a t -> string
  val print : 'a -> 'a t -> 'a t
  val warning: string -> 'a t -> 'a t
  val values : 'a t -> 'a list
end =
struct
  type 'a line =
    | SAlpha of 'a
    | SString of string

  type 'a t = 'a line list

  let empty = []

  let line_to_string alpha_to_string = function
    | SAlpha a -> alpha_to_string a
    | SString s -> s

  let to_string alpha_to_string = List.rev_map (line_to_string alpha_to_string) @> String.concat "\n"

  let print x sout = (SAlpha x)::sout

  let warning str sout = (SString str)::sout

  let val_of_line = function
    | SAlpha a -> Some a
    | SString _ -> None

  let values sout = List.filter_map val_of_line sout
end

type err = string

type pos = Lexing.position * Lexing.position

type 'a sexnval = | SBreak of LambdaJS.Values.label * 'a
		  | SThrow of 'a
		  | SError of err

type ('a, 'c) _sexn = (pos * 'c) * 'a sexnval

type ('a, 'b) rvalue =
  | SValue of 'a
  | SExn of 'b


module SState :
sig
  type 'a t
  type 'a _set
  type 'a call
  type 'a callstack
  type 'a sexn = ('a, 'a callstack) _sexn
  type set = srvalue _set
  and svalue = (unit t, set) _svalue
  and srvalue = (svalue, svalue sexn) rvalue
  type sclosure = (unit t, set) _closure
  type s = srvalue t
  type envlabel
  type env

  val marshal_in : in_channel -> set option
  val marshal_out : out_channel -> set option -> unit

  module ToString :
  sig
    val svalue : ?deep:bool -> ?brackets:bool -> 'a t -> svalue -> string
    val svalue_list : 'a t -> svalue list -> string
    val state : s -> string
    val nosymb_state : s -> string * string option
    val model : s -> string
    val short_model : s -> string
  end

  val first : unit t

  (* val is_empty : set -> bool *)
  val get_singleton : 'a _set -> 'a t option
  val singleton : 'a t -> 'a _set
  val map_unit : (s -> s) -> set -> set
  val map : ('a t -> 'b _set) -> 'a _set -> 'b _set
  val map_res : ('a -> 'a t -> 'b _set) -> 'a _set -> 'b _set
  val map_res_unit : ('a -> 'a t -> 'b t) -> 'a _set -> 'b _set
  val get_first : set -> s
  val get_next : set -> (unit -> set) option
    (* should be called only once for a lazy set *)

  val res : 'a -> 'b t -> 'a t
  val res_v : svalue -> 'a t -> set
  val res_undef : 'a t -> set
  val res_false : 'a t -> set
  val res_true : 'a t -> set
  val res_bool : bool -> 'a t -> set
  val res_int : int -> 'a t -> set
  val res_num : float -> 'a t -> set
  val res_str : string -> 'a t -> set
  val res_heaplabel : sheaplabel -> 'a t -> set
  val res_heap_add : sheaplabel -> svalue props -> sclosure internal_props -> 'a t -> set
  val res_heap_add_fresh : svalue props * sclosure internal_props -> 'a t -> set
  val res_id : typ:SymbolicValue.ssymb_type -> sid -> 'a t -> set
  val res_op1 : typ:SymbolicValue.ssymb_type -> string -> svalue -> 'a t -> set
  val res_op2 : typ:SymbolicValue.ssymb_type -> string -> svalue -> svalue -> 'a t -> set

  val exn : svalue sexn -> 'a t -> s
  val clean_exn : 'a t -> unit t

  val break : pos:pos -> LambdaJS.Values.label -> svalue -> 'a t -> set
  val throw : pos:pos -> svalue -> 'a t -> set
  val throw_str : pos:pos -> 'a t -> string -> set
  val err : pos:pos -> 'a t -> err -> set

  val check_exn : ('a t -> set) -> 'a t -> set
  val check_exn_res : ('a -> 'a t -> set) -> 'a t -> set
  val do_no_exn : (svalue -> s -> set) -> s -> set

  val do1 : ('a -> unit t -> set) -> (svalue -> s -> set) -> 'a -> 'c t -> set
  val do2 : ('a -> unit t -> set) -> (svalue -> svalue -> s -> set) -> 'a -> 'a -> 'c t -> set
  val do3 : ('a -> unit t -> set) -> (svalue -> svalue -> svalue -> s -> set) -> 'a -> 'a -> 'a -> 'b t -> set
  val do4 : ('a -> unit t -> set) -> (svalue -> svalue -> svalue -> svalue -> s -> set) -> 'a -> 'a -> 'a -> 'a -> 'b t -> set

  module CallStack :
  sig
    val mk_call : pos:pos -> svalue list -> 'a t -> svalue call
    val push : svalue call -> 'a t -> 'a t
    val pop : 'a t -> 'a t
    val top : 'a t -> svalue call option
    val call_pos : 'a call -> pos
    val call_env : 'a call -> env
  end
  module Env :
  sig
    val fresh_label : 'a t -> 'a t * envlabel
    val repl : id -> envlabel -> svalue -> 'a t -> 'a t
    val bind : id -> svalue -> 'a t -> 'a t
    val unbind : id -> 'a t -> 'a t
    val find : id -> 'a t -> svalue option
    val set : id -> svalue -> 'a t -> ('a t, 'a t) rvalue

    val get : 'a t -> env
    val dupl : 'a t -> 'a t
    val push : env -> 'a t -> 'a t
    val pop : 'a t -> 'a t
    val to_string : 'a t -> string
  end
  module Heap :
  sig
    val update_p : sheaplabel -> svalue props -> 'a t -> 'a t
    val update_ip : sheaplabel -> sclosure internal_props -> 'a t -> 'a t
    val add : sheaplabel -> svalue props -> sclosure internal_props -> 'a t -> 'a t
    val find_p : sheaplabel -> 'a t -> svalue props
    val find_ip : sheaplabel -> 'a t -> sclosure internal_props
  end
  module Output :
  sig
    val print : svalue -> 'a t -> 'a t
  end
  module PathCondition :
  sig
    val _assert : pos:pos -> svalue -> 'a t -> set
    val assume : pos:pos -> svalue -> 'a t -> set
    val branch : ('a t -> set) -> ('a t -> set) -> svalue -> 'a t -> set
  end
end =
struct

  module LabelSet = Set.Make(HeapLabel)
  module SHeap =
  struct
    module P = Map.Make(HeapLabel)
    module IP = LabMap.Make(HeapLabel)
    type ('v, 'c) sheap = { p : 'v props P.t; ip : 'c internal_props IP.t }
    let empty = { p = P.empty; ip = IP.empty }
  end
  module EnvLabel = HeapLabel
  module EnvVals = LabMap.Make(EnvLabel)
  type ('v, 'c) sheap = ('v, 'c) SHeap.sheap = { p : 'v props SHeap.P.t; ip : 'c internal_props SHeap.IP.t }
  type 'a envvals = 'a EnvVals.t
  type envlabel = EnvLabel.t
  type env = envlabel IdMmap.t

  type 's __set = 's * 's _next_set
  and 's _next_set = (unit -> 's __set) option

  type 'a call = { call_pos : pos ; call_env : env ; call_args : 'a list }
  and 'a callstack = 'a call list
  and 'a sexn = ('a, 'a callstack) _sexn
  and ('a, 'b) state = { pc : 'a PathCondition._pathcondition ; env : env ; env_stack : env list ; envvals : 'a envvals ; heap : ('a, sclosure) sheap ; res : 'b ; exn : 'a sexn option ; out : 'a SOutput.t ; callstack : 'a callstack }
  and svalue = ((svalue, unit) state, (svalue, srvalue) state __set) _svalue
  and srvalue = (svalue, svalue sexn) rvalue
  and sclosure = ((svalue, unit) state, (svalue, srvalue) state __set) _closure

  type 'b t = (svalue, 'b) state
  type s = srvalue t
  type 'a _set = 'a t __set
  type set = s __set

  let marshal_in ich = Marshal.from_channel ich
  let marshal_out och set_opt = Marshal.to_channel och set_opt [Marshal.Closures]

  module ToString = (* output a string *)
  struct

    let const = let open JS.Syntax in function
      | CInt x -> string_of_int x
      | CNum x -> string_of_float x
      | CString x -> sprintf "%S" x
      | CBool x -> string_of_bool x
      | CUndefined -> "undefined"
      | CNull -> "null"
      | CRegexp (re, g, i) -> sprintf "/%s/%s%s" re (if g then "g" else "") (if i then "i" else "")

    (* Collect only labels that will be printed by svalue AND by svalue of SHeap.find of these labels *)
    let collect_labels ~depth { heap ; _ } vl labs =
      let rec aux ~depth v labs = match v with
      | SConst _ -> labs
      | SHeapLabel l -> aux_heaplabel ~depth l labs
      | SClosure _ -> labs
      | SSymb (_, symb) -> match symb with
	| SId _ -> labs
	| SOp1(_, v) -> labs |> aux ~depth v
	| SOp2(_, v1, v2) -> labs |> aux ~depth v1 |> aux ~depth v2
	| SOp3(_, v1, v2, v3) -> labs |> aux ~depth v1 |> aux ~depth v2 |> aux ~depth v3
	| SApp(v, vl) -> labs |> aux ~depth v |> List.fold_right (aux ~depth) vl
      and aux_heaplabel ~depth l labs =
	if LabelSet.mem l labs then (* prevents from looping *)
	  labs
	else
	  let labs = LabelSet.add l labs in
	  if depth <= 0 then
	    labs
	  else
	    let depth = depth - 1 in
	    labs |> aux_props ~depth (SHeap.P.find l heap.p) |> aux_internal_props ~depth (SHeap.IP.find l heap.ip)
      and aux_props ~depth { fields; _ } = IdMap.fold (aux_prop ~depth) fields
      and aux_internal_props ~depth { proto; _ } = aux_opt ~depth proto
      and aux_prop ~depth _ prop = aux_optv ~depth prop.value @> aux_opt ~depth prop.getter @> aux_opt ~depth prop.setter
      and aux_optv ~depth = function Some v -> aux ~depth v | None -> (fun x -> x)
      and aux_opt ~depth = function Some l -> aux_heaplabel ~depth l | None -> (fun x -> x)
      in
      List.fold_right (aux ~depth) vl labs

    let rec svalue ?(deep=false) ?(brackets=false) s =
      let enclose x = if brackets then sprintf "(%s)" x else x in
      function
	| SConst c -> const c
	| SClosure _ -> "function"
	| SHeapLabel hl when deep -> enclose (sprintf "heap[%s]: %s" (HeapLabel.to_string hl) (sobj s (SHeap.P.find hl s.heap.p) (SHeap.IP.find hl s.heap.ip)))
	| SHeapLabel hl -> sprintf "heap[%s]" (HeapLabel.to_string hl)
	| SSymb (_, symb) ->
	    match symb with
	    | SId id -> SId.to_string id
	    | SOp1 (o, v) ->
		if Char.is_alpha o.[0] then
		  sprintf "%s(%s)" o (svalue s v)
		else
		  enclose (sprintf "%s %s" o (svalue ~brackets:true s v))
	    | SOp2 (o, v1, v2) ->
		if Char.is_alpha o.[0] then
		  sprintf "%s(%s, %s)" o (svalue s v1) (svalue s v2)
		else
		  enclose (sprintf "%s %s %s" (svalue ~brackets:true s v1) o (svalue ~brackets:true s v2))
	    | SOp3 (o, v1, v2, v3) -> sprintf "%s(%s, %s, %s)" o (svalue s v1) (svalue s v2) (svalue s v3)
	    | SApp (v, vl) -> sprintf "%s(%s)" (svalue ~brackets:true s v) (String.concat ", " (List.map (svalue s) vl))

    and sobj s props { proto; _class; extensible; code } =
      let s_proto = sprintf "proto: %s, " (match proto with None -> "null" | Some l -> svalue s (SHeapLabel l)) in
      let s_class = if _class = "" then "" else sprintf "class: %S, " _class in
      let s_extensible = sprintf "extensible: %B" extensible in
      let s_code = match code with None -> "" | Some _ -> ", code: <function>" in
      let s_props = if props_is_empty props then "" else String.interline "  " ("\n" ^ sprops s props) in
      "{[" ^ s_proto ^ s_class ^ s_extensible ^ s_code ^ "]" ^ s_props ^ "}"
    and spropattr_value s prop = match prop.value with
    | None -> "attrs"
    | Some v -> sprintf "#value: %s" (svalue s v)
    and sprops s { fields; more_but_fields } =
      let add_more l = match more_but_fields with
      | None -> l
      | Some but_fields ->
	  let but = IdSet.to_list but_fields |> String.concat ", " in
	  let but =
	    if but = "" then ""
	    else sprintf " (but %s)" but in
	  l@[sprintf "& more%s" but]
      in
      let unit_prop (prop_id, prop) =
	sprintf "%s: {%s}" prop_id (spropattr_value s prop)
      in
      fields |> IdMap.bindings |> List.map unit_prop |> add_more |> String.concat ",\n"

    let svalue_list s vl = String.concat ", " (List.map (svalue s) vl)

    let senv s env =
      let unit_binding (id, envlab) =
	let v = EnvVals.find envlab s.envvals in
	sprintf "%s\t%s" id (svalue s v)
      in
      env |> IdMmap.bindings |> List.map unit_binding |> String.concat "\n"

    let scall s { call_pos ; _ } = sprintf "Called from %s" (pretty_position ~alone:false call_pos)

    let scallstack s = List.map (scall s)

    let position_and_stack s pos cs =
      (pretty_position pos)::(scallstack s cs) |> String.concat "\n"

    let label l = l

    let exnval s = function
      | SBreak (l, v) -> sprintf "Break(%s, %s)" (label l) (svalue s v)
      | SThrow v -> sprintf "Throw(%s)" (svalue s v)
      | SError msg -> msg

    let exn s ((pos, cs), ev) =
      sprintf "%s\n%s" (position_and_stack s pos cs) (exnval s ev)

    let srvalue s = function
      | SExn e -> exn s e
      | SValue v -> svalue s v

    let string_of_svalue ~brackets s v = svalue ~brackets s v

    let pathcondition = PathCondition.ToString.pathcondition ~string_of_svalue
    let assumptions = PathCondition.ToString.assumptions ~string_of_svalue
    let assertions = PathCondition.ToString.assertions ~string_of_svalue

    let env s env = ""
    let callstack s cs = ""
    let heap ?labs s heap =
      let add_lab lab v l = (sprintf "%s\t%s" (HeapLabel.to_string lab) (String.interline "\t" (sobj s (SHeap.P.find lab heap.p) v)))::l in
      let unit_lab = match labs with
      | None -> add_lab
      | Some labs -> fun lab v l -> if LabelSet.mem lab labs then add_lab lab v l else l
      in
      SHeap.IP.fold unit_lab heap.ip [] |> String.concat "\n"
    let res_rsvalue s rv = ""
    let res_exn s = function
      | Some e -> exn s e
      | None -> ""
    let out s sout = SOutput.to_string (svalue s) sout

    (* these X_values functions should correspond to what is printed with res_X *)
    let env_values _ = []
    let rvalue_values _ = []
    let callstack_values _ = []
    let exnval_values = function
      | SBreak (_, v)
      | SThrow v -> [v]
      | SError _ -> []
    let exn_values = function
      | Some ((_, cs), ev) -> (callstack_values cs)@(exnval_values ev)
      | None -> []

    let state s =
      let depth = 1 in (* prevents from printing too many objects *)
      let labs = LabelSet.empty
      |> collect_labels ~depth s (PathCondition.PC.values s.pc)
      |> collect_labels ~depth s (env_values s.env)
      |> collect_labels ~depth s (rvalue_values s.res)
      |> collect_labels ~depth s (exn_values s.exn)
      |> collect_labels ~depth s (SOutput.values s.out)
      |> collect_labels ~depth s (callstack_values s.callstack)
      in
      let pc_label = sprintf "pc[%s]" (PathCondition.ToString.sat s.pc) in
      ["assum", assumptions s s.pc; "assert", assertions s s.pc; pc_label, pathcondition s s.pc; "env", env s s.env; "heap", heap ~labs s s.heap; "res", res_rsvalue s s.res; "exn", res_exn s s.exn; "stk", callstack s s.callstack; "out", out s s.out]
      |> List.filter_map (fun (name, msg) -> if msg = "" then None else
			    Some (sprintf "%s:\t%s" name (String.interline "\t" msg)))
      |> String.concat "\n"

    let state_set _ = assert false (* Change the API *)

    let nosymb_svalue s = function
      | SConst (JS.Syntax.CString x) -> x
      | _ -> failwith "Non-string value"

    let nosymb_out s sout = SOutput.to_string (nosymb_svalue s) sout

    let nosymb_state s =
      let out = nosymb_out s s.out in
      let exn = res_exn s s.exn in
      if exn = "" then
	out, None
      else
	out, Some exn

    let short_model s = PathCondition.ToString.short_model s.pc 

    let model s = PathCondition.ToString.model s.pc

  end (* ToString *)

  module CallStack =
  struct
    let mk_call ~pos args s = { call_pos = pos; call_env = s.env; call_args = args }
    let call_pos c = c.call_pos
    let call_env c = c.call_env
    let push c s = { s with callstack = c::s.callstack }
    let pop s = { s with callstack = List.tl s.callstack }
    let top s = match s.callstack with
    | [] -> None
    | c::_ -> Some c
  end

  module Env =
  struct
    let fresh_label s =
      let envvals, envlab = EnvVals.fresh s.envvals in
      { s with envvals }, envlab

    let repl id envlab v s = { s with env = IdMmap.replace_all id envlab s.env; envvals = EnvVals.add envlab v s.envvals }
    let bind id v s =
      let envvals, envlab = EnvVals.add_fresh v s.envvals in
      { s with env = IdMmap.push id envlab s.env; envvals }
    let unbind id s = { s with env = IdMmap.pop id s.env } (* important: unbind x ; but envlab must not be unbind in envvals *)
    let find id s = match IdMmap.find_opt id s.env with
    | Some envlab -> Some (EnvVals.find envlab s.envvals)
    | None -> None
    let set id v s = match IdMmap.find_opt id s.env with
    | Some envlab -> SValue { s with envvals = EnvVals.add envlab v s.envvals }
    | None -> SExn s

    let get s = s.env
    let dupl s = { s with env_stack = s.env::s.env_stack }
    let push env s = { s with env ; env_stack = s.env::s.env_stack }
    let pop s = { s with env = List.hd s.env_stack ; env_stack = List.tl s.env_stack }
    let to_string s = ToString.senv s s.env
  end

  module Heap =
  struct
    let update_p label props s =
      { s with heap = { s.heap with p = SHeap.P.add label props s.heap.p } }
    let update_ip label internal_props s =
      { s with heap = { s.heap with ip = SHeap.IP.add label internal_props s.heap.ip } }
    let add label props internal_props s = { s with heap = { p = SHeap.P.add label props s.heap.p ; ip = SHeap.IP.add label internal_props s.heap.ip } }
    let add_fresh props internal_props s =
      let ip, label = SHeap.IP.add_fresh internal_props s.heap.ip in
      let p = SHeap.P.add label props s.heap.p in
      { s with heap = { p; ip } }, label
    let find_p label s = SHeap.P.find label s.heap.p
    let find_ip label s = SHeap.IP.find label s.heap.ip
  end

  module Output =
  struct
    let print v s = { s with out = SOutput.print v s.out }
    let warning ~pos msg s =
      let str = sprintf "%s\n%s" (ToString.position_and_stack s pos s.callstack) msg in
      { s with out = SOutput.warning str s.out }
  end

  module Next =
  struct
    let map g = function
      | None -> None
      | Some f -> Some (f @> g)

    let app_snd f (x, y) = x, f y

    let rec seq_def g2 = function
      | None -> Some g2
      | Some g1 -> Some (g1 @> app_snd (seq_def g2))

    let seq n1 = function
      | None -> n1
      | Some g2 -> seq_def g2 n1
  end

  let first = { pc = PathCondition.PC.pc_true; env = IdMmap.empty; env_stack = []; envvals = EnvVals.empty; heap = SHeap.empty; res = (); exn = None; out = SOutput.empty; callstack = [] }

  (* let is_empty set = false *)

  let get_singleton = function
    | x, None -> Some x
    | _ -> None

  let singleton s = s, None

  let rec map_unit f (s, n) = f s, Next.map (map_unit f) n
  let rec map f (s, n) = let s, n' = f s in s, Next.seq n' (Next.map (map f) n)
  let map_res f = let f' s = f s.res s in map f'
  let map_res_unit f = let f' s = f s.res s in map_unit f'

  let get_first (s, _) = s
  let get_next (_, n) = n

  let res res s = { s with res }
  let res_v v s = singleton { s with res = SValue v }
  let res_undef s = res_v Mk.sundefined s
  let res_true s = res_v Mk.strue s
  let res_false s = res_v Mk.sfalse s
  let res_bool b s = res_v (Mk.bool b) s
  let res_int i s = res_v (Mk.int i) s
  let res_num n s = res_v (Mk.num n) s
  let res_str x s = res_v (Mk.str x) s
  let res_heaplabel l s = res_v (SHeapLabel l) s
  let res_heap_add l props internal_props s = res_v (SHeapLabel l) (Heap.add l props internal_props s)
  let res_heap_add_fresh (props, internal_props) s =
    let s, l = Heap.add_fresh props internal_props s in res_v (SHeapLabel l) s
  let res_id ~typ id s = res_v (Mk.sid ~typ id) s
  let res_op1 ~typ o v s = res_v (Mk.sop1 ~typ o v) s
  let res_op2 ~typ o v1 v2 s = res_v (Mk.sop2 ~typ o v1 v2) s

  let exn e s = { s with exn = Some e ; res = SExn e }
  let clean_exn s = { s with exn = None ; res = () }

  let res_e ~pos ev s = s |> exn ((pos, s.callstack), ev) |> singleton
  let break ~pos l v s = res_e ~pos (SBreak (l, v)) s
  let throw ~pos v s = res_e ~pos (SThrow v) s
  let throw_str ~pos s msg = throw ~pos (Mk.str msg) s
  let err ~pos s msg =
    if !Options.opt_fatal then
      failwith msg
    else
      res_e ~pos (SError msg) s

  let check_exn f s =
    match s.exn with
    | Some exn -> singleton { s with res = SExn exn }
    | None -> f s
  let check_exn_res f s =
    match s.exn with
    | Some exn -> singleton { s with res = SExn exn }
    | None -> f s.res s
  let do_no_exn f s =
    match s.res with
    | SExn _ -> singleton s
    | SValue v -> f v s

  let do1 : 'c. _ -> _ -> _ -> 'c t -> _ = fun f g x1 s -> s |> res () |> f x1 |> map (do_no_exn g)
  let do2 f g x1 x2 s = do1 f (fun v -> do1 f (g v) x2) x1 s
  let do3 f g x1 x2 x3 s = do1 f (fun v -> do2 f (g v) x2 x3) x1 s
  let do4 f g x1 x2 x3 x4 s = do1 f (fun v -> do3 f (g v) x2 x3 x4) x1 s

  module PathCondition =
  struct
    open PathCondition

    let branch f_t f_e v s =
      match PC.branch v s.pc with
      | Some pc_t, Some pc_e ->
	  let s', n = f_t { s with pc = pc_t } in
	  s', Next.seq n (Some (fun () -> f_e { s with pc = pc_e }))
      | Some pc_t, None -> f_t { s with pc = pc_t }
      | None, Some pc_e -> f_e { s with pc = pc_e }
      | None, None -> err ~pos:dummy_pos s "Path unsatisfiable"

    let _assert ~pos v s =
      match PC.add_assertion v s.pc with
      | _, None -> err ~pos s "This assertion is surely false!"
      | L_FALSE, Some pc -> res_true { s with pc }
      | L_TRUE, Some pc ->
	  let s = Output.warning ~pos "This assertion could be false" s in
	  res_false { s with pc }
      | L_UNDEF, Some pc ->
	  let s = Output.warning ~pos "This assertion cannot be checked" s in
	  res_false { s with pc }

    let assume ~pos v s =
      match PC.add_assumption v s.pc with
      | None -> err ~pos s "This assumption is surely false!"
      | Some pc -> res_true { s with pc }
  end
end

let make_closure f = SState.res () @> f


let value_opt = function
  | SValue v -> Some v
  | SExn _ -> None

module ToString = SState.ToString
