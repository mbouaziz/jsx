
open LambdaJS.Prelude
open MyPervasives



module SId :
sig
  type t
  val from_string : string -> t
  val to_string : t -> string
end =
struct
  type t = string
  let from_string s = s
  let to_string t = sprintf "@%s" t
end

module HeapLabel :
sig
  type t
  val compare : t -> t -> int
  val fresh : unit -> t
  val to_string : t -> string
end =
struct
  type t = int

  let compare = Pervasives.compare

  let fresh =
    let last = ref 0 in
    fun () -> incr last; !last

  let to_string l = sprintf "l%03d" l

end

module SIO :
sig
  type 'a t
  val empty : 'a t
  val to_string : ('a -> string) -> 'a t -> string
  val print : 'a -> 'a t -> 'a t
  val values : 'a t -> 'a list
end =
struct
  type 'a t = 'a list

  let empty = []

  let to_string alpha_to_string = List.rev_map alpha_to_string @> String.concat "\n"

  let print x sio = x::sio

  let values sio = sio
end


type sconst = JS.Syntax.const
type sid = SId.t
type sheaplabel = HeapLabel.t

type 'a sobj = { attrs : 'a IdMap.t ; props : ('a LambdaJS.Syntax.AttrMap.t) IdMap.t }

module LabelSet = Set.Make(HeapLabel)
module SHeap = Map.Make(HeapLabel)

type 'a sheap = 'a sobj SHeap.t

type err = string

type pos = Lexing.position * Lexing.position

type 'a sexn = | SBreak of pos * (LambdaJS.Values.label * 'a)
	       | SThrow of pos * 'a
	       | SError of err

type 'a predicate =
  (* | PredConst of bool *)
  | PredVal of 'a
  | PredNotVal of 'a

type 'a pathcondition = 'a predicate list (* big And *)

type 'a env = 'a IdMmap.t

type ('a, 'b) state = { pc : 'a pathcondition ; env : 'a env ; heap : 'a sheap ; res : 'b ; exn : 'a sexn option ; io : 'a SIO.t }

type ('a, 'b) rvalue =
  | SValue of 'a
  | SExn of 'b

type 'a sstate = (svalue, 'a) state
and svalue =
  | SConst of sconst
  | SClosure of (svalue list -> unit sstate -> srvalue sstate list)
  | SHeapLabel of sheaplabel
  | SSymb of ssymb
and ssymb =
  | SId of sid
  | SOp1 of string * svalue
  | SOp2 of string * svalue * svalue
  | SOp3 of string * svalue * svalue * svalue
  | SApp of svalue * svalue list
and srvalue = (svalue, svalue sexn) rvalue

type vsstate = srvalue sstate
type senv = svalue env



module PathCondition =
struct
  open JS.Syntax

  type t = svalue pathcondition

  let pc_true : t = []

  let opp = function
    | PredVal x -> PredNotVal x
    | PredNotVal x -> PredVal x

  let add p pc = match p with
  | PredVal (SConst (CBool true)) -> Some pc
  | PredVal (SConst (CBool false)) -> None
  | PredNotVal (SConst (CBool true)) -> None
  | PredNotVal (SConst (CBool false)) -> Some pc
  | p ->
      if List.mem p pc then
	Some pc
      else if List.mem (opp p) pc then
	None
      else
	Some (p::pc)

  let predval = function
    | PredVal v
    | PredNotVal v -> v

  let rec values = function
    | [] -> []
    | p::pc -> (predval p)::(values pc)
end


let empty_env : senv = IdMmap.empty
let make_empty_sstate x = { pc = PathCondition.pc_true; env = empty_env; heap = SHeap.empty; res = x; exn = None; io = SIO.empty }
let empty_sstate = make_empty_sstate ()


let sundefined = SConst JS.Syntax.CUndefined
let strue = SConst (JS.Syntax.CBool true)
let sfalse = SConst (JS.Syntax.CBool false)


let make_closure f s = f { s with res = () }


let value_opt = function
  | SValue v -> Some v
  | SExn _ -> None
let check_exn f s =
  match s.exn with
  | Some exn -> [{ s with res = SExn exn }]
  | None -> f s
let do_no_exn f s =
  match s.res with
  | SValue v -> f v s
  | SExn _ -> [s]

module Pretty = (* output a printer *)
struct

end

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
  let collect_labels { heap ; _ } vl labs =
    let rec aux v labs = match v with
    | SConst _ -> labs
    | SHeapLabel l -> labs |> LabelSet.add l |> aux_obj (SHeap.find l heap)
    | SClosure _ -> labs
    | SSymb symb -> match symb with
      | SId _ -> labs
      | SOp1(_, v) -> labs |> aux v
      | SOp2(_, v1, v2) -> labs |> aux v1 |> aux v2
      | SOp3(_, v1, v2, v3) -> labs |> aux v1 |> aux v2 |> aux v3
      | SApp(v, vl) -> labs |> aux v |> List.fold_right aux vl
    and aux_obj { attrs ; props } = IdMap.fold aux_map1 attrs @> IdMap.fold aux_map2 props
    and aux_map1 : 'a. 'a -> _ = fun _ -> aux
    and aux_map2 _ am = LambdaJS.Syntax.AttrMap.fold aux_map1 am
    in
    List.fold_right aux vl labs

  let rec svalue ?(deep=false) ?(brackets=false) s =
    let enclose x = if brackets then sprintf "(%s)" x else x in
    function
      | SConst c -> const c
      | SClosure _ -> "function"
      | SHeapLabel hl when deep -> enclose (sprintf "heap[%s]: %s" (HeapLabel.to_string hl) (sobj s (SHeap.find hl s.heap)))
      | SHeapLabel hl -> sprintf "heap[%s]" (HeapLabel.to_string hl)
      | SSymb symb -> match symb with
	|SId id -> SId.to_string id
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

  and sobj s { attrs ; props } =
    if IdMap.is_empty props then
      sprintf "{[%s]}" (sattrs s attrs)
    else
      sprintf "{[%s]\n%s}" (sattrs s attrs) (sprops s props)
  and sattrs s attrs =
    let unit_attr (attr, v) =
      sprintf "%s: %s" attr (svalue s v)
    in
    attrs |> IdMap.bindings |> List.map unit_attr |> String.concat ", "
  and spropattrs ?(sep="") s attrs =
    let unit_attr (attr, v) =
      sprintf "%s: %s" (LambdaJS.Syntax.string_of_attr attr) (svalue s v)
    in
    attrs |> LambdaJS.Syntax.AttrMap.bindings |> List.map unit_attr |> String.concat ",\n"
  and spropattr_value s sattrs = match LambdaJS.Syntax.AttrMap.find_opt LambdaJS.Syntax.Value sattrs with
  | None -> "attrs"
  | Some v -> sprintf "#value: %s" (svalue s v)
  and sprops s props =
    let unit_prop (prop_id, attrs) =
      sprintf "%s: {%s}" prop_id (spropattr_value s attrs)
      (* sprintf "%s: {%s}" prop_id (spropattrs ~sep:"\n" s attrs) *)
    in
    props |> IdMap.bindings |> List.map unit_prop |> String.concat ",\n"

  let svalue_list s vl = String.concat ", " (List.map (svalue s) vl)

  let label l = l

  let err s e = e

  let exn s = function
    | SBreak(pos,(l, v)) -> sprintf "%s\nBreak(%s, %s)" (pretty_position pos) (label l) (svalue s v)
    | SThrow(pos,v) -> sprintf "%s\nThrow(%s)" (pretty_position pos) (svalue s v)
    | SError e -> err s e

  let srvalue s = function
    | SExn e -> exn s e
    | SValue v -> svalue s v

  let predicate ?(brackets=false) s = function
    | PredVal v -> svalue ~brackets s v
    | PredNotVal v -> sprintf "Not(%s)" (svalue s v)

  let pathcondition s = function
    | [] -> "True"
    | [p] -> predicate s p
    | pl -> String.concat " /\\ " (List.rev_map (predicate ~brackets:true s) pl)

  let env s env = ""
  let heap ?labs s heap =
    let add_lab lab v l = (sprintf "%s\t%s" (HeapLabel.to_string lab) (sobj s v))::l in
    let unit_lab = match labs with
    | None -> add_lab
    | Some labs -> fun lab v l -> if LabelSet.mem lab labs then add_lab lab v l else l
    in
    SHeap.fold unit_lab heap [] |> String.concat "\n"
  let res_rsvalue s rv = ""
  let res_exn s = function
    | Some e -> exn s e
    | None -> ""
  let io s sio = SIO.to_string (svalue s) sio

  (* these X_values functions should correspond to what is printed with res_X *)
  let env_values _ = []
  let rvalue_values _ = []
  let exn_values = function
    | Some (SBreak(_,(_,v)))
    | Some (SThrow(_,v)) -> [v]
    | Some (SError _)
    | None -> []

  let state s =
    let labs = LabelSet.empty
    |> collect_labels s (PathCondition.values s.pc)
    |> collect_labels s (env_values s.env)
    |> collect_labels s (rvalue_values s.res)
    |> collect_labels s (exn_values s.exn)
    |> collect_labels s (SIO.values s.io)
    in
    ["pc", pathcondition s s.pc; "env", env s s.env; "heap", heap ~labs s s.heap; "res", res_rsvalue s s.res; "exn", res_exn s s.exn; "io", io s s.io]
    |> List.filter_map (fun (name, msg) -> if msg = "" then None else
			  Some (sprintf "%s:\t%s" name (String.interline "\t" msg)))
    |> String.concat "\n"

  let state_list = function
    | [] -> "NO STATE???"
    | sl -> sl |> List.map state |> String.concat "\n\n"

end
