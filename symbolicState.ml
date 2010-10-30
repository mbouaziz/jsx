
open LambdaJS.Prelude
open MyPervasives
(* open SymbolicValue *)



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
end =
struct
  type 'a t = 'a list

  let empty = []

  let to_string alpha_to_string = List.rev_map alpha_to_string @> String.concat "\n"

  let print x sio = x::sio
end


type sconst = JS.Syntax.const
type sid = SId.t
type sheaplabel = HeapLabel.t

type 'a sobj = { attrs : 'a IdMap.t ; props : ('a LambdaJS.Syntax.AttrMap.t) IdMap.t }

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
    | CString x -> sprintf "\"%s\"" x
    | CBool x -> string_of_bool x
    | CUndefined -> "undefined"
    | CNull -> "null"
    | CRegexp (re, g, i) -> sprintf "/%s/%s%s" re (if g then "g" else "") (if i then "i" else "")

  let rec svalue ?(brackets=false) s =
    let enclose x = if brackets then sprintf "(%s)" x else x in
    function
      | SConst c -> const c
      | SClosure _ -> "function"
      | SHeapLabel hl -> enclose (sprintf "heap[%s]: %s" (HeapLabel.to_string hl) (sobj s (SHeap.find hl s.heap)))
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

  and sobj s { attrs ; props } = "object"

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
  let heap heap = ""
  let res_rsvalue s rv = ""
  let res_exn s = function
    | Some e -> exn s e
    | None -> ""
  let io s sio = SIO.to_string (svalue s) sio

  let state s =
    ["pc", pathcondition s s.pc; "env", env s s.env; "heap", heap s.heap; "res", res_rsvalue s s.res; "exn", res_exn s s.exn; "io", io s s.io]
    |> List.filter_map (fun (name, msg) -> if msg = "" then None else
			  Some (sprintf "%s:\t%s" name (String.interline "\t" msg)))
    |> String.concat "\n"

  let state_list = function
    | [] -> "NO STATE"
    | sl -> sl |> List.map state |> String.concat "\n\n"

end
