
open LambdaJS.Prelude
open MyPervasives
(* open SymbolicValue *)



module SId :
sig
  type t
  val to_string : t -> string
end =
struct
  type t
  let to_string _ = "symbolic-id"
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

module Effects :
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

  let print x eff = x::eff
end


type sconst = JS.Syntax.const
type sid = SId.t
type sheaplabel = HeapLabel.t

type 'a sobj = { attrs : 'a IdMap.t ; props : ('a LambdaJS.Syntax.AttrMap.t) IdMap.t }

module SHeap = Map.Make(HeapLabel)

type 'a sheap = 'a sobj SHeap.t

type err = string

type 'a sexn = | SBreak of LambdaJS.Values.label * 'a
	       | SThrow of 'a
	       | SError of err

type 'a predicate =
  (* | PredConst of bool *)
  | PredVal of 'a
  | PredNotVal of 'a

type 'a pathcondition = 'a predicate list (* big And *)

type 'a env = 'a IdMmap.t

type ('a, 'b) state = { pc : 'a pathcondition ; env : 'a env ; heap : 'a sheap ; res : 'b ; exn : 'a sexn option ; effects : 'a Effects.t }

type 'a sstate = (svalue, 'a) state
and svalue =
  | SConst of sconst
  | SClosure of (svalue list -> unit sstate -> srvalue sstate list)
  | SHeapLabel of sheaplabel
  | SId of sid
  | SOp1 of string * svalue
  | SOp2 of string * svalue * svalue
  | SOp3 of string * svalue * svalue * svalue
  (* | SApp of svalue * svalue list *)
and srvalue =
  | SValue of svalue
  | SExn of svalue sexn

type vsstate = srvalue sstate
type spathcondition = svalue pathcondition
type senv = svalue env


let true_pathcondition : spathcondition = []
let empty_env : senv = IdMmap.empty
let make_empty_sstate x = { pc = true_pathcondition ; env = empty_env ; heap = SHeap.empty ; res = x ; exn = None ; effects = Effects.empty }
let empty_sstate = make_empty_sstate ()



let sundefined = SConst JS.Syntax.CUndefined
let strue = SConst (JS.Syntax.CBool true)
let sfalse = SConst (JS.Syntax.CBool false)

let make_closure f s = f { s with res = () }


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
    | SId id -> SId.to_string id
    | SOp1 (o, v) -> enclose (sprintf "%s %s" o (svalue ~brackets:true s v))
    | SOp2 (o, v1, v2) -> enclose (sprintf "%s %s %s" (svalue ~brackets:true s v1) o (svalue ~brackets:true s v2))
    | SOp3 (o, v1, v2, v3) -> sprintf "%s(%s, %s, %s)" o (svalue s v1) (svalue s v2) (svalue s v3)

  and sobj s { attrs ; props } = "object"

  let svalue_list s vl = String.concat ", " (List.map (svalue s) vl)

  let label l = l

  let err s e = e

  let exn s = function
    | SBreak(l, v) -> sprintf "Break(%s, %s)" (label l) (svalue s v)
    | SThrow v -> sprintf "Throw(%s)" (svalue s v)
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
    | pl -> String.concat "/\\" (List.map (predicate ~brackets:true s) pl)

  let env s env = ""
  let heap heap = ""
  let res_rsvalue s rv = ""
  let res_exn s = function
    | Some e -> exn s e
    | None -> ""
  let effects s eff = Effects.to_string (svalue s) eff

  let state s =
    ["pc", pathcondition s s.pc; "env", env s s.env; "heap", heap s.heap; "res", res_rsvalue s s.res; "exn", res_exn s s.exn; "effects", effects s s.effects]
    |> List.filter_map (fun (name, msg) -> if msg = "" then None else
			  Some (sprintf "%s:\t%s" name (String.interline "\t" msg)))
    |> String.concat "\n"

  let state_list sl = String.concat "\n\n" (List.map state sl)

end
