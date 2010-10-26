
open LambdaJS.Prelude
open MyPervasives
(* open SymbolicValue *)



module SId :
sig
  type t
end =
struct
  type t
end

module HeapLabel :
sig
  type t
  val compare : t -> t -> int
  val fresh : unit -> t
end =
struct
  type t = int

  let compare = Pervasives.compare

  let fresh =
    let last = ref 0 in
    fun () -> incr last; !last

end


type sconst = JS.Syntax.const
type sid = SId.t
type sheaplabel = HeapLabel.t

type 'a sobj = { attrs : 'a IdMap.t ; props : ('a LambdaJS.Syntax.AttrMap.t) IdMap.t }

module SHeap = Map.Make(HeapLabel)

type 'a sheap = 'a sobj SHeap.t


type 'a predicate =
  (* | PredConst of bool *)
  | PredVal of 'a
  | PredNotVal of 'a

type 'a pathcondition = 'a predicate list (* big And *)

type 'a env = 'a IdMmap.t

type ('a, 'b) state = { pc : 'a pathcondition ; env : 'a env ; heap : 'a sheap ; res : 'b }

type 'a sstate = (svalue, 'a) state
and svalue =
  | SConst of sconst
  | SClosure of (svalue list -> unit sstate -> svalue sstate list)
  | SHeapLabel of sheaplabel
  | SId of sid
  | SOp1 of string * svalue
  | SOp2 of string * svalue * svalue
  | SOp3 of string * svalue * svalue * svalue
  (* | SApp of svalue * svalue list *)

type vsstate = svalue sstate
type spathcondition = svalue pathcondition
type senv = svalue env


let true_pathcondition : spathcondition = []
let empty_env : senv = IdMmap.empty
let make_empty_sstate x = { pc = true_pathcondition ; env = empty_env ; heap = SHeap.empty ; res = x }
let empty_sstate = make_empty_sstate ()



let sundefined = SConst JS.Syntax.CUndefined
let strue = SConst (JS.Syntax.CBool true)

let make_closure f s = f { s with res = () }


let rec pretty_svalue = function
  | _ -> assert false
