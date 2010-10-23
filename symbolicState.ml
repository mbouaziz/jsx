
open LambdaJS.Prelude
open MyPervasives

type 'a predicate =
  (* | PredConst of bool *)
  | PredVal of 'a
  | PredNotVal of 'a

type 'a pathcondition = 'a predicate list (* big And *)

type 'a env = 'a IdMmap.t

type ('a, 'b) state = { pc : 'a pathcondition ; env : 'a env ; res : 'b }

type svalue = SymbolicValue.svalue
type spathcondition = svalue pathcondition
type senv = svalue env
type 'a sstate = (svalue, 'a) state
type vsstate = svalue sstate

let true_pathcondition : spathcondition = []
let empty_env : senv = IdMmap.empty
let empty_sstate x = { pc = true_pathcondition ; env = empty_env ; res = x }
