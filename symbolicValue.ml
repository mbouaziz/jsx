
open LambdaJS.Prelude


module SId : sig

  type t

end =
struct

  type t

end



type sconst = JS.Syntax.const

type sid = SId.t

type svalue =
  | SConst of sconst
  | SObject of sobj
  | SClosure of (svalue list -> svalue)
  | SId of sid
  | SOp1 of string * svalue
  | SOp2 of string * svalue * svalue
  | SOp3 of string * svalue * svalue * svalue
  | SApp of svalue * svalue list 

and sobj = { attrs : svalue IdMap.t ; props : (svalue LambdaJS.Syntax.AttrMap.t) IdMap.t }

let undefined = SConst JS.Syntax.CUndefined
