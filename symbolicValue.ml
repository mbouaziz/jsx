
open MyPervasives

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

type sid_attr = SymbAny | SymbBool | SymbInt | SymbNum | SymbStr
type sconst = JS.Syntax.const
type sheaplabel = HeapLabel.t
type sid = SId.t

type ('t, 's) _svalue = (* 't is a state, 's is a state set *)
  | SConst of sconst
  | SClosure of (('t, 's) _svalue list -> 't -> 's)
  | SHeapLabel of sheaplabel
  | SSymb of ('t, 's) _ssymb
and ('t, 's) _ssymb =
  | SId of sid * sid_attr
  | SOp1 of string * ('t, 's) _svalue
  | SOp2 of string * ('t, 's) _svalue * ('t, 's) _svalue
  | SOp3 of string * ('t, 's) _svalue * ('t, 's) _svalue * ('t, 's) _svalue
  | SApp of ('t, 's) _svalue * ('t, 's) _svalue list

type 'a sobj = { attrs : 'a IdMap.t ; props : ('a LambdaJS.Syntax.AttrMap.t) IdMap.t }


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
  let sop1 o v = SSymb (SOp1(o, v))
  let sop2 o v1 v2 = SSymb (SOp2(o, v1, v2))
  let sop3 o v1 v2 v3 = SSymb (SOp3(o, v1, v2, v3))
  let sapp v vl = SSymb (SApp(v, vl))
  let sid id k = SSymb (SId (id, k))
end
