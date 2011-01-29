
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
  val from_string : string -> t
  val to_string : t -> string
end =
struct
  type t = string
  let from_string s = s
  let to_string t = sprintf "@%s" t
end

type ssymb_type = TAny | TBool | TInt | TNum | TStr | TRef
type sconst = JS.Syntax.const
type sheaplabel = HeapLabel.t
type sid = SId.t

type ('t, 's) _svalue = (* 't is a state, 's is a state set *)
  | SConst of sconst
  | SClosure of (('t, 's) _svalue list -> 't -> 's)
  | SHeapLabel of sheaplabel
  | SSymb of (ssymb_type * ('t, 's) _ssymb)
and ('t, 's) _ssymb =
  | SId of sid
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
  let sop1 ?(typ=TAny) o v = SSymb (typ, SOp1(o, v))
  let sop2 ?(typ=TAny) o v1 v2 = SSymb (typ, SOp2(o, v1, v2))
  let sop3 ?(typ=TAny) o v1 v2 v3 = SSymb (typ, SOp3(o, v1, v2, v3))
  let sapp ?(typ=TAny) v vl = SSymb (typ, SApp(v, vl))
  let sid ~typ id = SSymb (typ, SId id)
end
