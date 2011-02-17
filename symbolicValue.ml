
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

  let cmp t1 t2 = match t1, t2 with
  | t1, t2 when t1 = t2 -> Some 0
  | _, TA
  | TV _, TV TVAny
  | TV (TP _), TV (TP TPAny)
  | TV (TP (TN _)), TV (TP (TN TNAny)) -> Some (-1)
  | TA, _
  | TV TVAny, TV _
  | TV (TP TPAny), TV (TP _)
  | TV (TP (TN TNAny)), TV (TP (TN _)) -> Some 1
  | _, _ -> None

  type ex_typ = TUndef | TNull | T of ssymb_type

  let prim_types = [ tBool; tInt; tNum; tStr; tRef ]

  let abs_types = [ tNAny; tPAny; tVAny; tA ] (* must respect the partial order *)

  let types = prim_types @ abs_types (* idem *)

  let ex_types = TUndef::TNull::(List.map (fun t -> T t) types)

  type f_type = ex_typ array

  module TypMap =
  struct
    module FTyp =
    struct
      type t = f_type
      let compare = Pervasives.compare
    end
    include Map.Make(FTyp)
  end
end

type sconst = JS.Syntax.const
type sheaplabel = HeapLabel.t
type sid = SId.t

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
  | SOp2 of string * ('t, 's) _svalue * ('t, 's) _svalue
  | SOp3 of string * ('t, 's) _svalue * ('t, 's) _svalue * ('t, 's) _svalue
  | SApp of ('t, 's) _svalue * ('t, 's) _svalue list

type 'a prop = {
  value : 'a option;
  getter : sheaplabel option;
  setter : sheaplabel option;
  writable : bool;
  config : bool;
  enum : bool;
}

(* 'v is a svalue, 'c is a closure *)
type 'v props = { fields : 'v prop IdMap.t; more_but_fields : IdSet.t option }
    (* if more_but_fields is Some set then the object can have more fields but not those in fields and in this set
       if a field is in the set, then not only has-own-property return false but also has-property
    *)

type 'c internal_props = {
  proto : sheaplabel option;
  _class : string;
  extensible : bool;
  code : 'c option;
}


let props_is_empty { fields; more_but_fields } = more_but_fields = None && IdMap.is_empty fields


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
  let sop2 ~typ o v1 v2 = SSymb (typ, SOp2(o, v1, v2))
  let sop3 ~typ o v1 v2 v3 = SSymb (typ, SOp3(o, v1, v2, v3))
  let sapp ~typ v vl = SSymb (typ, SApp(v, vl))
  let sid ~typ id = SSymb (typ, SId id)

  let internal_props =
    { proto = None; _class = "Object";
      extensible = false; code = None }

  let empty_props =
    { fields = IdMap.empty; more_but_fields = None }
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
