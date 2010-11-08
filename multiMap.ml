
open LambdaJS.Prelude

module type OrderedType = Map.OrderedType

module type S = sig

  type key
  type +'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val mem : key -> 'a t -> bool
  val push : key -> 'a -> 'a t -> 'a t
  val replace : key -> 'a -> 'a t -> 'a t
  val replace_all : key -> 'a -> 'a t -> 'a t
  val pop : key -> 'a t -> 'a t
  val pop_all : key -> 'a t -> 'a t
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val for_all : (key -> 'a -> bool) -> 'a t -> bool
  val exists : (key -> 'a -> bool) -> 'a t -> bool
  val cardinal : 'a t -> int
  val find : key -> 'a t -> 'a
  val find_opt : key -> 'a t -> 'a option
  val bindings : 'a t -> (key * 'a) list

end

module Make (Ord : OrderedType) : S with type key = Ord.t =
struct

  module M = Map.Make(Ord)

  type key = Ord.t

  type 'a t = 'a list M.t

  let empty = M.empty

  let is_empty = M.is_empty

  let mem = M.mem

  let push k v m = M.add k (v::try M.find k m with Not_found -> []) m

  (* produces an error if k is unbound, not like pop then push *)
  let replace k v m = M.add k (v::(List.tl (M.find k m))) m

  let replace_all k v m = M.add k [v] m

  let singleton k v = M.add k [v] empty

  let pop k m = match try Some (M.find k m) with Not_found -> None with
  | None -> m
  | Some [_] -> M.remove k m
  | Some v -> M.add k (List.tl v) m

  let pop_all = M.remove

  let list_compare cmp l1 l2 =
    let rec aux = function
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | h1::t1, h2::t2 ->
	  let c = cmp h1 h2 in
	  if c = 0 then aux (t1, t2) else c
    in aux (l1, l2)

  let compare cmp = M.compare (list_compare cmp)

  let list_equal eq l1 l2 =
    let rec aux = function
      | [], [] -> true
      | h1::t1, h2::t2 when eq h1 h2 -> aux (t1, t2)
      | _ -> false
    in aux (l1, l2)

  let equal eq = M.equal (list_equal eq)

  let onhd f k x = f k (List.hd x)

  let iter f = M.iter (onhd f)

  let fold f = M.fold (onhd f)

  let for_all f = M.for_all (onhd f)

  let exists f = M.exists (onhd f)

  let cardinal = M.cardinal

  let find k m = List.hd (M.find k m)

  let find_opt k m = match M.find_opt k m with
  | Some x -> Some (List.hd x)
  | None -> None

  let bindings m = List.map (fun (k, l) -> k, List.hd l) (M.bindings m)

end
