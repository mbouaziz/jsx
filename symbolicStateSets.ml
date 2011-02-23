
open MyPervasives

module type StateSet =
sig
  type 'a t
  val singleton : 'a -> 'a t
  val get_first : 'a t -> 'a
  val get_next : 'a t -> (unit -> 'a t) option
  val map_unit : ('a -> 'b) -> 'a t -> 'b t
  val map : ('a -> 'b t) -> 'a t -> 'b t
  val seq : 'a t -> (unit -> 'a t) -> 'a t
end


module StateSet_DFS : StateSet =
struct
  type 'a t = 'a * (unit -> 'a t) option
  let singleton a = a, None
  let get_first = fst
  let get_next = snd

  let next_map g = function
    | None -> None
    | Some f -> Some (f @> g)
  let app_snd f (x, y) = x, f y
  let rec next_seq_def g2 = function
    | None -> Some g2
    | Some g1 -> Some (g1 @> app_snd (next_seq_def g2))
  let next_seq n1 = function
    | None -> n1
    | Some g2 -> next_seq_def g2 n1

  let rec map_unit f (a, n) = f a, next_map (map_unit f) n
  let rec map f (a, n) = let a, n' = f a in a, next_seq n' (next_map (map f) n)
  let seq (a, n) f = a, next_seq_def f n
end

module StateSet_BFS : StateSet =
struct
  type 'a t = 'a list
  let singleton a = [a]
  let get_first = List.hd
  let get_next = function
    | _::((_::_) as l) -> Some (fun () -> l)
    | _ -> None
  let map_unit = List.map
  let map f = List.map f @> List.flatten
  let seq l f = l @ (f ())
end
