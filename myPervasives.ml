
include LambdaJS.Prelude

let (|>) x f = f x
let (@>) f g x = g (f x)


module Char =
struct
  include Char

  let is_alpha = function
    | 'a'..'z' | 'A'..'Z' -> true
    | _ -> false
end

module List =
struct
  include List

  let rec filter_map f = function
    | [] -> []
    | h::t -> match f h with
      | Some x -> x::(filter_map f t)
      | None -> filter_map f t

  let rev_filter_map f l =
    let rec rfmap_f accu = function
      | [] -> accu
      | h::t -> match f h with
	| Some x -> rfmap_f (x :: accu) t
	| None -> rfmap_f accu t
    in
    rfmap_f [] l

  (* fold_left but with fold_right syntax *)
  let fold_leftr f l acc =
    let f' a x = f x a in
    fold_left f' acc l

  let fold_leftr2 f l1 l2 acc =
    let f' a x1 x2 = f x1 x2 a in
    fold_left2 f' acc l1 l2

  let fold_map f acc l =
    let f' (acc, l) elt = let acc, elt = f acc elt in acc, (elt::l) in
    let acc, l = fold_left f' (acc, []) l in
    acc, (rev l)

  let fold_map_i f acc l =
    let f' (acc, i, l) elt = let acc, elt = f acc i elt in acc, (i+1), (elt::l) in
    let acc, _, l = fold_left f' (acc, 0, []) l in
    acc, (rev l)

  let rec fold_left3 : ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b list -> 'c list -> 'd list -> 'a =
    fun f acc l1 l2 l3 ->
      match l1, l2, l3 with
      | [], [], [] -> acc
      | h1::t1, h2::t2, h3::t3 -> fold_left3 f (f acc h1 h2 h3) t1 t2 t3
      | _ -> raise (Invalid_argument "fold_left3")
end


module String =
struct
  include String

  let nsplit_char char_sep s =
    let rec aux i =
      try let j = index_from s i char_sep in (sub s i (j-i))::(aux (j+1)) with
      | Invalid_argument _ -> [""]
      | Not_found -> [sub s i (length s - i)]
    in
    if s = "" then [] else aux 0

  let interline ?(sep='\n') ins = nsplit_char sep @> concat (sprintf "%c%s" sep ins)

  let after s i = sub s i (length s - i)
  let left s n = sub s 0 (min n (length s))

  let for_all p s =
    let res = ref true in
    iter (fun c -> if not (p c) then res := false) s;
    !res

  let is_numeric = for_all (fun c -> c >= '0' && c <= '9')
end


module Filename =
struct
  include Filename

  let get_suffix filename =
    let dot_index =
      try String.rindex filename '.' with
	Not_found -> String.length filename
    in
    String.sub filename dot_index ((String.length filename) - dot_index)

end

module Array =
struct
  include Array

  let fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array =
    fun f acc arr ->
      let f' (acc, lst) elt = let acc, elt = f acc elt in acc, (elt::lst) in
      let acc, lst = Array.fold_left f' (acc, []) arr in
      acc, (Array.of_list (List.rev lst))

  let fold_map_i : ('a -> int -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array =
    fun f acc arr ->
      let f' (acc, i, lst) elt = let acc, elt = f acc i elt in acc, (i+1), (elt::lst) in
      let acc, _, lst = Array.fold_left f' (acc, 0, []) arr in
      acc, (Array.of_list (List.rev lst))

  let fold_left_i : ('a -> int -> 'b -> 'a) -> 'a -> 'b array -> 'a =
    fun f acc arr ->
      let f' (acc, i) elt = (f acc i elt), (i + 1) in
      fst (Array.fold_left f' (acc, 0) arr)

  let fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a =
    fun f acc arr1 arr2 ->
      assert (length arr1 = length arr2);
      let f' (acc, i) elt1 = (f acc elt1 arr2.(i)), (i+1) in
      fst (Array.fold_left f' (acc, 0) arr1)

  let split : ('a * 'b) array -> 'a array * 'b array =
    fun a ->
      let n = length a in
      (init n (fun i -> fst (a.(i)))), (init n (fun i -> snd (a.(i))))
end

module StringMap = Map.Make(String)
module StringMmap = MultiMap.Make(String)
module IdMmap = MultiMap.Make(IdOrderedType)


let sprintf = Printf.sprintf

let pretty_position ?(alone=true) (p, e) =
  let open Lexing in
  if alone then
    sprintf "File \"%s\", line %d, characters %d-%d:" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol) (e.pos_cnum - e.pos_bol)
  else
    sprintf "file \"%s\", line %d, characters %d-%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol) (e.pos_cnum - e.pos_bol)

let warning msg =
  prerr_endline (sprintf "Warning: %s" msg)

let run_under_backtrace f check_print =
  Printexc.record_backtrace true;
  try f () with
    e ->
      print_endline (Printexc.to_string e);
      if check_print() then
	Printexc.print_backtrace stdout;
      exit 1
