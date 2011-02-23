
include LambdaJS.Prelude

let (&) f x = f x
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

  let assoc_opt x l = try Some (assoc x l) with
  | Not_found -> None

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

(*
product [1;2] [A;B] gives [(1, A); (1, B); (2, A); (2, B)]
*)
  let product list1 list2 =
    let rec aux l1 l2 acc = match l1, l2 with
    | [], _ -> acc
    | _::l1, [] -> aux l1 list2 acc
    | x::_, y::l2 -> aux l1 l2 ((x, y)::acc)
    in rev (aux list1 list2 [])
(*
tr_product [1;2] [A;B] gives [(1, A); (2, A); (1, B); (2, B)]
*)
  let tr_product list1 list2 =
    let rec aux l1 l2 acc = match l1, l2 with
    | _, [] -> acc
    | [], _::l2 -> aux list1 l2 acc
    | x::l1, y::_ -> aux l1 l2 ((x, y)::acc)
    in rev (aux list1 list2 []);;

  let assoc_flip l = List.map (fun (x,y)->y,x) l
end

module Big_int =
struct
  include Big_int

  (* shift_right finally returns 0 with a positive sign *)
  (* will be fixed in OCaml >= 3.12.1 *)
  let buggy_zero_big_int = shift_right_towards_zero_big_int (big_int_of_int 1) 1

  let count_bits bi = assert (ge_big_int bi zero_big_int);
    let rec aux bi =
      if eq_big_int bi zero_big_int || eq_big_int bi buggy_zero_big_int then
	0
      else
	1 + (aux (shift_right_towards_zero_big_int bi 1))
    in aux bi

  let simplify_fraction (h, l) =
    let gcd = gcd_big_int h l in
    div_big_int h gcd, div_big_int l gcd

  let is_int_fraction (h, l) =
    is_int_big_int h && is_int_big_int l

  let int_of_fraction (h, l) =
    (int_of_big_int h, int_of_big_int l)
end

module String =
struct
  include String

  let index_or_zero s c = try index s c with Not_found -> 0
  let index_or_length s c = try index s c with Not_found -> length s
  let after s i = sub s i (length s - i)
  let safe_after s i = if i < 0 then s else if i >= length s then "" else after s i
  let left s n = sub s 0 (min n (length s))
  let between s i1 i2 = sub s (i1+1) (max 0 (i2-i1-1))

  let before_char s c = try sub s 0 (index s c) with Not_found -> ""
  let after_char s c = try after s (index s c + 1) with Not_found -> ""
  let between_chars s c1 c2 = try
    let i1 = index s c1 in
    let i2 = try index_from s (i1+1) c2 with
      Not_found -> length s in
    sub s (i1+1) (i2-i1-1) with
    _ -> ""

  let split2 char_sep s =
    try let i = index s char_sep in left s i, after s (i+1) with
      Not_found -> s, ""

  let nsplit_char char_sep s =
    let rec aux i =
      try let j = index_from s i char_sep in (sub s i (j-i))::(aux (j+1)) with
      | Invalid_argument _ -> [""]
      | Not_found -> [after s i]
    in
    if s = "" then [] else aux 0

  let interline ?(sep='\n') ins = nsplit_char sep @> concat (sprintf "%c%s" sep ins)

  let to_array s = Array.init (length s) (fun i -> s.[i])

  let of_array a =
    let l = Array.length a in
    let s = create l in
    for i = 0 to l - 1 do s.[i] <- a.(i) done;
    s

  let map f s = for i = 0 to length s - 1 do s.[i] <- f s.[i] done
  let map_copy f s = let s = copy s in map f s; s

  let repl_char c1 c2 s = map_copy (fun c -> if c = c1 then c2 else c) s    

  let for_all p s =
    let res = ref true in
    iter (fun c -> if not (p c) then res := false) s;
    !res

  let pad_left c len s =
    let l = length s in
    if l >= len then
      s
    else
      let r = String.make len c in
      String.blit s 0 r (len - l) l;
      r

  module Numeric =
  struct
    let is_numeric = for_all (fun c -> c >= '0' && c <= '9')

    let is_zero = for_all ((=) '0')
  end

  (* Converts an ASCII string to a big_int
     First char corresponds to the 8-lowest bits
  *)
  let to_big_int s =
    let rec aux i bi =
      if i < 0 then
	bi
      else
	bi
	|> Big_int.mult_int_big_int 256
	|> Big_int.add_int_big_int (Char.code s.[i])
	|> aux (i-1)
    in aux ((length s) - 1) Big_int.zero_big_int

  let of_big_int =
    let bi256 = Big_int.big_int_of_int 256 in
    let rec aux bi =
    if Big_int.eq_big_int bi Big_int.zero_big_int then
      ""
    else
      let q, r = Big_int.quomod_big_int bi bi256 in
      let l = Big_int.int_of_big_int r |> Char.chr |> String.make 1 in
      let h = aux q in
      l ^ h
    in aux
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

  let fold_leftr2 : ('a -> 'b -> 'c -> 'c) -> 'a array -> 'b array -> 'c -> 'c =
    fun f arr1 arr2 acc ->
      assert (length arr1 = length arr2);
      let f' (acc, i) elt1 = (f elt1 arr2.(i) acc), (i+1) in
      fst (Array.fold_left f' (acc, 0) arr1)


  let split : ('a * 'b) array -> 'a array * 'b array =
    fun a ->
      let n = length a in
      (init n (fun i -> fst (a.(i)))), (init n (fun i -> snd (a.(i))))

  let find_map : ('a -> 'b option) -> 'a array -> 'b option =
    fun f a ->
      let l = length a in
      let rec aux i =
	if i = l then None
	else match f a.(i) with
	| Some x -> Some x
	| None -> aux (i+1)
      in aux 0
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
