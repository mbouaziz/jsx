
open LambdaJS.Prelude

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

module StringMap = Map.Make(String)

module IdMmap = MultiMap.Make(IdOrderedType)


let sprintf = Printf.sprintf

let pretty_position (p, e) =
  let open Lexing in
  sprintf "File \"%s\", line %d, characters %d-%d:" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol) (e.pos_cnum - e.pos_bol)

let warning msg =
  prerr_endline (sprintf "Warning: %s" msg)
