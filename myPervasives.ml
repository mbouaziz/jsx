
open LambdaJS.Prelude

let (|>) x f = f x
let (@>) f g x = g (f x)

let sprintf = Printf.sprintf

let pretty_position (p, e) =
  let open Lexing in
  sprintf "File \"%s\", line %d, characters %d-%d:" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol) (e.pos_cnum - e.pos_bol)

let warning msg =
  prerr_endline (sprintf "Warning: %s" msg)

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
