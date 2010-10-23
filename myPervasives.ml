
let (|>) x f = f x
let (@>) f g x = g (f x)

let sprintf = Printf.sprintf

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
module IdMmap = MultiMap.Make(struct
				type t = LambdaJS.Prelude.id
				let compare = Pervasives.compare
			      end)
