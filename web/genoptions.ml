
open MyPervasives

let php_of_boolspec (specname, opt_ref, desc) =
  sprintf "'%s' => array(%B, '%s')" specname !opt_ref desc

let php_make_array name body =
  body
  |> String.concat ",\n"
  |> String.interline "\t"
  |> sprintf "$%s = array(\n\t%s\n);\n" name

let php_code body = sprintf "<?\n\n%s\n\n?>" body

let _ =
  Options.boolspeclist
  |> List.map php_of_boolspec
  |> php_make_array "boolspeclist"
  |> php_code
  |> print_endline
