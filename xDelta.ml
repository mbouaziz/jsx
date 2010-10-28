
open MyPervasives

let op1 ~pos = function
  | op -> failwith (sprintf "%s\nError [xeval] No implementation of unary operator \"%s\"" (pretty_position pos) op)

let op2 ~pos = function
  | op -> failwith (sprintf "%s\nError [xeval] No implementation of binary operator \"%s\"" (pretty_position pos) op)

let op3 ~pos = function
  | op -> failwith (sprintf "%s\nError [xeval] No ternary operators yet, so what's this \"%s\"" (pretty_position pos) op)
