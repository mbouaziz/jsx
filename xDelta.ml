
open MyPervasives
open SymbolicState

let err s msg = let exn = SError msg in { s with exn = Some exn ; res = SExn exn }
let errl s msg = [err s msg]


(* Unary operators *)

let print v s = [{ s with effects = Effects.print v s.effects }]

let err_op1 ~pos ~op _ s = errl s (sprintf "%s\nError [xeval] No implementation of unary operator \"%s\"" (pretty_position pos) op)

let op1 ~pos = function
  | "print" -> print
  | op -> err_op1 ~pos ~op

(* Binary operators *)

let err_op2 ~pos ~op _ _ s = errl s (sprintf "%s\nError [xeval] No implementation of binary operator \"%s\"" (pretty_position pos) op)

let op2 ~pos = function
  | op -> err_op2 ~pos ~op

(* Ternary operators *)

let err_op3 ~pos ~op _ _ _ s = errl s (sprintf "%s\nError [xeval] No ternary operators yet, so what's this \"%s\"" (pretty_position pos) op)

let op3 ~pos = function
  | op -> err_op3 ~pos ~op
