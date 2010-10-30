
open MyPervasives
open SymbolicState

let res_e s e = { s with exn = Some e ; res = SExn e }
let resl_e s e = [res_e s e]
let err s msg =
  if !Options.opt_fatal then
    failwith msg
  else
    res_e s (SError msg)
let errl s msg = [err s msg]


(* Unary operators *)

let print v s = [{ s with io = SIO.print v s.io }]

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
