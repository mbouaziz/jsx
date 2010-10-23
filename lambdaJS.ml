
module Desugar = Es5_desugar
module Eval = Es5_eval
module Lexer = Es5_lexer
module Parser = Es5_parser
module Prelude = Prelude
module Pretty = Es5_pretty
module Syntax =
struct
  include Es5_syntax

  type raw_exp = src_exp
  type fine_exp = prim_exp

  let raw_of_fine (e : fine_exp) = (e :> raw_exp)
  let fine_of_raw = Desugar.check_op

end
