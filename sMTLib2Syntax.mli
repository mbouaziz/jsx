
type pos = Lexing.position * Lexing.position

type numeral = string
type decimal = string
type hexadecimal = string
type binary = string

type symbol = string
type keyword = string

type constant = private
  | Numeral of numeral
  | Decimal of decimal
  | Hexadecimal of hexadecimal
  | Binary of binary
  | String of string

type s_expr = private
  | EConstant of constant
  | ESymbol of symbol
  | EKeyword of keyword
  | EApp of s_expr list

type attribute_value = private
  | AConstant of constant
  | ASymbol of symbol
  | AApp of s_expr list

type identifier = symbol * numeral list
type attribute = private keyword * attribute_value option
type sort = identifier * sort list
type shorthand_sort = identifier * sort
type constructor_decl = identifier * shorthand_sort list
type datatype = identifier * constructor_decl list
type qual_identifier = identifier * sort option
type sorted_var = symbol * sort
type quant = ForAll | Exists

type var_binding = private symbol * term

and term = private
  | TConstant of constant
  | TAppQualId of qual_identifier * term list
  | TLet of var_binding list * term
  | TQuant of quant * sorted_var list * term
  | TExcl of term * attribute list

type command = private
  | SetLogic of symbol
  | SetInfo of attribute
  | DeclareSort of (symbol * numeral)
  | DefineSort of (symbol * symbol list * sort)
  | DeclareFun of (symbol * sort list * sort)
  | DefineFun of (symbol * sorted_var list * sort * term)
  | Push of numeral
  | Pop of numeral
  | Assert of term
  | CheckSat
  | GetAssertions
  | GetProof
  | GetUnsatCore
  | GetValue of term list
  | GetAssignment
  | GetOption of keyword
  | Exit
  | DefineSorts of shorthand_sort list
  | DeclareDatatypes of datatype list

type script = command list

module Mk :
sig
  val dummy_pos : pos

  module Const :
  sig
    val numeral : pos -> numeral -> constant
    val decimal : pos -> decimal -> constant
    val hexadecimal : pos -> hexadecimal -> constant
    val binary : pos -> binary -> constant
    val string : pos -> string -> constant

    val numeral_one : numeral
  end

  module SExpr :
  sig
    val constant : pos -> constant -> s_expr
    val symbol : pos -> symbol -> s_expr
    val keyword : pos -> keyword -> s_expr
    val app : pos -> s_expr list -> s_expr
  end

  module Id :
  sig
    val symbol : pos -> symbol -> identifier
    val indexed_symbol : pos -> symbol -> numeral list -> identifier
  end

  module AttrVal :
  sig
    val constant : pos -> constant -> attribute_value
    val symbol : pos -> symbol -> attribute_value
    val app : pos -> s_expr list -> attribute_value
  end

  module Attr :
  sig
    val keyword : pos -> keyword -> attribute
    val keyword_value : pos -> keyword -> attribute_value -> attribute
  end

  module Sort :
  sig
    val id : pos -> identifier -> sort
    val app : pos -> identifier -> sort list -> sort
    val shorthand : pos -> identifier -> sort -> shorthand_sort
  end

  module Datatypes :
  sig
    val datatype : pos -> identifier -> constructor_decl list -> datatype
    val id : pos -> identifier -> constructor_decl
    val app : pos -> identifier -> shorthand_sort list -> constructor_decl
  end

  module QualId :
  sig
    val id : pos -> identifier -> qual_identifier
    val app_as : pos -> identifier -> sort -> qual_identifier
  end

  module VarBinding :
  sig
    val app : pos -> symbol -> term -> var_binding
  end

  module SortedVar :
  sig
    val app : pos -> symbol -> sort -> sorted_var
  end

  module Term :
  sig
    val constant : pos -> constant -> term
    val qual_id : pos -> qual_identifier -> term
    val app_qual_id : pos -> qual_identifier -> term list -> term
    val app_let : pos -> var_binding list -> term -> term
    val for_all : pos -> sorted_var list -> term -> term
    val exists : pos -> sorted_var list -> term -> term
    val excl : pos -> term -> attribute list -> term
  end

  module Cmd :
  sig
    val set_logic : pos -> symbol -> command
    val set_info : pos -> attribute -> command
    val declare_sort : pos -> symbol -> numeral -> command
    val define_sort : pos -> symbol -> symbol list -> sort -> command
    val declare_fun : pos -> symbol -> sort list -> sort -> command
    val define_fun : pos -> symbol -> sorted_var list -> sort -> term -> command
    val push : pos -> numeral -> command
    val pop : pos -> numeral -> command
    val app_assert : pos -> term -> command
    val check_sat : pos -> unit -> command
    val get_assertions : pos -> unit -> command
    val get_proof : pos -> unit -> command
    val get_unsat_core : pos -> unit -> command
    val get_value : pos -> term list -> command
    val get_assignment : pos -> unit -> command
    val get_option : pos -> keyword -> command
    val app_exit : pos -> unit -> command
    val define_sorts : pos -> shorthand_sort list -> command
    val declare_datatypes : pos -> datatype list -> command
  end

  module Script :
  sig
    val list : pos -> command list -> script
  end

end
