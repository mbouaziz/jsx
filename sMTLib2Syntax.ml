
type pos = Lexing.position * Lexing.position

type numeral = string
type decimal = string * string
type hexadecimal = string
type binary = string

type symbol = string
type keyword = string

type constant =
  | Numeral of numeral
  | Decimal of decimal
  | Hexadecimal of hexadecimal
  | Binary of binary
  | String of string

type index =
  | INumeral of numeral
  | ISymbol of symbol

type s_expr =
  | EConstant of constant
  | ESymbol of symbol
  | EKeyword of keyword
  | EApp of s_expr list

type attribute_value =
  | AConstant of constant
  | ASymbol of symbol
  | AApp of s_expr list

type identifier = symbol * index list
type attribute = keyword * attribute_value option
type sort = identifier * sort list
type shorthand_sort = identifier * sort
type constructor_decl = identifier * shorthand_sort list
type datatype = identifier * constructor_decl list
type qual_identifier = identifier * sort option
type sorted_var = symbol * sort
type quant = ForAll | Exists

type var_binding = symbol * term

and term =
  | TConstant of constant
  | TAppQualId of qual_identifier * term list
  | TLet of var_binding list * term
  | TQuant of quant * sorted_var list * term
  | TExcl of term * attribute list

type command =
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
  | Define of (symbol * sorted_var list * term)
  | DefineSorts of shorthand_sort list
  | DeclareDatatypes of datatype list

type script = command list

module Mk =
struct

  let dummy_pos = Lexing.dummy_pos, Lexing.dummy_pos

  module Index =
  struct
    let numeral pos x = INumeral x
    let symbol pos x = ISymbol x
  end

  module Const =
  struct
    let numeral pos x = Numeral x
    let decimal pos x = Decimal x
    let hexadecimal pos x = Hexadecimal x
    let binary pos x = Binary x
    let string pos x = String x

    let numeral_one = "1"
  end

  module SExpr =
  struct
    let constant pos x = EConstant x
    let symbol pos x = ESymbol x
    let keyword pos x = EKeyword x
    let app pos x = EApp x
  end

  module Id =
  struct
    let symbol pos x = x, []
    let indexed_symbol pos s nl = s, nl
  end

  module AttrVal =
  struct
    let constant pos x = AConstant x
    let symbol pos x = ASymbol x
    let app pos x = AApp x
  end

  module Attr =
  struct
    let keyword pos x = x, None
    let keyword_value pos k v = k, Some v
  end

  module Sort =
  struct
    let id pos x = x, []
    let app pos i sl = i, sl
    let shorthand pos i s = i, s
  end

  module Datatypes =
  struct
    let datatype pos i c = i, c
    let id pos i = i, []
    let app pos i s = i, s
  end

  module QualId =
  struct
    let id pos x = x, None
    let app_as pos i s = i, Some s
  end

  module VarBinding =
  struct
    let app pos s t = s, t
  end

  module SortedVar =
  struct
    let app pos x s = x, s
  end

  module Term =
  struct
    let constant pos x = TConstant x
    let qual_id pos x = TAppQualId (x, [])
    let app_qual_id pos q t = TAppQualId (q, t)
    let app_let pos v t = TLet (v, t)
    let for_all pos s t = TQuant (ForAll, s, t)
    let exists pos s t = TQuant (Exists, s, t)
    let excl pos t a = TExcl (t, a)
  end

  module Cmd =
  struct
    let set_logic pos s = SetLogic s
    let set_info pos a = SetInfo a
    let declare_sort pos s n = DeclareSort (s, n)
    let define_sort pos x xl s = DefineSort (x, xl, s)
    let declare_fun pos x sl s = DeclareFun (x, sl, s)
    let define_fun pos x sl s t = DefineFun (x, sl, s, t)
    let push pos n = Push n
    let pop pos n = Pop n
    let app_assert pos t = Assert t
    let check_sat pos () = CheckSat
    let get_assertions pos () = GetAssertions
    let get_proof pos () = GetProof
    let get_unsat_core pos () = GetUnsatCore
    let get_value pos t = GetValue t
    let get_assignment pos () = GetAssignment
    let get_option pos k = GetOption k
    let app_exit pos () = Exit
    let define pos x sl t = Define (x, sl, t)
    let define_sorts pos s = DefineSorts s
    let declare_datatypes pos d = DeclareDatatypes d
  end

  module Script =
  struct
    let list pos cl = cl
  end

end
