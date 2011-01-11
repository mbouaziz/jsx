%{
(* 
   Parser for: SMT-LIB Standard version 2.0 (release Aug 28, 2010)
   No Theory Declaration
   No Logic Declaration
   No set-option, get-info

   Extensions (from Z3):
   define-sorts
   declare-datatypes
   1 by default for push/pop
*)
open MyPervasives

module Mk = SMTLib2Syntax.Mk

%}

%token <SMTLib2Syntax.binary> Binary
%token <SMTLib2Syntax.hexadecimal> Hexadecimal
%token <SMTLib2Syntax.decimal> Decimal
%token <SMTLib2Syntax.numeral> Numeral
%token <string> String
%token <SMTLib2Syntax.symbol> Symbol
%token <SMTLib2Syntax.keyword> Keyword

%token Par NUMERAL DECIMAL STRING Underscore
%token Excl As Let ForAll Exists
%token SetLogic SetOption SetInfo DeclareSort
%token DefineSort DeclareFun DefineFun Push Pop
%token Assert CheckSat GetAssertions GetProof
%token GetUnsatCore GetValue GetAssignment GetOption
%token GetInfo Exit

%token DefineSorts DeclareDatatypes

%token LParen RParen
%token LSqBracket RSqBracket Colon
%token EOF

%start script
%type <SMTLib2Syntax.script> script

%%

spec_constant:
  | x=Numeral { Mk.Const.numeral ($startpos, $endpos) x }
  | x=Decimal { Mk.Const.decimal ($startpos, $endpos) x }
  | x=Hexadecimal { Mk.Const.hexadecimal ($startpos, $endpos) x }
  | x=Binary { Mk.Const.binary ($startpos, $endpos) x }
  | x=String { Mk.Const.string ($startpos, $endpos) x }

s_expr:
  | x=spec_constant { Mk.SExpr.constant ($startpos, $endpos) x }
  | x=Symbol { Mk.SExpr.symbol ($startpos, $endpos) x }
  | x=Keyword { Mk.SExpr.keyword ($startpos, $endpos) x }
  | LParen x=s_expr* RParen { Mk.SExpr.app ($startpos, $endpos) x }

numeral_indexes_r:
  | x=Numeral RSqBracket { [x] }
  | x=Numeral Colon l=numeral_indexes_r { x::l }

identifier:
  | x=Symbol { Mk.Id.symbol ($startpos, $endpos) x }
  | LParen Underscore s=Symbol nl=Numeral+ RParen { Mk.Id.indexed_symbol ($startpos, $endpos) s nl }
  | s=Symbol LSqBracket nl=numeral_indexes_r { Mk.Id.indexed_symbol ($startpos, $endpos) s nl }

attribute_value:
  | x=spec_constant { Mk.AttrVal.constant ($startpos, $endpos) x }
  | x=Symbol { Mk.AttrVal.symbol ($startpos, $endpos) x }
  | LParen x=s_expr* RParen { Mk.AttrVal.app ($startpos, $endpos) x }

attribute:
  | x=Keyword { Mk.Attr.keyword ($startpos, $endpos) x }
  | k=Keyword v=attribute_value { Mk.Attr.keyword_value ($startpos, $endpos) k v }

sort:
  | x=identifier { Mk.Sort.id ($startpos, $endpos) x }
  | LParen i=identifier sl=sort+ RParen { Mk.Sort.app ($startpos, $endpos) i sl }

qual_identifier:
  | x=identifier { Mk.QualId.id ($startpos, $endpos) x }
  | LParen As i=identifier s=sort RParen { Mk.QualId.app_as ($startpos, $endpos) i s }

var_binding:
  | LParen s=Symbol t=term RParen { Mk.VarBinding.app ($startpos, $endpos) s t }

sorted_var:
  | LParen x=Symbol s=sort RParen { Mk.SortedVar.app ($startpos, $endpos) x s }

quant:
  | ForAll { Mk.Term.for_all }
  | Exists { Mk.Term.exists }

term:
  | x=spec_constant { Mk.Term.constant ($startpos, $endpos) x }
  | x=qual_identifier { Mk.Term.qual_id ($startpos, $endpos) x }
  | LParen q=qual_identifier t=term+ RParen { Mk.Term.app_qual_id ($startpos, $endpos) q t }
  | LParen Let LParen v=var_binding+ RParen t=term RParen { Mk.Term.app_let ($startpos, $endpos) v t }
  | LParen q=quant LParen s=sorted_var+ RParen t=term RParen { q ($startpos, $endpos) s t }
  | LParen Excl t=term a=attribute+ RParen { Mk.Term.excl ($startpos, $endpos) t a }

shorthand_sort:
  | LParen i=identifier s=sort RParen { Mk.Sort.shorthand ($startpos, $endpos) i s }

constructor_decl:
  | i=identifier { Mk.Datatypes.id ($startpos, $endpos) i }
  | LParen i=identifier s=shorthand_sort+ RParen { Mk.Datatypes.app ($startpos, $endpos) i s }

datatype:
  | LParen i=identifier c=constructor_decl+ RParen { Mk.Datatypes.datatype ($startpos, $endpos) i c }

command:
  | LParen SetLogic s=Symbol RParen { Mk.Cmd.set_logic ($startpos, $endpos) s }
  | LParen SetInfo a=attribute RParen { Mk.Cmd.set_info ($startpos, $endpos) a }
  | LParen DeclareSort s=Symbol n=Numeral RParen { Mk.Cmd.declare_sort ($startpos, $endpos) s n }
  | LParen DefineSort x=Symbol LParen xl=Symbol* RParen s=sort RParen { Mk.Cmd.define_sort ($startpos, $endpos) x xl s }
  | LParen DeclareFun x=Symbol LParen sl=sort* RParen s=sort RParen { Mk.Cmd.declare_fun ($startpos, $endpos) x sl s }
  | LParen DefineFun x=Symbol LParen sl=sorted_var* RParen s=sort t=term RParen { Mk.Cmd.define_fun ($startpos, $endpos) x sl s t }
  | LParen Push RParen { Mk.Cmd.push ($startpos, $endpos) Mk.Const.numeral_one }
  | LParen Push n=Numeral RParen { Mk.Cmd.push ($startpos, $endpos) n }
  | LParen Pop RParen { Mk.Cmd.pop ($startpos, $endpos) Mk.Const.numeral_one }
  | LParen Pop n=Numeral RParen { Mk.Cmd.pop ($startpos, $endpos) n }
  | LParen Assert t=term RParen { Mk.Cmd.app_assert ($startpos, $endpos) t }
  | LParen CheckSat RParen { Mk.Cmd.check_sat ($startpos, $endpos) () }
  | LParen GetAssertions RParen { Mk.Cmd.get_assertions ($startpos, $endpos) () }
  | LParen GetProof RParen { Mk.Cmd.get_proof ($startpos, $endpos) () }
  | LParen GetUnsatCore RParen { Mk.Cmd.get_unsat_core ($startpos, $endpos) () }
  | LParen GetValue LParen t=term+ RParen RParen { Mk.Cmd.get_value ($startpos, $endpos) t }
  | LParen GetAssignment RParen { Mk.Cmd.get_assignment ($startpos, $endpos) () }
  | LParen GetOption k=Keyword RParen { Mk.Cmd.get_option ($startpos, $endpos) k }
  | LParen Exit RParen { Mk.Cmd.app_exit ($startpos, $endpos) () }
  | LParen DefineSorts LParen s=shorthand_sort* RParen RParen { Mk.Cmd.define_sorts ($startpos, $endpos) s }
  | LParen DeclareDatatypes LParen d=datatype* RParen RParen { Mk.Cmd.declare_datatypes ($startpos, $endpos) d }

script:
  | cl=command* EOF { Mk.Script.list ($startpos, $endpos) cl }

%%
