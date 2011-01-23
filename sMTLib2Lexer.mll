{
open Lexing
open MyPervasives
open SMTLib2Parser
}

let bin = ['0' '1']
let digit = ['0'-'9']
let hex = ['0'-'9' 'A'-'F' 'a'-'f']
let symb0 = ['A'-'Z' 'a'-'z' '~' '!' '@' '$' '%' '^' '&' '*' '_' '-' '+' '=' '<' '>' '.' '?' '/']
let symb1 = ['0'-'9' 'A'-'Z' 'a'-'z' '~' '!' '@' '$' '%' '^' '&' '*' '_' '-' '+' '=' '<' '>' '.' '?' '/']

let binary = bin+
let numeral = '0' | (['1'-'9'] digit*)
let numeral_z = digit*
let hexadecimal = hex+
let symbol = symb0 symb1*

let blank = [ ' ' '\t' ]
let line_terminator = "\n\r" | '\n' | "\r\n" | '\r'

rule token = parse
  | ';' [^ '\r' '\n']* line_terminator { new_line lexbuf; token lexbuf }
  | ';' [^ '\r' '\n']* eof { EOF }
  | blank+ { token lexbuf }
  | line_terminator { new_line lexbuf; token lexbuf }
  | '(' { LParen }
  | ')' {  RParen }
  | '[' { LSqBracket }
  | ']' { RSqBracket }
  | "#b" (binary as x) { Binary x }
  | "#x" (hexadecimal as x) { Hexadecimal x }
  | (numeral as h) '.' (numeral_z as l) { Decimal (h, l) }
  | numeral as x { Numeral x }
  | '"' { String (string_lit '"' [] lexbuf) }
  | '_' { Underscore }
  | '!' { Excl }
  | "DECIMAL" { DECIMAL }
  | "NUMERAL" { NUMERAL }
  | "STRING" { STRING }
  | "assert" { Assert }
  | "as" { As }
  | "check-sat" { CheckSat }
  | "declare-datatypes" { DeclareDatatypes }
  | "declare-fun" { DeclareFun }
  | "declare-sort" { DeclareSort }
  | "define-fun" { DefineFun }
  | "define-sorts" { DefineSorts }
  | "define-sort" { DefineSort }
  | "define" { Define }
  | "exists" { Exists }
  | "exit" { Exit }
  | "forall" { ForAll }
  | "get-assertions" { GetAssertions }
  | "get-assignment" { GetAssignment }
  | "get-info" { GetInfo }
  | "get-option" { GetOption }
  | "get-proof" { GetProof }
  | "get-unsat-core" { GetUnsatCore }
  | "get-value" { GetValue }
  | "let" { Let }
  | "par" { Par }
  | "pop" { Pop }
  | "push" { Push }
  | "set-info" { SetInfo }
  | "set-logic" { SetLogic }
  | "set-option" { SetOption }
  | symbol as x { Symbol x }
  | '|' { Symbol (quoted_symbol '|' [] lexbuf) }
  | ':' (symbol as x) { Keyword x }
  | ':' { Colon }
  | eof { EOF }

and string_lit end_ch acc = parse
  (* multi-lines *)
  | line_terminator as x { new_line lexbuf; string_lit end_ch (x::acc) lexbuf }
  (* escape codes *)
  | "\\'"  { string_lit end_ch ("'"::acc) lexbuf }
  | "\\\"" { string_lit end_ch ("\""::acc) lexbuf }
  | "\\\\" { string_lit end_ch ("\\"::acc) lexbuf }
  | "\\b" { string_lit end_ch ("\b"::acc) lexbuf }
  | "\\n" { string_lit end_ch ("\n"::acc) lexbuf }
  | "\\r" { string_lit end_ch ("\r"::acc) lexbuf }
  | "\\t" { string_lit end_ch ("\t"::acc) lexbuf }
  | "\\v" { string_lit end_ch ("\x0b"::acc) lexbuf }
  | "\\ " { string_lit end_ch ("\ "::acc) lexbuf }
  | "\\0" { string_lit end_ch ("\x00"::acc) lexbuf }
  | "\\x" (hex hex as ascii) { string_lit end_ch ((String.make 1 (char_of_int (int_of_string ("0x" ^ ascii))))::acc) lexbuf }
  | [^ '\n' '\r' '\\' '"' '\'']+ as x { string_lit end_ch (x::acc) lexbuf }
  | _ as ch
      { if end_ch = ch then
	  String.concat "" (List.rev acc)
        else
          string_lit end_ch ((String.make 1 ch)::acc) lexbuf
      }

and quoted_symbol end_ch acc = parse
  | line_terminator as x { new_line lexbuf; quoted_symbol end_ch (x::acc) lexbuf }
  | [^ '\n' '\r' '\\' '|']+ as x { quoted_symbol end_ch (x::acc) lexbuf }
  | _ as ch
      { assert (ch <> '\\');
	if end_ch = ch then
	  String.concat "" (List.rev acc)
        else
          quoted_symbol end_ch ((String.make 1 ch)::acc) lexbuf
      }
