open MyPervasives

module Inputs =
struct

  type input_type =
    | File of string
    | InChannel of string * in_channel
    | String of string * string

  type code_type = JS | LJS | ENV

  let add_input inputs code_type input =
    inputs := (code_type, input) :: !inputs

  let add_file inputs code_type filename =
    let check_access x = Unix.access x [Unix.F_OK; Unix.R_OK] in
    Unix.handle_unix_error check_access filename;
    add_input inputs code_type (File filename)

  let add_any_file inputs filename =
    if filename = "STDIN" then
      add_input inputs JS (InChannel (filename, stdin))
    else
      let code_type =
	match Filename.get_suffix filename with
	| ".js" -> JS
	| ".ljs" | ".jsl" | ".es5" -> LJS
	| ".env" -> Env
	| suffix -> failwith (sprintf "Unknown suffix \"%s\" for file \"%s\"" suffix filename)
      in
      add_file inputs code_type filename

end

module Options =
struct

  open Inputs

  (* inputs *)
  let inputs = ref []

  (* options and their default values *)
  let opt_desugar = ref true
  let opt_pretty = ref true

  (* 'a -> 'a functions for options *)
  let ifoption opt_ref f x = if !opt_ref then f x else x

  let if_desugar = ifoption opt_desugar
  let if_pretty = ifoption opt_pretty


  let arg_speclist = Arg.align
    [
      "-js", Arg.String (add_file inputs JS), "<file> Load <file> as JavaScript";
      "-ljs", Arg.String (add_file inputs LJS), "<file> Load <file> as LambaJS.ES5";
      "-env", Arg.String (add_file inputs Env), "<file> Load <file> as environment (LambdaJS.ES5)";
      "-pretty", Arg.Set opt_pretty, "Turn on pretty printing of code (default)";
      "-no-pretty", Arg.Clear opt_pretty, "Turn off pretty printing of code";
      "-desugar", Arg.Set opt_desugar, "Turn on desugaring of code (default)";
      "-no-desugar", Arg.Clear opt_desugar, "Turn off desugaring of code";
    ]

  let arg_usage = sprintf "Usage: %s [options] <file> ..." Sys.executable_name

  let arg_parse () = Arg.parse arg_speclist (add_any_file inputs) arg_usage

  let error_usage errmsg =
    Arg.usage arg_speclist (errmsg ^ "\n\n" ^ arg_usage);
    exit 1

end

module Parsers =
struct

  let dummy_pos = LambdaJS.Prelude.dummy_pos

  let empty_ljs =
    LambdaJS.Syntax.EConst (dummy_pos, JS.Syntax.CUndefined)

  let try_parse parse lexe lexbuf f =
    let curpos lexbuf =
      LambdaJS.Prelude.string_of_position (lexbuf.Lexing.lex_curr_p, lexbuf.Lexing.lex_curr_p)
    in
    let x = try parse lexe lexbuf with
    | Failure "lexing: empty token" ->
	failwith (sprintf "Lexical error at %s" (curpos lexbuf))
    | JS.Parser.Error
    | LambdaJS.Parser.Error ->
        failwith (sprintf "Parse error at %s; unexpected token %s" (curpos lexbuf) (Lexing.lexeme lexbuf))
    in f x

  let from_input (code_type, input_type) prev_ljs =
    let fname, lexbuf = match input_type with
    | Inputs.File fname -> fname, Lexing.from_channel (open_in fname)
    | Inputs.InChannel (fname, cin) -> fname, Lexing.from_channel cin
    | Inputs.String (fname, s) -> fname, Lexing.from_string s
    in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = fname };
    match code_type with
    | Inputs.JS ->
	let from_js js =
	  let interm = JS.Interm.from_javascript js in
	  let ljs = LambdaJS.Desugar.ds_top interm in
	  let ljs = Options.if_desugar LambdaJS.Desugar.desugar ljs in
	  LambdaJS.Syntax.ESeq (dummy_pos, prev_ljs, ljs)
	in
	try_parse JS.Parser.program JS.Lexer.token lexbuf from_js
    | Inputs.LJS ->
	let from_ljs ljs =
	  let ljs = Options.if_desugar LambdaJS.Desugar.desugar ljs in
	  LambdaJS.Syntax.ESeq (dummy_pos, prev_ljs, ljs)
	in
	try_parse LambdaJS.Parser.prog LambdaJS.Lexer.token lexbuf from_ljs
    | Inputs.Env ->
	let from_env env =
	  LambdaJS.Env.enclose_in_env env prev_ljs
	in
	try_parse LambdaJS.Parser.env LambdaJS.Lexer.token lexbuf from_env

  let from_inputs input_list =
    List.fold_right from_input input_list empty_ljs

end


let main () =
  Options.arg_parse ();
  if !Options.inputs = [] then
    Options.error_usage "No input";
  if !Options.opt_desugar && List.for_all (function (Env, _) -> false | _ -> true) then
    warning "Desugaring without environment"
  let parsed_inputs = Parsers.from_inputs (!Options.inputs) in
  if !Options.opt_pretty then TODO
  if !Options.xeval then
    XEval.
