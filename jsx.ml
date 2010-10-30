open MyPervasives

module Inputs =
struct

  type input_type =
    | File of string
    | InChannel of string * in_channel
    | String of string * string

  type code_type = JS | LJS | Env

  let add_input inputs code_type input =
    inputs := (code_type, input) :: !inputs

  let add_file inputs code_type filename =
    if filename = "STDIN" then
      add_input inputs code_type (InChannel (filename, stdin))
    else
      let check_access x = Unix.access x [Unix.F_OK; Unix.R_OK] in
      let _ = Unix.handle_unix_error check_access filename in
      add_input inputs code_type (File filename)

  let add_any_file inputs filename =
    let code_type =
      if filename = "STDIN" then
	JS
      else
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
  let opt_eval = ref false
  let opt_features = ref false
  let opt_pretty = ref false
  let opt_xeval = ref true

  (* 'a -> 'a functions for options *)
  let ifoption opt_ref f x = if !opt_ref then f x else x

  (* need OCaml 3.12 to get rid of f x ? *)
  let if_eval f x = ifoption opt_eval f x
  let if_features f x = ifoption opt_features f x
  let if_pretty f x = ifoption opt_pretty f x
  let if_xeval f x = ifoption opt_xeval f x


  let arg_speclist =
    let speclist =
      [
	"-js", Arg.String (add_file inputs JS), "<file> Load <file> as JavaScript";
	"-ljs", Arg.String (add_file inputs LJS), "<file> Load <file> as LambaJS.ES5";
	"-env", Arg.String (add_file inputs Env), "<file> Load <file> as environment (LambdaJS.ES5)";
      ]
    in
    let boolspeclist =
      [
	"eval", opt_eval, "evaluation of code";
	"features", opt_features, "listing of used features";
	"pretty", opt_pretty, "pretty printing of code";
	"xeval", opt_xeval, "symbolic evaluation of code";
      ]
    in
    let turn l (name, r, meaning) =
      ("-" ^ name, Arg.Set r, " Turn on " ^ meaning ^ (if !r then " (default)" else ""))
      ::("-no-" ^ name, Arg.Clear r, " Turn off " ^ meaning ^ (if !r then "" else " (default)"))
      ::l
    in
    Arg.align (List.sort Pervasives.compare (List.fold_left turn speclist boolspeclist))

  let arg_usage = sprintf "Usage: %s [options] <file> ..." (Filename.basename Sys.executable_name)

  let arg_parse () = Arg.parse arg_speclist (add_any_file inputs) arg_usage

  let error_usage errmsg =
    Arg.usage arg_speclist (errmsg ^ "\n\n" ^ arg_usage);
    exit 1

end


module Parsers =
struct

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
    let eseq ljs1 ljs2 =
      LambdaJS.Syntax.ESeq (LambdaJS.Prelude.dummy_pos, ljs1, ljs2)
    in
    match code_type with
    | Inputs.JS -> try_parse JS.Parser.program JS.Lexer.token lexbuf (JS.Interm.from_javascript @> LambdaJS.Desugar.ds_top @> eseq prev_ljs)
    | Inputs.LJS -> try_parse LambdaJS.Parser.prog LambdaJS.Lexer.token lexbuf (LambdaJS.Syntax.raw_of_fine @> eseq prev_ljs)
    | Inputs.Env -> try_parse LambdaJS.Parser.env LambdaJS.Lexer.token lexbuf ((|>) prev_ljs)

  let from_inputs input_list =
    LambdaJS.Syntax.EConst (LambdaJS.Prelude.dummy_pos, JS.Syntax.CUndefined)
    |> List.fold_right from_input input_list

end


let main () =
  Options.arg_parse ();
  if !Options.inputs = [] then
    Options.error_usage "No input";
  if List.for_all (function (Inputs.Env, _) -> false | _ -> true) !Options.inputs then
    warning "Desugaring without environment";
  let raw_ljs = Parsers.from_inputs (!Options.inputs) in
  let fine_ljs = LambdaJS.Desugar.desugar raw_ljs in
  let raw_ljs = LambdaJS.Syntax.raw_of_fine fine_ljs in
  if !Options.opt_pretty then begin
    LambdaJS.Pretty.exp raw_ljs Prelude.Format.std_formatter;
    print_newline ();
  end;
  if !Options.opt_features then begin
    let m = FeaturesList.of_exp raw_ljs in
    print_endline (FeaturesList.Pretty.string_of_map ~sort_max:true m);
  end;
  if !Options.opt_eval then begin
    let _ = LambdaJS.Eval.eval_expr fine_ljs in
    print_newline ();
  end;
  if !Options.opt_xeval then
    let sl = XEval.xeval fine_ljs SymbolicState.empty_sstate in
    print_endline (SymbolicState.ToString.state_list sl)

let _ =
  Printexc.record_backtrace true;
  let _ = try main () with
    e ->
      print_endline (Printexc.to_string e);
      Printexc.print_backtrace stdout
  in
  (* pp_print_flush std_formatter (); *)
  (* pp_print_flush err_formatter (); *)
  ()
