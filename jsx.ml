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
  let opt_desugar = ref true
  let opt_eval = ref true
  let opt_features = ref true
  let opt_pretty = ref true
  let opt_xeval = ref true

  (* 'a -> 'a functions for options *)
  let ifoption opt_ref f x = if !opt_ref then f x else x

  (* need OCaml 3.12 to get rid of f x ? *)
  let if_desugar f x  = ifoption opt_desugar f x
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
	"desugar", opt_desugar, "desugaring of code";
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

module LJS =
struct

  type raw_ljs = LambdaJS.Syntax.raw_exp
  type fine_ljs = LambdaJS.Syntax.fine_exp
  type ljs = RawLJS of raw_ljs | FineLJS of fine_ljs

  (* let raw_of_fine (e : fine_ljs) = (e :> raw_ljs) *)
  let fine = function
    | RawLJS e -> LambdaJS.Syntax.fine_of_raw e
    | FineLJS e -> e
  let raw = function
    | RawLJS e -> e
    | FineLJS e -> LambdaJS.Syntax.raw_of_fine e

  let dummy_pos = LambdaJS.Prelude.dummy_pos

  let empty_ljs = FineLJS
    (LambdaJS.Syntax.EConst (dummy_pos, JS.Syntax.CUndefined))

end

module Parsers =
struct

  open LJS

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
    let eseq ljs1 ljs2 = match ljs1, ljs2 with
    | FineLJS e1, FineLJS e2 -> FineLJS (LambdaJS.Syntax.ESeq (dummy_pos, e1, e2))
    | _, _ -> let e1 = raw ljs1 and e2 = raw ljs2 in
      RawLJS (LambdaJS.Syntax.ESeq (dummy_pos, e1, e2))
    in
    match code_type with
    | Inputs.JS ->
	let from_js js =
	  js
          |> JS.Interm.from_javascript
          |> LambdaJS.Desugar.ds_top
	  |> (fun rawljs -> if !Options.opt_desugar then
		FineLJS (LambdaJS.Desugar.desugar rawljs)
	      else
		RawLJS rawljs)
	  |> eseq prev_ljs
	in
	try_parse JS.Parser.program JS.Lexer.token lexbuf from_js
    | Inputs.LJS ->
	let from_ljs fineljs =
	  fineljs
          |> Options.if_desugar (LambdaJS.Syntax.raw_of_fine @> LambdaJS.Desugar.desugar)
	  |> (fun x -> FineLJS x)
	  |> eseq prev_ljs
	in
	try_parse LambdaJS.Parser.prog LambdaJS.Lexer.token lexbuf from_ljs
    | Inputs.Env ->
	let tp env = try_parse LambdaJS.Parser.env LambdaJS.Lexer.token lexbuf env in
	match prev_ljs with
	| FineLJS e -> tp (fun env -> FineLJS (env e))
	| RawLJS e -> tp (fun env -> RawLJS (env e))

  let from_inputs input_list =
    List.fold_right from_input input_list empty_ljs

end


let main () =
  Options.arg_parse ();
  if !Options.inputs = [] then
    Options.error_usage "No input";
  if !Options.opt_desugar && List.for_all (function (Inputs.Env, _) -> false | _ -> true) !Options.inputs then
    warning "Desugaring without environment";
  let ljs = Parsers.from_inputs (!Options.inputs) in
  if !Options.opt_pretty then begin
    LambdaJS.Pretty.exp (LJS.raw ljs) Prelude.Format.std_formatter;
    print_newline ();
  end;
  if !Options.opt_features then begin
    let m = FeaturesList.of_exp (LJS.raw ljs) in
    print_endline (FeaturesList.Pretty.string_of_map ~sort_max:true m);
  end;
  if !Options.opt_eval then begin
    let _ = LambdaJS.Eval.eval_expr (LJS.fine ljs) in
    print_newline ();
  end;
  if !Options.opt_xeval then
    let _ = XEval.xeval (LJS.fine ljs) SymbolicState.empty_sstate in
    ();
    ()

let _ =
  main ()
