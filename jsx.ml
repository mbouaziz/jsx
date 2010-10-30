open MyPervasives


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
    let open Options.Inputs in
    let fname, lexbuf = match input_type with
    | File fname -> fname, Lexing.from_channel (open_in fname)
    | InChannel (fname, cin) -> fname, Lexing.from_channel cin
    | String (fname, s) -> fname, Lexing.from_string s
    in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = fname };
    let eseq ljs1 ljs2 =
      LambdaJS.Syntax.ESeq (LambdaJS.Prelude.dummy_pos, ljs1, ljs2)
    in
    match code_type with
    | JS -> try_parse JS.Parser.program JS.Lexer.token lexbuf (JS.Interm.from_javascript @> LambdaJS.Desugar.ds_top @> eseq prev_ljs)
    | LJS -> try_parse LambdaJS.Parser.prog LambdaJS.Lexer.token lexbuf (LambdaJS.Syntax.raw_of_fine @> eseq prev_ljs)
    | Env -> try_parse LambdaJS.Parser.env LambdaJS.Lexer.token lexbuf ((|>) prev_ljs)

  let from_inputs input_list =
    LambdaJS.Syntax.EConst (LambdaJS.Prelude.dummy_pos, JS.Syntax.CUndefined)
    |> List.fold_right from_input input_list

end


let main () =
  Options.arg_parse ();
  if !Options.inputs = [] then
    Options.error_usage "No input";
  if List.for_all (function (Options.Inputs.Env, _) -> false | _ -> true) !Options.inputs then
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
