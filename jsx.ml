open MyPervasives


module Parsers =
struct

  let try_parse parse lexe lexbuf f =
    let curpos lexbuf =
      pretty_position (lexbuf.Lexing.lex_curr_p, lexbuf.Lexing.lex_curr_p)
    in
    let x = try parse lexe lexbuf with
    | Failure "lexing: empty token" ->
	failwith (sprintf "%s\nLexical error" (curpos lexbuf))
    | JS.Parser.Error
    | LambdaJS.Parser.Error ->
        failwith (sprintf "%s\nParse error: unexpected token \"%s\"" (curpos lexbuf) (Lexing.lexeme lexbuf))
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
      LambdaJS.Syntax.( { p = LambdaJS.Prelude.dummy_pos ; e = ESeq (ljs1, ljs2) } )
    in
    match code_type with
    | JS -> try_parse JS.Parser.program JS.Lexer.token lexbuf (JS.Interm.from_javascript @> LambdaJS.Desugar.ds_top @> eseq prev_ljs)
    | LJS -> try_parse LambdaJS.Parser.prog LambdaJS.Lexer.token lexbuf (LambdaJS.Syntax.raw_of_fine @> eseq prev_ljs)
    | Env -> try_parse LambdaJS.Parser.env LambdaJS.Lexer.token lexbuf ((|>) prev_ljs)

  let from_inputs input_list =
    LambdaJS.Syntax.( { p = LambdaJS.Prelude.dummy_pos ; e = EConst JS.Syntax.CUndefined } )
    |> List.fold_right from_input input_list

end


let main () =
  Options.arg_parse ();
  Printexc.record_backtrace !Options.opt_backtrace;
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
  if !Options.opt_xeval then begin
    let set = XEval.xeval fine_ljs SymbolicState.SState.first in
    if !Options.opt_symbols then
      let print_state () s =
	print_endline (SymbolicState.ToString.state s);
	print_endline "";
	if !Options.opt_interactive then begin
	  let rec read_interaction () =
	    print_string "[N]ext(default)/[A]ll/[M]odel/[S]hort model/Reprint [P]ath/[Q]uit ? ";
	    flush stdout;
	    let ans = String.lowercase (read_line ()) in
	    if ans = "" || ans = "n" then
	      ()
	    else if ans = "a" then begin
	      Options.opt_interactive := false;
	      ()
	    end else if ans = "m" then begin
	      print_endline (SymbolicState.ToString.model s);
	      read_interaction ()
	    end else if ans = "s" then begin
	      print_endline (SymbolicState.ToString.short_model s);
	      read_interaction ()
	    end else if ans = "p" then begin
	      print_endline (SymbolicState.ToString.state s);
read_interaction ()
	    end else if ans = "q" then
	      exit 1
	    else
	      read_interaction ()
	  in
	  read_interaction ();
	end;
      in
      SymbolicState.SState.fold print_state () set
    else if SymbolicState.SState.is_empty set then
      failwith "No state"
    else match SymbolicState.SState.get_singleton set with
    | None -> failwith "Several states"
    | Some s -> let io, exn_opt = SymbolicState.ToString.nosymb_state s in
      print_endline io;
      begin match exn_opt with
      | None -> ()
      | Some exn ->
	  print_endline exn;
	  if !Options.opt_fatal then
	    exit 1
      end
  end

let _ = run_under_backtrace main Options.check_print_backtrace
