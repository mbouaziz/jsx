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


let interactive_loop def opts =
  Sys.catch_break false;
  let prompt =
    opts
    |> List.map (fun (k, (t, _)) -> if k = def then t ^ "(default)" else t)
    |> String.concat "/"
    |> sprintf "%s ? "
  in
  let rec loop () =
    print_string prompt;
    flush stdout;
    let ans = String.lowercase (read_line ()) in
    let ans = if ans = "" then def else ans in
    match List.assoc_opt ans opts with
    | None -> loop ()
    | Some (_, a) -> if a () then loop ()
  in
  loop ();
  if not !Options.opt_interactive then
    Sys.catch_break true


let main () =
  Options.arg_parse ();
  Printexc.record_backtrace !Options.opt_backtrace;
  if !Options.OtherOptions.opt_load_set <> None then begin
    if not !Options.opt_xeval then
      Options.error_usage "Option -load-set cannot be used with -no-xeval";
    if !Options.inputs <> [] then
      Options.error_usage "Option -load-set cannot be used with other input files";
    if !Options.opt_pretty then
      Options.error_usage "Option -load-set cannot be used with -pretty";
    if !Options.opt_features then
      Options.error_usage "Option -load-set cannot be used with -features";
    if !Options.opt_eval then
      Options.error_usage "Option -load-set cannot be used with -eval";
  end;
  if !Options.OtherOptions.opt_save_set <> None then begin
    if not !Options.opt_xeval then
      Options.error_usage "Option -save-set cannot be used with -no-xeval";
    if not !Options.opt_symbols then
      Options.error_usage "Option -save-set cannot be used with -no-symb";
    (* Because a model contains an abstract type which cannot be marshalled *)
    Options.opt_model := false;
  end;
  let get_fine_ljs =
    let _fine_ljs = ref None in
    fun () -> match !_fine_ljs with
    | Some fine_ljs -> fine_ljs
    | None ->
	if !Options.inputs = [] then
	  Options.error_usage "No input";
	if List.for_all (function (Options.Inputs.Env, _) -> false | _ -> true) !Options.inputs then
	  warning "Desugaring without environment";
	let raw_ljs = Parsers.from_inputs (!Options.inputs) in
	let fine_ljs = LambdaJS.Desugar.desugar raw_ljs in
	_fine_ljs := Some fine_ljs;
	fine_ljs
  in
  let get_raw_ljs () =
    get_fine_ljs () |> LambdaJS.Syntax.raw_of_fine
  in
  if !Options.opt_pretty then begin
    LambdaJS.Pretty.opt_print_args := true;
    LambdaJS.Pretty.exp (get_raw_ljs ()) Prelude.Format.std_formatter;
    LambdaJS.Pretty.opt_print_args := false;
    print_newline ();
  end;
  if !Options.opt_features then begin
    let m = FeaturesList.of_exp (get_raw_ljs ()) in
    print_endline (FeaturesList.Pretty.string_of_map ~sort_max:true m);
  end;
  if !Options.opt_eval then begin
    let _ = LambdaJS.Eval.eval_expr (get_fine_ljs ()) in
    print_newline ();
  end;
  if !Options.opt_xeval then begin
    let set_opt =
      (* idea: an option to chain xeval + load-set *)
      match !Options.OtherOptions.opt_load_set with
      | None ->
	  let fine_ljs = get_fine_ljs () in
	  Some (XEval.xeval fine_ljs SymbolicState.SState.first)
      | Some (_, ich) ->
	  let set_opt = SymbolicState.SState.marshal_in ich in
	  close_in ich;
	  set_opt
    in
    if !Options.opt_symbols then begin
      let of_a_set set =
	let s = SymbolicState.SState.get_first set in
	let get_next_opt = SymbolicState.SState.get_next set in

	print_endline (SymbolicState.ToString.state s);
	print_endline "";

	if !Options.opt_interactive then begin
	  let do_all () = Options.opt_interactive := false; false in
	  let do_model () = print_endline (SymbolicState.ToString.model s); true in
	  let do_short_model () = print_endline (SymbolicState.ToString.short_model s); true in
	  let do_print_path () = print_endline (SymbolicState.ToString.state s); true in
	  let do_quit () = exit 1 in
	  let do_next () = false in
	  let opts = [
	    "p", ("Reprint [P]ath", do_print_path);
	    "q", ("[Q]uit", do_quit);
	  ] in
	  let opts =
	    if !Options.opt_model then ("m", ("[M]odel", do_model))::("s", ("[S]hort model", do_short_model))::opts
	    else opts in
	  let def, opts =
	    if get_next_opt = None then "q", opts
	    else "n", ("n", ("[N]ext", do_next))::("a", ("[A]ll", do_all))::opts in
	  interactive_loop def opts
	end;

	match get_next_opt with
	| None -> None
	| Some f -> Some (f ())
      in
      let continue = match !Options.OtherOptions.opt_nb_paths with
      | None -> ref true
      | Some nb_paths -> ref (nb_paths > 0)
      in
      let cur_set_opt = ref set_opt in
      let cur_path = ref 0 in
      if not !Options.opt_interactive then
	Sys.catch_break true;
      while !continue do
	match !cur_set_opt with
	| None -> continue := false
	| Some set ->
	    try
	      cur_set_opt := of_a_set set;
	      incr cur_path;
	      match !Options.OtherOptions.opt_nb_paths with
	      | Some nb_paths when !cur_path >= nb_paths -> continue := false
	      | _ -> ()
	    with
	      Sys.Break -> Options.opt_interactive := true
      done;
      Sys.catch_break false;
      begin match !Options.OtherOptions.opt_save_set with
      | None -> ()
      | Some (_, och) ->
	  SymbolicState.SState.marshal_out och !cur_set_opt;
	  close_out och
      end;
    end else match set_opt with
    | None -> failwith "Bug? No state"
    | Some set ->
	match SymbolicState.SState.get_singleton set with
	| None -> failwith "Bug? Several states without symbols!"
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
