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

module OtherOptions =
struct

  let _get_ctx : (unit -> Z3.context) ref = ref (fun () -> assert false)

  let smt_trace filename =
    if not (Z3.trace_to_file (!_get_ctx ()) filename) then
      failwith (sprintf "Unable to set SMT trace to file \"%s\"" filename)

end

open Inputs
open OtherOptions

(* inputs *)
let inputs = ref []

(* options and their default values *)
let opt_assumptions = ref false
let opt_backtrace = ref true
let opt_eval = ref false
let opt_fatal = ref false
let opt_features = ref false
let opt_pretty = ref false
let opt_smt = ref true
let opt_symbols = ref true
let opt_xeval = ref true

let opt_err_unbound_id_env = ref false


let boolspeclist =
  [
    "assumptions", opt_assumptions, "display assumptions";
    "backtrace", opt_backtrace, "record backtrace";
    "eval", opt_eval, "evaluate code";
    "features", opt_features, "list used features";
    "fatal", opt_fatal, "fatal errors";
    "pretty", opt_pretty, "pretty print code";
    "smt", opt_smt, "SMT solver";
    "symb", opt_symbols, "symbols in symbolic evaluation";
    "xeval", opt_xeval, "symbolically evaluate code";
  ]


let arg_speclist =
  let speclist =
    [
      "-js", Arg.String (add_file inputs JS), "<file> Load <file> as JavaScript";
      "-ljs", Arg.String (add_file inputs LJS), "<file> Load <file> as LambaJS-ES5";
      "-env", Arg.String (add_file inputs Env), "<file> Load <file> as environment (LambdaJS.ES5)";
      "-smt-trace", Arg.String smt_trace, "<file> Enable SMT trace messages to a file (won't include SMT env)";
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

let check_print_backtrace () = !opt_backtrace
