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
  let generic_opt_io fopen opt name filename = match !opt with
  | Some (fname, _) -> failwith (sprintf "Trying to %s file \"%s\", but already set to \"%s\"" name filename fname)
  | None ->
      let ch = try fopen filename with
      | Sys_error err -> failwith (sprintf "Unable to %s file \"%s\": %s" name filename err)
      in
      opt := Some (filename, ch)
  let generic_opt_out opt name filename = generic_opt_io open_out opt (name ^ " to") filename
  let generic_opt_out_bin opt name filename = generic_opt_io open_out_bin opt (name ^ " to") filename
  let generic_opt_in opt name filename = generic_opt_io open_in opt (name ^ " from") filename
  let generic_opt_in_bin opt name filename = generic_opt_io open_in_bin opt (name ^ " from") filename


  let _get_ctx : (unit -> Z3.context) ref = ref (fun () -> assert false)
  let smt_trace filename =
    if not (Z3.trace_to_file (!_get_ctx ()) filename) then
      failwith (sprintf "Unable to set SMT trace to file \"%s\"" filename)


  let opt_smt_log = ref None
  (* let opt_smt_log = ref Some ("z3.log", open_out "z3.log") *)
  let smt_log = generic_opt_out opt_smt_log "set SMT log"

  let opt_nb_paths = ref None
  let set_nb_paths i =
    if i < 0 then
      failwith "-nb-paths argument should be a non-negative integer";
    opt_nb_paths := Some i

  let opt_save_set = ref None
  let set_save_set = generic_opt_out_bin opt_save_set "save states set"

  let opt_load_set = ref None
  let set_load_set = generic_opt_in_bin opt_load_set "load states set"
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
let opt_interactive = ref false
let opt_model = ref true
let opt_pretty = ref false
let opt_smt = ref true
let opt_symbols = ref true
let opt_xeval = ref true

let opt_assertions = opt_assumptions
let opt_pathcondition = ref true
let opt_err_unbound_id_env = ref false


let boolspeclist =
  [
    "assumptions", opt_assumptions, "display assumptions";
    "backtrace", opt_backtrace, "record backtrace";
    "eval", opt_eval, "evaluate code";
    "features", opt_features, "list used features";
    "fatal", opt_fatal, "fatal errors";
    "interactive", opt_interactive, "interactive mode";
    "model", opt_model, "SMT model";
    "pretty", opt_pretty, "pretty print code";
    "smt", opt_smt, "SMT solver";
    "symb", opt_symbols, "symbols in symbolic evaluation";
    "xeval", opt_xeval, "symbolic evaluation";
  ]


let arg_speclist =
  let speclist =
    [
      "-js", Arg.String (add_file inputs JS), "<file> Load <file> as JavaScript";
      "-ljs", Arg.String (add_file inputs LJS), "<file> Load <file> as LambaJS-ES5";
      "-env", Arg.String (add_file inputs Env), "<file> Load <file> as environment (LambdaJS.ES5)";
      "-nb-paths", Arg.Int set_nb_paths, "<integer> Will stop after the given number of paths";
      "-save-set", Arg.String set_save_set, "<file> Save states set to a file (to be loaded with -load-set)";
      "-load-set", Arg.String set_load_set, "<file> Load a states set from a file (previously saved with -save-set)";
      "-smt-log", Arg.String smt_log, "<file> Enable SMT log to a file (won't include SMT env)";
      "-smt-trace", Arg.String smt_trace, "<file> Enable SMT trace messages to a file (won't include SMT env)";
    ]
  in
  let turn l (name, r, meaning) =
    ("-" ^ name, Arg.Set r, " Turn on " ^ meaning ^ (if !r then " (default)" else ""))
    ::("-no-" ^ name, Arg.Clear r, " Turn off " ^ meaning ^ (if !r then "" else " (default)"))
    ::l
  in
  Arg.align (List.sort Pervasives.compare (List.fold_left turn speclist boolspeclist))

let arg_usage = sprintf "Usage: %s [options] [ <file> ... | -load-set <file> ]" (Filename.basename Sys.executable_name)

let arg_parse () = Arg.parse arg_speclist (add_any_file inputs) arg_usage

let error_usage errmsg =
  Arg.usage arg_speclist (errmsg ^ "\n\n" ^ arg_usage);
  prerr_endline "";
  prerr_endline "Option -load-set cannot be used with options -no-xeval, -pretty, -features, -eval or with input files.";
  prerr_endline "Option -save-set cannot be used with options -no-xeval or -no-symb, and automatically turns off -model.";
  exit 1

let check_print_backtrace () = !opt_backtrace
