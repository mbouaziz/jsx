
open MyPervasives
open SMTLib2Syntax

type func_decl = Z3.func_decl
type macro = Z3.ast array -> Z3.ast

type func =
  | FuncDecl of func_decl
  | Macro of macro
  | MacroConst of Z3.ast

type loaded_env = {
  context : Z3.context ;
  sorts : Z3.sort StringMmap.t ;
  funs : func StringMmap.t ;
}

let empty_env ctx = {
  context = ctx ;
  sorts = StringMmap.empty ;
  funs = StringMmap.empty ;
}

let env_filename = "env.smt2"

let _log lazy_v = match !Options.OtherOptions.opt_smt_log with
| None -> ()
| Some (_, och) -> output_string och (Lazy.force lazy_v)

module Helpers =
struct
  let ast_of_decimal ctx h l =
    if String.Numeric.is_zero l then
      Z3.mk_numeral ctx h (Z3.mk_real_sort ctx)
    else
      let bi_h = Big_int.big_int_of_string h in
      let sh = "1" ^ (String.make (String.length l) '0') in
      let bi_sh = Big_int.big_int_of_string sh in
      let bi_l = Big_int.big_int_of_string l in
      let bi = Big_int.add_big_int bi_l (Big_int.mult_big_int bi_h bi_sh) in
      let frac = Big_int.simplify_fraction (bi, bi_sh) in
      if Big_int.is_int_fraction frac then
	let h, l = Big_int.int_of_fraction frac in
	Z3.mk_real ctx h l
      else
	failwith (sprintf "Don't know how to represent decimal \"%s.%s\" in Z3" h l)
end

module LoadSMTEnv :
sig

  val load : loaded_env -> loaded_env

end =
struct
  let string_of_index = function
    | INumeral s -> s
    | ISymbol s -> s

  let string_of_id = function
    | s, [] -> s
    | s, l -> sprintf "%s[%s]" s (String.concat ":" (List.map string_of_index l))

  let push_func_decl symb f env = { env with funs = StringMmap.push symb (FuncDecl f) env.funs }
  let push_macro symb f env = { env with funs = StringMmap.push symb (Macro f) env.funs }
  let push_macro_const symb ast env = { env with funs = StringMmap.push symb (MacroConst ast) env.funs }
  let pop_fun symb env = { env with funs = StringMmap.
pop symb env.funs }

  (* X_of_Y means X is a Z3 thing and Y is an SMT-LIB2 thing *)

  let symbol_of_symbol env symbol = Z3.mk_string_symbol env.context symbol

  let symbol_of_id env (symbol, idx_list) =
    assert (idx_list = []); (* NYI or never ? *)
    symbol_of_symbol env symbol

  let int_of_numeral num = int_of_string num (* TODO overflow check *)

  let rec sort_of_sort env = function
    | ("Bool", []), [] -> Z3.mk_bool_sort env.context
    | ("Int", []), [] -> Z3.mk_int_sort env.context
    | ("Real", []), [] -> Z3.mk_real_sort env.context
    | ("BitVec", [INumeral num_size]), [] -> Z3.mk_bv_sort env.context (int_of_numeral num_size)
    | ("Array", []), [s1; s2] ->
	let sort1 = sort_of_sort env s1 in
	let sort2 = sort_of_sort env s2 in
	Z3.mk_array_sort env.context sort1 sort2
    | (symb, []), [] ->
	begin match StringMmap.find_opt symb env.sorts with
	| Some sort -> sort
	| None -> failwith (sprintf "Unknown sort \"%s\"" symb)
	end
    | (symb, _), l -> failwith (sprintf "Unknown sort \"%s\" of arity %d" symb (List.length l))

  let ast_of_constant env = function
    | Numeral num -> Z3.mk_numeral env.context num (Z3.mk_int_sort env.context)
    | Decimal (h, l) -> Helpers.ast_of_decimal env.context h l
    | Hexadecimal _
    | Binary _
    | String _ -> assert false (* don't know what to do with them *)

  let is_bv_const str = (String.left str 2 = "bv") && (String.Numeric.is_numeric (String.after str 2))
  let get_bv_const str = String.after str 2

  let is_bvstr_const str = String.left str 6 = "bvstr:"
  let get_bvstr_const str =
    let bi = String.to_big_int (String.after str 6) in
    Big_int.string_of_big_int bi, Big_int.count_bits bi

  let rec ast_of_app_qual_id env (id, sort_opt) term_list =
    assert (sort_opt = None);
    let ast_list = List.map (ast_of_term env) term_list in
    match id, ast_list with
    | ("true", []), [] -> Z3.mk_true env.context
    | ("false", []), [] -> Z3.mk_false env.context
    | ("=", []), [x; y] -> Z3.mk_eq env.context x y
    | ("distinct", []), ast_list -> Z3.mk_distinct env.context (Array.of_list ast_list)
    | ("not", []), [x] -> Z3.mk_not env.context x
    | ("if", []), [i;t;e]
    | ("ite", []), [i;t;e] -> Z3.mk_ite env.context i t e
    | ("<=>", []), [x;y]
    | ("iff", []), [x;y] -> Z3.mk_iff env.context x y
    | ("=>", []), [x;y]
    | ("implies", []), [x;y] -> Z3.mk_implies env.context x y
    | ("xor", []), [x;y] -> Z3.mk_xor env.context x y
    | ("and", []), ast_list -> Z3.mk_and env.context (Array.of_list ast_list)
    | ("or", []), ast_list -> Z3.mk_or env.context (Array.of_list ast_list)
    | ("+", []), ast_list
    | ("add", []), ast_list -> Z3.mk_add env.context (Array.of_list ast_list)
    | ("*", []), ast_list
    | ("mul", []), ast_list -> Z3.mk_mul env.context (Array.of_list ast_list)
    | ("-", []), ast_list
    | ("sub", []), ast_list -> Z3.mk_sub env.context (Array.of_list ast_list)
    | ("~", []), [x] -> Z3.mk_sub env.context [| x |]
    | ("/", []), [x;y]
    | ("div", []), [x;y] -> Z3.mk_div env.context x y
    | ("%", []), [x;y]
    | ("mod", []), [x;y] -> Z3.mk_mod env.context x y
    | ("rem", []), [x;y] -> Z3.mk_rem env.context x y
    | ("<", []), [x;y]
    | ("lt", []), [x;y] -> Z3.mk_lt env.context x y
    | ("<=", []), [x;y]
    | ("le", []), [x;y] -> Z3.mk_le env.context x y
    | (">", []), [x;y]
    | ("gt", []), [x;y] -> Z3.mk_gt env.context x y
    | (">=", []), [x;y]
    | ("ge", []), [x;y] -> Z3.mk_ge env.context x y
    | ("to_real", []), [x] -> Z3.mk_int2real env.context x
    | ("real2int", []), [x] -> Z3.mk_real2int env.context x
    | ("is_int", []), [x] -> Z3.mk_is_int env.context x
    | ("bvnot", []), [x] -> Z3.mk_bvnot env.context x
    | ("bvredand", []), [x] -> Z3.mk_bvredand env.context x
    | ("bvredor", []), [x] -> Z3.mk_bvredor env.context x
    | ("bvand", []), [x;y] -> Z3.mk_bvand env.context x y
    | ("bvor", []), [x;y] -> Z3.mk_bvor env.context x y
    | ("bvxor", []), [x;y] -> Z3.mk_bvxor env.context x y
    | ("bvnand", []), [x;y] -> Z3.mk_bvnand env.context x y
    | ("bvnor", []), [x;y] -> Z3.mk_bvnor env.context x y
    | ("bvxnor", []), [x;y] -> Z3.mk_bvxnor env.context x y
    | ("bvneg", []), [x] -> Z3.mk_bvneg env.context x
    | ("bvadd", []), [x;y] -> Z3.mk_bvadd env.context x y
    | ("bvsub", []), [x;y] -> Z3.mk_bvsub env.context x y
    | ("bvmul", []), [x;y] -> Z3.mk_bvmul env.context x y
    | ("bvudiv", []), [x;y] -> Z3.mk_bvudiv env.context x y
    | ("bvsdiv", []), [x;y] -> Z3.mk_bvsdiv env.context x y
    | ("bvurem", []), [x;y] -> Z3.mk_bvurem env.context x y
    | ("bvsrem", []), [x;y] -> Z3.mk_bvsrem env.context x y
    | ("bvsmod", []), [x;y] -> Z3.mk_bvsmod env.context x y
    | ("bvult", []), [x;y] -> Z3.mk_bvult env.context x y
    | ("bvslt", []), [x;y] -> Z3.mk_bvslt env.context x y
    | ("bvule", []), [x;y] -> Z3.mk_bvule env.context x y
    | ("bvsle", []), [x;y] -> Z3.mk_bvsle env.context x y
    | ("bvuge", []), [x;y] -> Z3.mk_bvuge env.context x y
    | ("bvsge", []), [x;y] -> Z3.mk_bvsge env.context x y
    | ("bvugt", []), [x;y] -> Z3.mk_bvugt env.context x y
    | ("bvsgt", []), [x;y] -> Z3.mk_bvsgt env.context x y
    | ("concat", []), [x;y] -> Z3.mk_concat env.context x y
    | ("extract", [INumeral h; INumeral l]), [x] -> Z3.mk_extract env.context (int_of_string h) (int_of_string l) x
    | ("sign_ext", [INumeral size]), [x] -> Z3.mk_sign_ext env.context (int_of_string size) x
    | ("zero_ext", [INumeral size]), [x] -> Z3.mk_zero_ext env.context (int_of_string size) x
    | ("repeat", [INumeral size]), [x] -> Z3.mk_repeat env.context (int_of_string size) x
    | ("bvshl", []), [x;y] -> Z3.mk_bvshl env.context x y
    | ("bvlshr", []), [x;y] -> Z3.mk_bvlshr env.context x y
    | ("bvashr", []), [x;y] -> Z3.mk_bvashr env.context x y
    | ("rotate_left", [INumeral n]), [x] -> Z3.mk_rotate_left env.context (int_of_string n) x
    | ("rotate_right", [INumeral n]), [x] -> Z3.mk_rotate_right env.context (int_of_string n) x
    (* | ("ext_rotate_left", []), [x;y] -> Z3.mk_ext_rotate_left env.context x y *)
    (* | ("ext_rotate_right", []), [x;y] -> Z3.mk_ext_rotate_right env.context x y *)
    | ("int2bv", [INumeral num]), [x] -> Z3.mk_int2bv env.context (int_of_string num) x
    | ("bv2int", []), [x] -> Z3.mk_bv2int env.context x false
    | ("bv2int", [ISymbol "Int"]), [x] -> Z3.mk_bv2int env.context x true
	(* TODO *)
    | (symb, [INumeral num_bv_size]), [] when is_bv_const symb -> (* bit-vectors initializers, like bv0[32] *)
	Z3.mk_numeral env.context (get_bv_const symb) (Z3.mk_bv_sort env.context (int_of_string num_bv_size))
	(* Extensions *)
    | (symb, [INumeral num_bv_size]), [] when is_bvstr_const symb ->
	let bv_size = int_of_string num_bv_size in
	let str_const, nb_bits = get_bvstr_const symb in
	assert (bv_size >= nb_bits);
	Z3.mk_numeral env.context str_const (Z3.mk_bv_sort env.context bv_size)
    (* | ("Int", [num]), [] -> Z3.mk_numeral env.context num (Z3.mk_int_sort env.context) *)
    (* | ("Real", [num]), [] -> Z3.mk_numeral env.context num (Z3.mk_real_sort env.context) *)
	(* User-defined *)
    | (symb, idx_list), ast_list ->
	assert (idx_list = []);
	match StringMmap.find_opt symb env.funs with
	| Some (FuncDecl f) -> Z3.mk_app env.context f (Array.of_list ast_list)
	| Some (MacroConst ast) -> assert (ast_list = []); ast
	| Some (Macro f) -> f (Array.of_list ast_list)
	| None -> failwith (sprintf "Application of unknown function \"%s\" of arity %d" (string_of_id (symb, idx_list)) (List.length ast_list))

  and ast_of_quant env quant sv_list term =
    let w = 1 in (* ?? *)
    let pat_array = [||] in
    let symbol_list, sort_list = List.split sv_list in
    let sort_list = List.map (sort_of_sort env) sort_list in
    let symb_list = List.map (symbol_of_symbol env) symbol_list in
    let env = List.fold_left3 (fun env symbol symb sort -> push_func_decl symbol (Z3.mk_func_decl env.context symb [||] sort) env) env symbol_list symb_list sort_list in
    let ast = ast_of_term env term in
    let env = List.fold_leftr pop_fun symbol_list env in
    let f = match quant with
    | ForAll -> Z3.mk_forall
    | Exists -> Z3.mk_exists
    in
    f env.context w pat_array (Array.of_list sort_list) (Array.of_list symb_list) ast

  and ast_of_term env = function
    | TConstant c -> ast_of_constant env c
    | TAppQualId (qual_id, term_list) -> ast_of_app_qual_id env qual_id term_list
    | TLet (vb_list, term) -> ast_of_let env vb_list term
    | TQuant (quant, sv_list, term) -> ast_of_quant env quant sv_list term
    | TExcl (term, attr_list) -> ast_of_excl env term attr_list

  and ast_of_let env vb_list term = assert false (* NYI *)
  and ast_of_excl env term attr_list = assert false (* NYI *)

  let z3_sort_null = (Obj.magic 0 : Z3.sort)

  let sort2_of_sort rec_sorts env sort = match sort with
  | (symb, []), [] ->
      begin match StringMap.find_opt symb rec_sorts with
      | Some idx -> z3_sort_null, idx
      | None -> (sort_of_sort env sort), 0
      end
  | sort -> (sort_of_sort env sort), 0

  let add_shorthand_sort env id sort =
    match id with
    | symb, [] -> { env with sorts = StringMmap.push symb sort env.sorts }
    | _ -> assert false

  let define_shorthand_sort env (id, sort) =
    add_shorthand_sort env id (sort_of_sort env sort)

  let define_sorts env shsl = List.fold_left define_shorthand_sort env shsl

  let constr_of_constr rec_sorts env ((symb_constr, num_list), fields_list) =
    let symb_is = "is_" ^ symb_constr in
    let symbol_constr = symbol_of_id env (symb_constr, num_list) in
    let symbol_is = symbol_of_id env (symb_is, num_list) in
    let fields_list, sort_list = List.split fields_list in
    let fields_array = Array.of_list fields_list in
    let symbol_fields = Array.map (symbol_of_id env) fields_array in
    let sort_list, idx_list = List.split (List.map (sort2_of_sort rec_sorts env) sort_list) in
    let constructor = Z3.mk_constructor env.context symbol_constr symbol_is
      symbol_fields (Array.of_list sort_list) (Array.of_list idx_list) in
    (* let f_constr, f_is, f_fields = Z3.query_constructor env.context constructor 10 (\* (Array.length fields_array) *\) in *)
    (* let env = push_func_decl symb_constr f_constr env in *)
    (* let env = push_func_decl symb_is f_is env in *)
    (* let env = Array.fold_left2 push_func_decl env (Array.map fst fields_array) f_fields in *)
    env, (constructor, (symb_constr, symb_is, (Array.map fst fields_array)))

  let constrl_of_constrl rec_sorts env constrl =
    let env, constrl_plus = List.fold_map (constr_of_constr rec_sorts) env constrl in
    let constrl, plus = List.split constrl_plus in
    env, ((Z3.mk_constructor_list env.context (Array.of_list constrl)), plus)

  let rec_sorts_of_id_arr id_arr =
    let f m i (symb, num_list) = assert (num_list = []); StringMap.add symb i m in
    Array.fold_left_i f StringMap.empty id_arr

  let fill_funs plus_arr sort_arr env =
    let aux env plus sort =
      let aux' env (symb_constr, symb_is, symb_fields)
	  { Z3.constructor = f_constr ;
	    Z3.recognizer = f_is ;
	    Z3.accessors = f_fields } =
	env
        |> push_func_decl symb_constr f_constr
	|> push_func_decl symb_is f_is
	|> Array.fold_leftr2 push_func_decl symb_fields f_fields
      in
      let dtcra = Z3.get_datatype_sort env.context sort in
      Array.fold_left2 aux' env (Array.of_list plus) dtcra
    in
    Array.fold_left2 aux env plus_arr sort_arr

  let declare_datatypes env dtl =
    let idl, constrll = List.split dtl in
    let id_arr = Array.of_list idl in
    let symb_arr = Array.map (symbol_of_id env) id_arr in
    let rec_sorts = rec_sorts_of_id_arr id_arr in
    let constrl_arr = Array.of_list constrll in
    let env, constrl_plus_arr = Array.fold_map (constrl_of_constrl rec_sorts) env constrl_arr in
    let constrl_arr, plus_arr = Array.split constrl_plus_arr in
    let sort_arr, constrl_arr = Z3.mk_datatypes env.context symb_arr constrl_arr in
    let env = fill_funs plus_arr sort_arr env in
    List.fold_left2 add_shorthand_sort env idl (Array.to_list sort_arr)

  let do_assert env term =
    let ast = ast_of_term env term in
    (* print_endline (sprintf "ENV<<%s>>" (Z3.ast_to_string env.context ast)); *)
    _log (lazy (sprintf "(assert\n  %s)\n" (String.interline "  " (Z3.ast_to_string env.context ast))));
    Z3.assert_cnstr env.context ast;
    env

  let declare_fun env (symbol, sort_list, sort) =
    let symb = symbol_of_symbol env symbol in
    let sort_list = List.map (sort_of_sort env) sort_list in
    let sort = sort_of_sort env sort in
    let f = Z3.mk_func_decl env.context symb (Array.of_list sort_list) sort in
    _log (lazy (sprintf "%s\n" (Z3.func_decl_to_string env.context f)));
    push_func_decl symbol f env

  module ToString =
  struct
    let sorted_var env (symb, sort) =
      sprintf "(%s %s)" symb (sort_of_sort env sort |> Z3.sort_to_string env.context)
      
    let sorted_var_list env svl =
      svl
      |> List.map (sorted_var env)
      |> String.concat " "
  end

  let define env (symb, sorted_var_list, term) =
    if sorted_var_list = [] then
      let ast = ast_of_term env term in
      _log (lazy (sprintf "(define %s %s)\n" symb (Z3.ast_to_string env.context ast)));
      push_macro_const symb ast env
    else
      (* todo: check bound var at creation time *)
      let symb_arr = Array.of_list (List.map fst sorted_var_list) in
      let arity = Array.length symb_arr in
      let f ast_arr =
	if Array.length ast_arr <> arity then
	  failwith (sprintf "Macro %s called with %d arguments instead of %d\n" symb (Array.length ast_arr) arity);
	let env = Array.fold_leftr2 push_macro_const symb_arr ast_arr env in
        ast_of_term env term
      in
      _log (lazy (
	      let ast_list = List.map (fun (symb, sort) -> Z3.mk_fresh_const env.context symb (sort_of_sort env sort)) sorted_var_list in
	      let str_svl =
		let svl =
		  let symb_list = List.map (Z3.ast_to_string env.context) ast_list in
		  let sort_list = List.map snd sorted_var_list in
		  List.combine symb_list sort_list in
		ToString.sorted_var_list env svl in
	      let str_term =
		let symb_list = List.map fst sorted_var_list in
		let env = List.fold_leftr2 push_macro_const symb_list ast_list env in
		ast_of_term env term
	        |> Z3.ast_to_string env.context
		|> String.interline "  "
	      in
	      sprintf "(define (%s %s)\n  %s)\n" symb str_svl str_term));
      push_macro symb f env

  (* transforms
     (define-fun f ((x1 s1) ... (xN sN)) s t)
     into
     (declare-fun f (s1 ... sN) s)
     (assert (forall (x1 s1) ... (xN sN) (= (f x1 ... xN) t)))
  *)
  let define_fun env (symb, sorted_var_list, sort, term) =
    let sort_list = List.map snd sorted_var_list in
    let env = declare_fun env (symb, sort_list, sort) in
    let ast_eq = SMTLib2Syntax.Mk.(
      Term.app_qual_id dummy_pos (("=", []), None) [
	term;
	(Term.app_qual_id dummy_pos ((symb, []), None)
	   (List.map (fun (s,_)->Term.app_qual_id dummy_pos ((s,[]),None) []) sorted_var_list)
	)] )
    in
    let ast =
      if sorted_var_list = [] then
	ast_eq
      else
	SMTLib2Syntax.Mk.(Term.for_all dummy_pos sorted_var_list ast_eq)
    in
    do_assert env ast

  let of_command env = function
    | Assert t -> do_assert env t
    | DeclareFun f -> declare_fun env f
    | Define f -> define env f
    | DefineFun f -> define_fun env f
    | DefineSorts l -> define_sorts env l
    | DeclareDatatypes l -> declare_datatypes env l
    | _ -> assert false (* NYI *)

  let of_script env script = List.fold_left of_command env script

  let load env =
    let open Lexing in
    let ich = open_in env_filename in
    let lexbuf = from_channel ich in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = env_filename };
    let smt2ast = try SMTLib2Parser.script SMTLib2Lexer.token lexbuf with
    | Failure "lexing: empty token"
    | SMTLib2Parser.Error -> failwith (sprintf "%s\nParse error: unexpected token \"%s\"" (pretty_position (lexeme_start_p lexbuf, lexeme_end_p lexbuf)) (lexeme lexbuf))
    in
    close_in ich;
    of_script env smt2ast

end
