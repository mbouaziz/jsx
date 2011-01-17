
open MyPervasives
open SMTLib2Syntax

type loaded_env = {
  context : Z3.context ;
  sorts : Z3.sort StringMmap.t ;
  funs : Z3.func_decl StringMmap.t ;
}

let empty_env ctx = {
  context = ctx ;
  sorts = StringMmap.empty ;
  funs = StringMmap.empty ;
}

let env_filename = "env.smt2"

module LoadSMTEnv :
sig

  val load : loaded_env -> loaded_env

end =
struct
  let string_of_id = function
    | s, [] -> s
    | s, l -> sprintf "%s[%s]" s (String.concat ":" l)

  let push_fun env symb f = { env with funs = StringMmap.push symb f env.funs }
  let pop_fun env symb = { env with funs = StringMmap.pop symb env.funs }

  (* X_of_Y means X is a Z3 thing and Y is an SMT-LIB2 thing *)

  let symbol_of_symbol env symbol = Z3.mk_string_symbol env.context symbol

  let symbol_of_id env (symbol, num_list) =
    assert (num_list = []); (* NYI or never ? *)
    symbol_of_symbol env symbol

  let int_of_numeral num = int_of_string num (* TODO overflow check *)

  let rec sort_of_sort env = function
    | ("Bool", []), [] -> Z3.mk_bool_sort env.context
    | ("Int", []), [] -> Z3.mk_int_sort env.context
    | ("Real", []), [] -> Z3.mk_real_sort env.context
    | ("BitVec", [num_size]), [] -> Z3.mk_bv_sort env.context (int_of_numeral num_size)
    | ("Array", []), [s1; s2] ->
	let sort1 = sort_of_sort env s1 in
	let sort2 = sort_of_sort env s2 in
	Z3.mk_array_sort env.context sort1 sort2
    | (symb, []), [] -> StringMmap.find symb env.sorts
    | _, _ -> assert false

  let ast_of_constant env = function
    | Numeral _
    | Decimal _
    | Hexadecimal _
    | Binary _
    | String _ -> assert false (* don't know what to do with them *)

  let is_bv_const str = (String.left str 2 = "bv") && (String.is_numeric (String.after str 2))
  let get_bv_const str = String.after str 2

  let rec ast_of_app_qual_id env (id, sort_opt) term_list =
    assert (sort_opt = None);
    let ast_list = List.map (ast_of_term env) term_list in
    match id, ast_list with
    | ("true", []), [] -> Z3.mk_true env.context
    | ("false", []), [] -> Z3.mk_false env.context
    | ("=", []), [x; y] -> Z3.mk_eq env.context x y
    | ("distinct", []), ast_list -> Z3.mk_distinct env.context (Array.of_list ast_list)
    | ("not", []), [x] -> Z3.mk_not env.context x
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
	(* TODO *)
    | (symb, [num_bv_size]), [] when is_bv_const symb -> (* bit-vectors initializers, like bv0[32] *)
	Z3.mk_numeral env.context (get_bv_const symb) (Z3.mk_bv_sort env.context (int_of_string num_bv_size))
	(* Extensions *)
    | ("Int", [num]), [] -> Z3.mk_numeral env.context num (Z3.mk_int_sort env.context)
    | ("Real", [num]), [] -> Z3.mk_numeral env.context num (Z3.mk_real_sort env.context)
	(* User-defined *)
    | (symb, num_list), ast_list ->
	assert (num_list = []);
	match StringMmap.find_opt symb env.funs with
	| Some f -> Z3.mk_app env.context f (Array.of_list ast_list)
	| None -> failwith (sprintf "Application of unknown function \"%s\" of arity %d" (string_of_id (symb, num_list)) (List.length ast_list))

  and ast_of_quant env quant sv_list term =
    let w = 1 in (* ?? *)
    let pat_array = [||] in
    let symbol_list, sort_list = List.split sv_list in
    let sort_list = List.map (sort_of_sort env) sort_list in
    let symb_list = List.map (symbol_of_symbol env) symbol_list in
    let env = List.fold_left3 (fun env symbol symb sort -> push_fun env symbol (Z3.mk_func_decl env.context symb [||] sort)) env symbol_list symb_list sort_list in
    let ast = ast_of_term env term in
    let env = List.fold_left pop_fun env symbol_list in
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
    (* let env = push_fun env symb_constr f_constr in *)
    (* let env = push_fun env symb_is f_is in *)
    (* let env = Array.fold_left2 push_fun env (Array.map fst fields_array) f_fields in *)
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
	let env = push_fun env symb_constr f_constr in
	let env = push_fun env symb_is f_is in
	let env = Array.fold_left2 push_fun env symb_fields f_fields in
	env
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
    print_endline (sprintf "ENV<<%s>>" (Z3.ast_to_string env.context ast));
    Z3.assert_cnstr env.context ast;
    env

  let declare_fun env (symbol, sort_list, sort) =
    let symb = symbol_of_symbol env symbol in
    let sort_list = List.map (sort_of_sort env) sort_list in
    let sort = sort_of_sort env sort in
    let f = Z3.mk_func_decl env.context symb (Array.of_list sort_list) sort in
    let env = push_fun env symbol f in
    env

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
