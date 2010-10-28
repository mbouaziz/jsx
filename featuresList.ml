
open MyPervasives

module Feature =
struct

  (* JS.Syntax.const *)
  type js_const =
    | FCString
    | FCRegexp
    | FCNum
    | FCInt
    | FCBool
    | FCNull
    | FCUndefined

  type attr = LambdaJS.Syntax.attr

  (* LambdaJS.Syntax.exp *)
  type exp =
    | FEConst of js_const
    | FEId
    | FEObject
    | FEUpdateFieldSurface
    | FEGetFieldSurface
    | FEAttr of attr
    | FESetAttr of attr
    | FEDeleteField
    | FESet
    | FEOp1 of LambdaJS.Syntax.op1
    | FEOp2 of LambdaJS.Syntax.op2
    | FEOp3 of LambdaJS.Syntax.op3
    | FEIf
    | FEApp
    | FESeq
    | FELet
    | FEFix
    | FELabel
    | FEBreak
    | FETryCatch
    | FETryFinally
    | FEThrow
    | FELambda

  type t =
    | FExp of exp
    | FAttr of attr (* in EObject *)

  let compare = Pervasives.compare

end

open Feature

module FeatureMap = Map.Make(Feature)
module FM =
struct
  include FeatureMap

  let _inc v t =
    let n = try find v t with Not_found -> 0 in
    add v (n+1) t

  let inc e t = _inc (FExp e) t

  let inc_attr a t = _inc (FAttr a) t

  (* remove if OCaml >= 3.12.0 *)
  let bindings m = List.rev (fold (fun k v l -> (k, v)::l) m [])

  let merge f m1 m2 =
    let b1 = bindings m1 in
    let b2 = bindings m2 in
    let concatf k o1 o2 l = match f k o1 o2 with
    | None -> l
    | Some v -> (k, v)::l
    in
    let rec aux l1 l2 = match l1, l2 with
      | [], [] -> []
      | (k, v1)::t1, [] -> concatf k (Some v1) None (aux t1 [])
      | [], (k, v2)::t2 -> concatf k None (Some v2) (aux [] t2)
      | (k1, v1)::t1, (k2, v2)::t2 ->
	  match Feature.compare k1 k2 with
	  | 0 -> concatf k1 (Some v1) (Some v2) (aux t1 t2)
	  | x when x < 0 -> concatf k1 (Some v1) None (aux t1 l2)
	  | _ -> concatf k2 None (Some v2) (aux l1 t2)
    in
    List.fold_left (fun m (k, v) -> add k v m) empty (aux b1 b2)
    
end

let empty = FM.empty

module OfJS =
struct

  open JS.Syntax

  let f_of_const = function
    | CString _ -> FCString
    | CRegexp _ -> FCRegexp
    | CNum _ -> FCNum
    | CInt _ -> FCInt
    | CBool _ -> FCBool
    | CNull -> FCNull
    | CUndefined -> FCUndefined

  let of_const c t = FM.inc (FEConst (f_of_const c)) t

end

module OfLambdaJS =
struct

  open LambdaJS.Syntax

  let rec of_exp ljs t =
    match ljs with
    | EConst (_, c) -> OfJS.of_const c t
    | EId _ -> FM.inc FEId t
    | EObject (_, sel, saell) ->
	let of_Xe t (_, e) = of_exp e t in
	let of_ae t (a, e) = t |> FM.inc_attr a |> of_exp e in
	let of_sael t (_, ael) = List.fold_left of_ae t ael in
	let t = FM.inc FEObject t in
	let t = List.fold_left of_Xe t sel in
	let t = List.fold_left of_sael t saell in
	t
    | EUpdateFieldSurface (_, e1, e2, e3, e4) -> t |> FM.inc FEUpdateFieldSurface |> of_explist [e1; e2; e3; e4]
    | EGetFieldSurface (_, e1, e2, e3) -> t |> FM.inc FEGetFieldSurface |> of_explist [e1; e2; e3]
    | EAttr (_, a, e1, e2) -> t |> FM.inc (FEAttr a) |> of_explist [e1; e2]
    | ESetAttr (_, a, e1, e2, e3) -> t |> FM.inc (FESetAttr a) |> of_explist [e1; e2; e3]
    | EDeleteField (_, e1, e2) -> t |> FM.inc FEDeleteField |> of_explist [e1; e2]
    | ESet (_, _, e) -> t |> FM.inc FESet |> of_exp e
    | EOp1 (_, op1, e) -> t |> FM.inc (FEOp1 op1) |> of_exp e
    | EOp2 (_, op2, e1, e2) -> t |> FM.inc (FEOp2 op2) |> of_explist [e1; e2]
    | EOp3 (_, op3, e1, e2, e3) -> t |> FM.inc (FEOp3 op3) |> of_explist [e1; e2; e3]
    | EIf (_, e1, e2, e3) -> t |> FM.inc FEIf |> of_explist [e1; e2; e3]
    | EApp (_, e, el) -> t |> FM.inc FEApp |> of_explist (e::el)
    | ESeq (_, e1, e2) -> t |> FM.inc FESeq |> of_explist [e1; e2]
    | ELet (_, _, e1, e2) -> t |> FM.inc FELet |> of_explist [e1; e2]
    | EFix (_, _, e) -> t |> FM.inc FEFix |> of_exp e
    | ELabel (_, _, e) -> t |> FM.inc FELabel |> of_exp e
    | EBreak (_, _, e) -> t |> FM.inc FEBreak |> of_exp e
    | ETryCatch (_, e1, e2) -> t |> FM.inc FETryCatch |> of_explist [e1; e2]
    | ETryFinally (_, e1, e2) -> t |> FM.inc FETryFinally |> of_explist [e1; e2]
    | EThrow (_, e) -> t |> FM.inc FEThrow |> of_exp e
    | ELambda (_, _, e) -> t |> FM.inc FELambda |> of_exp e

  and of_explist el t = List.fold_left (fun t e -> of_exp e t) t el

end

let of_exp exp = OfLambdaJS.of_exp exp FM.empty

module Pretty =
struct

  open LambdaJS.Syntax

  let char_sep = '.'

  let sep = String.make 1 char_sep

  let of_const = function
    | FCString -> "CString"
    | FCRegexp -> "CRegexp"
    | FCNum -> "CNum"
    | FCInt -> "CInt"
    | FCBool -> "CBool"
    | FCNull -> "CNull"
    | FCUndefined -> "CUndefined"

  let of_attr = function
    | Value -> "Value"
    | Getter -> "Getter"
    | Setter -> "Setter"
    | Config -> "Config"
    | Writable -> "Writable"
    | Enum -> "Enum"

  let of_id id = id

  let of_op1 = function
    | `Op1Prefix id -> "Op1Prefix" ^ sep ^ (of_id id)
    | `Prim1 s -> "Prim1" ^ sep ^ s

  let of_op2 = function
    | `Op2Infix id -> "Op2Infix" ^ sep ^ (of_id id)
    | `Prim2 s -> "Prim2" ^ sep ^ s

  let of_op3 = function
    | `Op3Prefix id -> "Op3Prefix" ^ sep ^ (of_id id)
    | `Prim3 s -> "Prim3" ^ sep ^ s

  let of_exp = function
    | FEConst c -> "EConst" ^ sep ^ (of_const c)
    | FEId -> "EId"
    | FEObject -> "EObject"
    | FEUpdateFieldSurface -> "EUpdateFieldSurface"
    | FEGetFieldSurface -> "EGetFieldSurface"
    | FEAttr a -> "EAttr" ^ sep ^ (of_attr a)
    | FESetAttr a -> "ESetAttr" ^ sep ^ (of_attr a)
    | FEDeleteField -> "EDeleteField"
    | FESet -> "ESet"
    | FEOp1 op1 -> "EOp1" ^ sep ^ (of_op1 op1)
    | FEOp2 op2 -> "EOp2" ^ sep ^ (of_op2 op2)
    | FEOp3 op3 -> "EOp3" ^ sep ^ (of_op3 op3)
    | FEIf -> "EIf"
    | FEApp -> "EApp"
    | FESeq -> "ESeq"
    | FELet -> "ELet"
    | FEFix -> "EFix"
    | FELabel -> "ELabel"
    | FEBreak -> "EBreak"
    | FETryCatch -> "ETryCatch"
    | FETryFinally -> "ETryFinally"
    | FEThrow -> "EThrow"
    | FELambda -> "ELambda"

  let of_feature = function
    | FExp e -> "Exp" ^ sep ^ (of_exp e)
    | FAttr a -> "Attr" ^ sep ^ (of_attr a)


  let add_all m =
    let const = [FCString; FCRegexp; FCNum; FCInt; FCBool; FCNull; FCUndefined] in
    let attr = [Value; Getter; Setter; Config; Writable; Enum] in
    let op1 = [(*`Op1Prefix "";*) `Prim1 ""] in
    let op2 = [(*`Op2Infix "";*) `Prim2 ""] in
    let op3 = [(*`Op3Prefix "";*) `Prim3 ""] in
    let exp =
      [
	FEId; FEObject; FEUpdateFieldSurface; FEGetFieldSurface;
	FEDeleteField; FESet; FEIf;
	FEApp; FESeq; FELet; FEFix; FELabel; FEBreak;
	FETryCatch; FETryFinally; FEThrow; FELambda
      ]
      @ List.map (fun c -> FEConst c) const
      @ List.map (fun a -> FEAttr a) attr
      @ List.map (fun a -> FESetAttr a) attr
      @ List.map (fun o -> FEOp1 o) op1
      @ List.map (fun o -> FEOp2 o) op2
      @ List.map (fun o -> FEOp3 o) op3
    in
    let l = List.map (fun e -> FExp e) exp @ List.map (fun a -> FAttr a) attr in
    let m' = List.fold_left (fun m f -> FM.add f () m) FM.empty l in
    let mergefun f _ = function
      | Some x -> Some x
      | None -> Some 0
    in
    FM.merge mergefun m' m


  let of_map m = FM.fold (fun f n sm -> StringMap.add (of_feature f) n sm) m StringMap.empty

  let group_stringmap m =
    let rec add_to_map f n gsm =
      if f = "" then
	gsm
      else
	let l = String.length f in
	let i = try String.index f char_sep with Not_found -> l in
	let gf = String.sub f 0 i in
	let n_of_f, subgsm = try StringMap.find gf gsm with Not_found -> 0, StringMap.empty in
	let subgsm = if i = l then subgsm else
	  add_to_map (String.sub f (i+1) (l-i-1)) n subgsm
	in
	StringMap.add gf (n_of_f + n, subgsm) gsm
    in
    StringMap.fold add_to_map m StringMap.empty

  let ind_char = ' '
  let default_indent = (true, 0) (* true: add father length *)
  let default_sort_max = false

  let rec list_of_groupstringmap gsm =
    StringMap.fold (fun f (n, gsm) l -> (f, n, (list_of_groupstringmap gsm))::l) gsm []

  let of_grouplist ?(sort_max = default_sort_max) ?(indent = default_indent) gl =
    let new_ind ind f = (if fst indent then String.length f else 0) + (snd indent) + ind
    in
    let rec flatten_grouplist ind gl =
      let gl = if sort_max then
	List.sort (fun (f1, n1, _) (f2, n2, _) -> Pervasives.compare (n1, f1) (n2, f2)) gl
      else
	gl
      in
      List.fold_left (fun l (f, n, gl) -> ((String.make ind ind_char ^ f, n)::(flatten_grouplist (new_ind ind f) gl))::l) [] gl
    |> List.flatten
    in
    let l = flatten_grouplist 0 gl in
    let max_length = List.fold_left (fun m (f, _) -> max m (String.length f)) 0 l in
    let max_n = List.fold_left (fun m (_, n) -> max m n) 0 l in
    let n_max_length = String.length (string_of_int max_n) in
    let one_entry (f, n) =
      let n_string = string_of_int n in
      let n_length = String.length n_string in
      let f_length = String.length f in
      let nb_ind = (max_length - f_length) + 1 + (n_max_length - n_length) in
      f ^ (String.make nb_ind ind_char) ^ n_string
    in
    let l = List.map one_entry l in
    String.concat "\n" l

  let string_of_map ?(sort_max = default_sort_max) ?(indent = default_indent) m =
    m |> add_all |> of_map |> group_stringmap |> list_of_groupstringmap |> of_grouplist ~sort_max ~indent

end
