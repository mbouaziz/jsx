
open MyPervasives
open SymbolicValue


module SState :
sig
  type 'r t
  type 'r _set
  type 'v call
  type 'v callstack
  type 'v sexn = ('v, 'v callstack) _sexn
  type set = srvalue _set
  and svalue = sclosure _svalue
  and srvalue = (svalue, svalue sexn) rvalue
  and sclosure = (unit t, set) _closure
  type s = srvalue t
  type envlabel
  type env

  val marshal_in : in_channel -> set option
  val marshal_out : out_channel -> set option -> unit

  val first : unit t
  val get_singleton : 'a _set -> 'a t option
  val singleton : 'a t -> 'a _set
  val map_unit : ('a t -> 'b t) -> 'a _set -> 'b _set
  val map : ('a t -> 'b _set) -> 'a _set -> 'b _set
  val map_res : ('a -> 'a t -> 'b _set) -> 'a _set -> 'b _set
  val map_res_unit : ('a -> 'a t -> 'b t) -> 'a _set -> 'b _set
  val get_first : set -> s
  val get_next : set -> (unit -> set) option
    (* the return function should be called only once for a lazy set *)

  val res : 'a -> 'b t -> 'a t
  val res_v : svalue -> 'a t -> set
  val res_undef : 'a t -> set
  val res_false : 'a t -> set
  val res_true : 'a t -> set
  val res_bool : bool -> 'a t -> set
  val res_int : int -> 'a t -> set
  val res_num : float -> 'a t -> set
  val res_str : string -> 'a t -> set
  val res_heaplabel : sheaplabel -> 'a t -> set
  val res_heap_add : sheaplabel -> svalue props -> sclosure internal_props -> 'a t -> set
  val res_heap_add_fresh : svalue props * sclosure internal_props -> 'a t -> set
  val res_id : typ:SymbolicValue.ssymb_type -> sid -> 'a t -> set
  val res_op1 : typ:SymbolicValue.ssymb_type -> string -> svalue -> 'a t -> set
  val res_op2 : typ:SymbolicValue.ssymb_type -> string -> svalue -> svalue -> 'a t -> set

  val exn : svalue sexn -> 'a t -> s
  val clean_exn : 'a t -> unit t

  val break : pos:pos -> LambdaJS.Values.label -> svalue -> 'a t -> set
  val throw : pos:pos -> svalue -> 'a t -> set
  val throw_str : pos:pos -> 'a t -> string -> set
  val err : pos:pos -> 'a t -> err -> set

  val check_exn : ('a t -> set) -> 'a t -> set
  val check_exn_res : ('a -> 'a t -> set) -> 'a t -> set
  val do_no_exn : (svalue -> s -> set) -> s -> set

  val do1 : ('a -> unit t -> set) -> (svalue -> s -> set) -> 'a -> 'c t -> set
  val do2 : ('a -> unit t -> set) -> (svalue -> svalue -> s -> set) -> 'a -> 'a -> 'c t -> set
  val do3 : ('a -> unit t -> set) -> (svalue -> svalue -> svalue -> s -> set) -> 'a -> 'a -> 'a -> 'b t -> set
  val do4 : ('a -> unit t -> set) -> (svalue -> svalue -> svalue -> svalue -> s -> set) -> 'a -> 'a -> 'a -> 'a -> 'b t -> set
end

open SState

module CallStack :
sig
  val mk_call : pos:pos -> svalue list -> 'a t -> svalue call
  val push : svalue call -> 'a t -> 'a t
  val pop : 'a t -> 'a t
  val top : 'a t -> svalue call option
  val call_pos : 'a call -> pos
  val call_env : 'a call -> env
end
module Env :
sig
  val fresh_label : 'a t -> 'a t * envlabel
  val repl : id -> envlabel -> svalue -> 'a t -> 'a t
  val bind : id -> svalue -> 'a t -> 'a t
  val unbind : id -> 'a t -> 'a t
  val find : id -> 'a t -> svalue option
  val set : id -> svalue -> 'a t -> ('a t, 'a t) rvalue

  val get : 'a t -> env
  val dupl : 'a t -> 'a t
  val push : env -> 'a t -> 'a t
  val pop : 'a t -> 'a t
  val to_string : 'a t -> string
end
module Heap :
sig
  val update_p : sheaplabel -> svalue props -> 'a t -> 'a t
  val update_ip : sheaplabel -> sclosure internal_props -> 'a t -> 'a t
  val add : sheaplabel -> svalue props -> sclosure internal_props -> 'a t -> 'a t
  val find_p : sheaplabel -> 'a t -> svalue props
  val find_ip : sheaplabel -> 'a t -> sclosure internal_props
end
module Output :
sig
  val print : name:string -> svalue -> 'a t -> 'a t
end
module PathCondition :
sig
  val _assert : pos:pos -> svalue -> 'a t -> set
  val assume : pos:pos -> svalue -> 'a t -> set
  val branch : ('a t -> set) -> ('a t -> set) -> svalue -> 'a t -> set
end  
module ToString :
sig
  val svalue : ?deep:bool -> ?brackets:bool -> 'a t -> svalue -> string
  val svalue_list : 'a t -> svalue list -> string
  val state : s -> string
  val nosymb_state : s -> string * string option
  val model : s -> string
  val short_model : s -> string
end
