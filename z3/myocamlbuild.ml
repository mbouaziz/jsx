(*
Modified from:
http://brion.inria.fr/gallium/index.php/Ocamlbuild_example_with_C_stubs
*)

 open Ocamlbuild_plugin
 
 (* Configuration section *)
 let static = true
 
 (* List of headers *)
 let headers = ["include/z3_api.h"; "include/z3.h"]
 
 ;;
 
 dispatch begin function
 | After_rules ->
 
     (* If `static' is true then every ocaml link in bytecode will add -custom *)
     if static then flag ["link"; "ocaml"; "byte"] (A"-custom");
 
     (* As an approximation all our C files use the headers.
        Note: This will import headers in the build directory. *)
     dep  ["compile"; "c"] headers;
     flag ["compile"; "c"] (S[A"-ccopt";A"-I../include"]);
 | _ -> ()
 end
