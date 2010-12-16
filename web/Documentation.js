/*
  Welcome to JSX Web
  
  This web interface let you play with JSX as if you have installed it from source.
  
  You have to write a source code in this text area or select a file in the list above.
  
  A source code can be written in JavaScript or in LambdaJS-ES5.
  Select the language you want to use.
  The JavaScript parser is from LambdaJS, there is no automatic semi-colon insertion.
  
  You can select the environments [env] to use.
  A code won't run without es5-lib.es5 (LambdaJS standard library).
  symbolic.es5 is an additional environment allowing to use:
  - symbol("X") for the symbolic value @X
  - assume(some_predicate) to assume some_predicate
  - assume_primitive(expr) to assume that expr is of a primitive type
  - assume_callable(expr) to assume that expr is a callable object
  - assume_string(expr) to assume that expr is of type string

  The environments [pre-js] [post-js] are used by some test suites.
  
  Options:
  - display assumptions
      if selected, will show assumptions collected in each path
  - record backtrace
      if selected, show the OCaml call stack whenever an exception is raised
      can be unselected to improve performance
  - evaluate code
      call the evaluator of LambdaJS and display the result
  - list used features
      list all LambdaJS features used in the current code (including environments)
  - fatal errors
      if selected, an OCaml exception will be raised if an exception is raised in a path of the symbolic evaluation
      basically for debugging purposes
  - pretty print code
      print the LambdaJS code (including environments)
  - symbols in symbolic evaluation
      if unselected, disallow the primitive 'symbol' and assume that there is only one path
      used to test semantics without symbols
  - symbolically evaluate code
      call the symbolic evaluator (JSX)

  The output of the symbolic evaluation is a list of tuples:
  - (possibly) 'assum' a conjunction of assumptions (if the option is selected)
  - 'pc' a path condition, which is a conjunction of symbolic values or negation of symbolic values
  - (possibly) 'heap' a heap state, only objects referenced somewhere else in the output are shown
  - (possibly) 'exn' an exception
  - (possibly) 'out' an output, use the function 'print' to display values on the output
*/

