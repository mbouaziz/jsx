/*
  With SMT enabled, only one case can happen in each path
  And cow will never happen!
 */
x = symbol("x");
s = typeof(x);
if (s === "null")
    print("Null");
if (s === "undefined")
    print("Undefined");
if (s === "boolean")
    print("Boolean");
if (s === "number")
    print("Number");
if (s === "string")
    print("String");
if (s === "cow")
    print("Cow");
