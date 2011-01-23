function f(x) { return x-1; };
function g(x) { return x+1; };
x = symbol_int("x");
print( f(g(x)) == x ? "Yes" : "No" );
print( g(f(x)) == x ? "Yes" : "No" );