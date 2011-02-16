
b0 = symbol_bool("b0");
b1 = symbol_bool("b1");

p0 = function(s) { output("p0", s); };
p1 = function(s) { output("p1", s); };

x = (b0 && b1 ? p0 : p1)("and");
x = (b0 || b1 ? p0 : p1)("or");
