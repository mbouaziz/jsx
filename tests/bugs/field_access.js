var x = { a : { n : "A" }, b : { n : "B" } };
var s = "a";
x[s].n = (function(){ s = "b"; return "C"; })();
print(x.a.n); // C
print(x.b.n); // B

x.c = 0;
x.c += (function(){ x = { c : 1 }; return 2; })();
print(x.c); // 1

x.c = 0;
x.c += (function(){ x.c = 1; return 2; })();
print(x.c); // 2

x.c = 0;
x.c += (function(){ x.c += 1; return 2; })();
print(x.c); // 2

var c = 0;
c += (function(){ c = 1; return 2; })();
print(c); // 2

c = 0;
c += (function(){ c += 1; return 2; })();
print(c); // 2

c = 0;
c = (function(){ c = 1; return 2; })() + c;
print(c); // 3

c = 0;
c = (function(){ c += 1; return 2; })() + c;
print(c); // 3
