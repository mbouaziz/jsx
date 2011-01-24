/*
  This example demonstrates a case in which depth-first search can
  give partial results whereas breadth-first would take too much
  time to give any result (and memory usage would be too large)
 */

var M = 20;
var b = [], v = [];

for (var i = 0 ; i < M ; i++)
    {
	b[i] = symbol_bool("b" + i);
	v[i] = i == 0 ? 1 : 2*v[i-1];
    }

var r = 0;
for (var i = M-1 ; i >=0 ; i--)
    r+=b[i]?0:v[i];

print(r);
