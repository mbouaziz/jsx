
var r = [];

for (var i = 0 ; i < 10 ; ++i)
    {
	r[i] = symbol_int("r" + i);
	assume(0 <= r[i]);
	assume(r[i] <= i);
	if (r[i] * r[i] === i)
	    print(i + " is a perfect square");
    }
