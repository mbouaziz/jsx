
for (var i = 0 ; i < 10 ; ++i)
    {
	x = symbol_int("r" + i);
	assume(0 <= x);
	assume(x <= i);
	if (x * x === i)
	    print(i + " is a perfect square");
    }
