a = symbol_string("a");
b = symbol_string("b");
c = symbol_string("c");

if (a == "a")
    {
	assume(c == a+b);
	assume(c == "ab");
	assert(b == "b");
    }
