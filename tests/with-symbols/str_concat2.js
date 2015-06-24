a = symbol_string("a");
b = symbol_string("b");

if (a === "a" && b === "b")
    {
	assert(a+b === "ab");
	print("Ok");
    }
else
    print("Maybe");
