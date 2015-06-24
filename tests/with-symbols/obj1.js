
var o = symbol_object("o", Object, "Object", true);

if (o.a === o)
    {
	print(o.a);
    }
else
    {
o.h = "hello";
o.a = o;
print(o.a.a.a.h);
    }