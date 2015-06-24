var f = function (y) {
    var x = function () { };
    if (x)
	x(this, y);
};
