function a() {
 this.x = (function(z){delete z.x; return 1;})(this);
};

b = new a();
print(b.x);
