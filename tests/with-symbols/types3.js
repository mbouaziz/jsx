/*
  Notice that a path condition is created to test if
  typeof(...) is printable. Since it is always true,
  z is not in the model
 */
print(typeof(symbol("z")));
