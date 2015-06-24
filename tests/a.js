var desc = Object.getOwnPropertyDescriptor(Error.prototype, "constructor");
print(desc.value);
print(Error.prototype.constructor);
print(desc.value === Error.prototype.constructor);
print(desc.writable);
print(desc.enumerable);
print(desc.configurable);

