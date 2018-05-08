package pgo.model.golang;

public final class Builtins {
	
	public static class BuiltinType extends Type {
		String name;
		
		public BuiltinType(String name) {
			this.name = name;
		}
		
		public String getName() {
			return name;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((name == null) ? 0 : name.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			BuiltinType other = (BuiltinType) obj;
			if (name == null) {
				if (other.name != null)
					return false;
			} else if (!name.equals(other.name))
				return false;
			return true;
		}
	}
	
	public static class BuiltinConstant extends Expression {
		String value;
		
		public BuiltinConstant(String value) {
			this.value = value;
		}
		
		public String getValue() {
			return value;
		}
		
		@Override
		public <T> T accept(Expression.Visitor<T> v) {
			return v.visit(this);
		}
	};

	static Type Bool = new BuiltinType("bool");
	static Type String = new BuiltinType("string");
	static Type UInt8 = new BuiltinType("uint8");
	static Type UInt16 = new BuiltinType("uint16");
	static Type UInt32 = new BuiltinType("uint32");
	static Type UInt64 = new BuiltinType("uint64");
	static Type Float32 = new BuiltinType("float32");
	static Type Float64 = new BuiltinType("float64");
	static Type Int8 = new BuiltinType("int8");
	static Type Int16 = new BuiltinType("int16");
	static Type Int32 = new BuiltinType("int32");
	static Type Int64 = new BuiltinType("int64");
	static Type Complex32 = new BuiltinType("complex32");
	static Type Complex64 = new BuiltinType("complex64");
	
	// types that aren't real, but may be useful to mark that an algorithm doesn't care
	// about 32 vs. 64 bit floats for example
	static Type Float = Float32;
	
	// machine-specific aliases, defined by Go
	static Type UInt = new BuiltinType("uint");
	static Type Int = new BuiltinType("int");
	static Type UIntPtr = new BuiltinType("uintptr");
	
	// language aliases, here for convenience
	static Type Byte = new BuiltinType("byte"); // uint8
	static Type Rune = new BuiltinType("rune"); // int32
	
	// built-in constants
	static Expression True = new BuiltinConstant("true");
	static Expression False = new BuiltinConstant("false");
	
	static Expression Nil = new BuiltinConstant("nil");
}
