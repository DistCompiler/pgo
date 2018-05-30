package pgo.model.golang;

public final class Builtins {
	
	private Builtins() {}
	
	public static class BuiltinConstant extends Expression {
		private String value;
		
		public BuiltinConstant(String value) {
			this.value = value;
		}
		
		public String getValue() {
			return value;
		}
		
		@Override
		public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
			return visitor.visit(this);
		}
	}

	public static TypeName Bool = new TypeName("bool");
	public static TypeName String = new TypeName("string");
	public static TypeName UInt8 = new TypeName("uint8");
	public static TypeName UInt16 = new TypeName("uint16");
	public static TypeName UInt32 = new TypeName("uint32");
	public static TypeName UInt64 = new TypeName("uint64");
	public static TypeName Float32 = new TypeName("float32");
	public static TypeName Float64 = new TypeName("float64");
	public static TypeName Int8 = new TypeName("int8");
	public static TypeName Int16 = new TypeName("int16");
	public static TypeName Int32 = new TypeName("int32");
	public static TypeName Int64 = new TypeName("int64");
	public static TypeName Complex32 = new TypeName("complex32");
	public static TypeName Complex64 = new TypeName("complex64");

	// types that aren't real, but may be useful to mark that an algorithm doesn't care
	// about 32 vs. 64 bit floats for example
	public static Type Float = Float32;
	
	// machine-specific aliases, defined by Go
	public static Type UInt = new TypeName("uint");
	public static Type Int = new TypeName("int");
	public static Type UIntPtr = new TypeName("uintptr");
	
	// language aliases, here for convenience
	public static Type Byte = new TypeName("byte"); // uint8
	public static Type Rune = new TypeName("rune"); // int32
	
	// built-in constants
	public static Expression True = new BuiltinConstant("true");
	public static Expression False = new BuiltinConstant("false");

	public static Expression EmptyString = new BuiltinConstant("\"\"");

	public static Expression Nil = new BuiltinConstant("nil");
}
