package pgo.model.golang;

import java.util.Objects;

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

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			BuiltinConstant that = (BuiltinConstant) o;
			return Objects.equals(value, that.value);
		}

		@Override
		public int hashCode() {

			return Objects.hash(value);
		}
	}

	public static TypeName Bool = new TypeName("bool", true);
	public static TypeName String = new TypeName("string", true);
	public static TypeName UInt8 = new TypeName("uint8", true);
	public static TypeName UInt16 = new TypeName("uint16", true);
	public static TypeName UInt32 = new TypeName("uint32", true);
	public static TypeName UInt64 = new TypeName("uint64", true);
	public static TypeName Float32 = new TypeName("float32", true);
	public static TypeName Float64 = new TypeName("float64", true);
	public static TypeName Int8 = new TypeName("int8", true);
	public static TypeName Int16 = new TypeName("int16", true);
	public static TypeName Int32 = new TypeName("int32", true);
	public static TypeName Int64 = new TypeName("int64", true);
	public static TypeName Complex32 = new TypeName("complex32", true);
	public static TypeName Complex64 = new TypeName("complex64", true);

	// types that aren't real, but may be useful to mark that an algorithm doesn't care
	// about 32 vs. 64 bit floats for example
	public static Type Float = Float32;
	
	// machine-specific aliases, defined by Go
	public static Type UInt = new TypeName("uint", true);
	public static Type Int = new TypeName("int", true);
	public static Type UIntPtr = new TypeName("uintptr", true);
	
	// language aliases, here for convenience
	public static Type Byte = new TypeName("byte", true); // uint8
	public static Type Rune = new TypeName("rune", true); // int32
	
	// built-in constants
	public static Expression True = new BuiltinConstant("true");
	public static Expression False = new BuiltinConstant("false");

	public static Expression Nil = new BuiltinConstant("nil");
}
