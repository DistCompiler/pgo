package pgo.model.golang;

import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeName;

import java.util.Objects;

public final class GoBuiltins {

	private GoBuiltins() {}

	public static class BuiltinConstant extends GoExpression {
		private String value;

		public BuiltinConstant(String value) {
			this.value = value;
		}

		public String getValue() {
			return value;
		}

		@Override
		public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
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

	public static GoTypeName Interface = new GoTypeName("interface{}", true);
	public static GoTypeName Error = new GoTypeName("error", true);
	public static GoTypeName Bool = new GoTypeName("bool", true);
	public static GoTypeName String = new GoTypeName("string", true);
	public static GoTypeName UInt8 = new GoTypeName("uint8", true);
	public static GoTypeName UInt16 = new GoTypeName("uint16", true);
	public static GoTypeName UInt32 = new GoTypeName("uint32", true);
	public static GoTypeName UInt64 = new GoTypeName("uint64", true);
	public static GoTypeName Float32 = new GoTypeName("float32", true);
	public static GoTypeName Float64 = new GoTypeName("float64", true);
	public static GoTypeName Int8 = new GoTypeName("int8", true);
	public static GoTypeName Int16 = new GoTypeName("int16", true);
	public static GoTypeName Int32 = new GoTypeName("int32", true);
	public static GoTypeName Int64 = new GoTypeName("int64", true);
	public static GoTypeName Complex32 = new GoTypeName("complex32", true);
	public static GoTypeName Complex64 = new GoTypeName("complex64", true);

	// types that aren't real, but may be useful to mark that an algorithm doesn't care
	// about 32 vs. 64 bit floats for example
	public static GoType Float = Float32;

	// machine-specific aliases, defined by GoRoutineStatement
	public static GoType UInt = new GoTypeName("uint", true);
	public static GoType Int = new GoTypeName("int", true);
	public static GoType UIntPtr = new GoTypeName("uintptr", true);

	// language aliases, here for convenience
	public static GoType Byte = new GoTypeName("byte", true); // uint8
	public static GoType Rune = new GoTypeName("rune", true); // int32

	// built-in constants
	public static GoExpression True = new BuiltinConstant("true");
	public static GoExpression False = new BuiltinConstant("false");

	public static GoExpression Nil = new BuiltinConstant("nil");
}
