package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * Wraps the definition of a Golang struct
 *
 */
public class StructLiteral extends Expression {
	
	Type type;
	
	List<StructLiteralField> fields;

    public StructLiteral(Type type, List<StructLiteralField> fields) {
        this.type = type;
        this.fields = fields;
    }
    
    public Type getType() {
    	return type;
    }
    
    public List<StructLiteralField> getFields(){
    	return fields;
    }

    @Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		StructLiteral that = (StructLiteral) o;
		return Objects.equals(type, that.type) &&
				Objects.equals(fields, that.fields);
	}

	@Override
	public int hashCode() {

		return Objects.hash(type, fields);
	}
}
