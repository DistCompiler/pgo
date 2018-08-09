package pgo.model.golang;

import pgo.model.golang.type.GoType;

import java.util.List;
import java.util.Objects;

/**
 * Wraps the definition of a Golang struct
 *
 */
public class GoStructLiteral extends GoExpression {
	
	GoType type;
	
	List<GoStructLiteralField> fields;

    public GoStructLiteral(GoType type, List<GoStructLiteralField> fields) {
        this.type = type;
        this.fields = fields;
    }
    
    public GoType getType() {
    	return type;
    }
    
    public List<GoStructLiteralField> getFields(){
    	return fields;
    }

    @Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoStructLiteral that = (GoStructLiteral) o;
		return Objects.equals(type, that.type) &&
				Objects.equals(fields, that.fields);
	}

	@Override
	public int hashCode() {

		return Objects.hash(type, fields);
	}
}
