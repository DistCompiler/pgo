package pgo.model.golang;

import java.util.List;

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
}
