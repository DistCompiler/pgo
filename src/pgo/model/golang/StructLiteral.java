package pgo.model.golang;

import java.util.LinkedHashMap;

/**
 * Wraps the definition of a Golang struct
 *
 */
public class StructLiteral extends Expression {
	
	Type type;
	
	LinkedHashMap<String, Expression> fields;

    public StructLiteral(Type type, LinkedHashMap<String, Expression> fields) {
        this.type = type;
        this.fields = fields;
    }
    
    public Type getType() {
    	return type;
    }
    
    public LinkedHashMap<String, Expression> getFields(){
    	return fields;
    }

    @Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}
}
