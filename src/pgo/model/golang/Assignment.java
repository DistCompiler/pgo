package pgo.model.golang;

import java.util.List;

/**
 * Assigns a value to a variable :
 *
 *
 *  goVar = {expr}
 *
 */
public class Assignment extends Statement {

	private List<Expression> names;
	private boolean defines;
	private Expression value;
    
    public Assignment(List<Expression> names, boolean defines, Expression value) {
    	this.names = names;
    	this.value = value;
    }
    
    public List<Expression> getNames() {
    	return names;
    }
    
    public boolean getDefines() {
    	return defines;
    }
    
    public Expression getValue() {
    	return value;
    }

    @Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
