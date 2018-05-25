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
	private List<Expression> values;
    
    public Assignment(List<Expression> names, boolean defines, List<Expression> values) {
    	this.names = names;
    	this.defines = defines;
    	this.values = values;
    }
    
    public List<Expression> getNames() {
    	return names;
    }
    
    public boolean isDefinition() {
    	return defines;
    }
    
    public List<Expression> getValues() {
    	return values;
    }

    @Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
