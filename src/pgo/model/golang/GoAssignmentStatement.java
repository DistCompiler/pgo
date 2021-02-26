package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * Assigns a value to a variable :
 *
 *
 *  goVar = {expr}
 *
 */
public class GoAssignmentStatement extends GoStatement {

	private final List<GoExpression> names;
	private final boolean defines;
	private final List<GoExpression> values;
    
    public GoAssignmentStatement(List<GoExpression> names, boolean defines, List<GoExpression> values) {
    	this.names = names;
    	this.defines = defines;
    	this.values = values;
    }
    
    public List<GoExpression> getNames() {
    	return names;
    }
    
    public boolean isDefinition() {
    	return defines;
    }
    
    public List<GoExpression> getValues() {
    	return values;
    }

    @Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoAssignmentStatement that = (GoAssignmentStatement) o;
		return defines == that.defines &&
				Objects.equals(names, that.names) &&
				Objects.equals(values, that.values);
	}

	@Override
	public int hashCode() {

		return Objects.hash(names, defines, values);
	}
}
