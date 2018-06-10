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

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Assignment that = (Assignment) o;
		return defines == that.defines &&
				Objects.equals(names, that.names) &&
				Objects.equals(values, that.values);
	}

	@Override
	public int hashCode() {

		return Objects.hash(names, defines, values);
	}
}
