package pgo.model.golang;

import java.util.Collections;
import java.util.List;

/**
 * Assigns a value to a variable :
 *
 *
 *  goVar = {expr}
 *
 */
public class Assignment extends Statement {

    List<VariableName> names;
    Expression value;
    
    public Assignment(VariableName name, Expression value) {
    	this.names = Collections.singletonList(name);
    	this.value = value;
    }
    
    public Assignment(List<VariableName> names, Expression value) {
    	this.names = names;
    	this.value = value;
    }
    
    public List<VariableName> getNames() {
    	return names;
    }
    
    public Expression getValue() {
    	return value;
    }

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}
}
