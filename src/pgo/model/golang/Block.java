package pgo.model.golang;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Block extends Statement {
	
	Map<String, Type> locals; 
	List<Statement> statements;
	Set<String> labels;
	
	public Block() {
		this.locals = new HashMap<>();
		this.statements = new ArrayList<>();
	}
	
	public Map<String, Type> getLocals(){
		return locals;
	}
	
	public List<Statement> getStatements(){
		return statements;
	}
	
	public void addStatement(Statement statement) {
		this.statements.add(statement);
	}
	
	public VariableName addLocal(String name, Type type) {
		locals.put(name, type);
		return new VariableName(name, type);
	}
	
	public LabelName addLabel(String name) {
		String realName = name;
		int counter = 0;
		while(labels.contains(realName)) {
			realName = name + counter;
			counter++;
		}
		labels.add(realName);
		return new LabelName(realName);
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

}
