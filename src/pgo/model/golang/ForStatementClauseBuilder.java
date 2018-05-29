package pgo.model.golang;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import pgo.scope.UID;

public class ForStatementClauseBuilder {

	private ASTBuilder parent;
	private NameCleaner nameCleaner;
	private Map<UID, VariableName> nameMap;
	private Set<String> labelScope;
	
	private Statement init;
	private Expression condition;
	private Statement inc;

	public ForStatementClauseBuilder(ASTBuilder parent, NameCleaner nameCleaner, Map<UID, VariableName> nameMap,
			Set<String> labelScope) {
		this.parent = parent;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		
		this.init = null;
		this.condition = null;
		this.inc = null;
	}
	
	public VariableName initVariable(String nameHint, Expression value) {
		String actualName = nameCleaner.cleanName(nameHint);
		VariableName name = new VariableName(actualName);
		init = new Assignment(Collections.singletonList(name), true, Collections.singletonList(value));
		return name;
	}
	
	public void setCondition(Expression condition) {
		this.condition = condition;
	}
	
	public void setInc(Statement inc) {
		this.inc = inc;
	}
	
	public BlockBuilder getBlockBuilder() {
		return new BlockBuilder(parent, nameCleaner, nameMap, labelScope, block -> {
			parent.addStatement(new For(init, condition, inc, block));
		});
	}

}
