package pgo.model.golang.builder;

import java.util.Collections;
import java.util.Map;

import pgo.model.golang.*;
import pgo.model.golang.builder.GoASTBuilder;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.scope.UID;

public class GoForStatementClauseBuilder {

	private GoASTBuilder parent;
	private NameCleaner nameCleaner;
	private Map<UID, GoVariableName> nameMap;
	private NameCleaner labelScope;
	
	private GoStatement init;
	private GoExpression condition;
	private GoStatement inc;

	public GoForStatementClauseBuilder(GoASTBuilder parent, NameCleaner nameCleaner, Map<UID, GoVariableName> nameMap,
									   NameCleaner labelScope) {
		this.parent = parent;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		
		this.init = null;
		this.condition = null;
		this.inc = null;
	}
	
	public GoVariableName initVariable(String nameHint, GoExpression value) {
		String actualName = nameCleaner.cleanName(nameHint);
		GoVariableName name = new GoVariableName(actualName);
		init = new GoAssignmentStatement(Collections.singletonList(name), true, Collections.singletonList(value));
		return name;
	}
	
	public void setCondition(GoExpression condition) {
		this.condition = condition;
	}
	
	public void setInc(GoStatement inc) {
		this.inc = inc;
	}
	
	public GoBlockBuilder getBlockBuilder() {
		return new GoBlockBuilder(parent, nameCleaner, nameMap, labelScope, block -> {
			parent.addStatement(new GoFor(init, condition, inc, block));
		});
	}

}
