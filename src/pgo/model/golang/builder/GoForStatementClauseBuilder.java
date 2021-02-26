package pgo.model.golang.builder;

import pgo.model.golang.*;
import pgo.scope.UID;
import pgo.trans.passes.codegen.NameCleaner;

import java.util.Collections;
import java.util.Map;

public class GoForStatementClauseBuilder {

	private final GoASTBuilder parent;
	private final NameCleaner nameCleaner;
	private final Map<UID, GoVariableName> nameMap;
	private final NameCleaner labelScope;
	
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
