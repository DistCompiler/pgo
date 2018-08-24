package pgo.model.golang.builder;

import pgo.model.golang.*;
import pgo.scope.UID;
import pgo.util.NameCleaner;

import java.io.Closeable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class GoSwitchBuilder implements Closeable {
	private GoASTBuilder builder;
	private NameCleaner nameCleaner;
	private Map<UID, GoVariableName> nameMap;
	private NameCleaner labelScope;
	private GoExpression switchExp;
	private List<GoSwitchCase> cases;
	private List<GoStatement> defaultBlock;

	public GoSwitchBuilder(GoASTBuilder builder, NameCleaner nameCleaner, Map<UID, GoVariableName> nameMap,
						   NameCleaner labelScope, GoExpression switchExp) {
		this.builder = builder;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		this.switchExp = switchExp;
		this.cases = new ArrayList<>();
	}

	private void addCase(GoExpression expression, GoBlock block) {
		cases.add(new GoSwitchCase(expression, block.getStatements()));
	}

	private void defaultCase(GoBlock block) {
		defaultBlock = block.getStatements();
	}

	public GoBlockBuilder addCase(GoExpression expression) {
		return new GoBlockBuilder(builder, nameCleaner.child(), nameMap, labelScope, block -> addCase(expression, block));
	}

	public GoBlockBuilder defaultCase() {
		return new GoBlockBuilder(builder, nameCleaner.child(), nameMap, labelScope, this::defaultCase);
	}

	@Override
	public void close() {
		builder.addStatement(new GoSwitch(switchExp, cases, defaultBlock));
	}
}
