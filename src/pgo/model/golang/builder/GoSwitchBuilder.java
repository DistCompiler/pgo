package pgo.model.golang.builder;

import pgo.model.golang.*;
import pgo.scope.UID;
import pgo.trans.passes.codegen.NameCleaner;

import java.io.Closeable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class GoSwitchBuilder implements Closeable {
	private final GoASTBuilder builder;
	private final NameCleaner nameCleaner;
	private final Map<UID, GoVariableName> nameMap;
	private final NameCleaner labelScope;
	private final GoExpression switchExp;
	private final List<GoSwitchCase> cases;
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
