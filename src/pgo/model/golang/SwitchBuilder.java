package pgo.model.golang;

import pgo.scope.UID;

import java.io.Closeable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class SwitchBuilder implements Closeable {
	private ASTBuilder builder;
	private NameCleaner nameCleaner;
	private Map<UID, VariableName> nameMap;
	private NameCleaner labelScope;
	private Expression switchExp;
	private List<SwitchCase> cases;
	private List<Statement> defaultBlock;

	public SwitchBuilder(ASTBuilder builder, NameCleaner nameCleaner, Map<UID, VariableName> nameMap,
	                     NameCleaner labelScope, Expression switchExp) {
		this.builder = builder;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		this.switchExp = switchExp;
		this.cases = new ArrayList<>();
	}

	private void addCase(Expression expression, Block block) {
		cases.add(new SwitchCase(expression, block.getStatements()));
	}

	private void defaultCase(Block block) {
		defaultBlock = block.getStatements();
	}

	public BlockBuilder addCase(Expression expression) {
		return new BlockBuilder(builder, nameCleaner.child(), nameMap, labelScope, block -> addCase(expression, block));
	}

	public BlockBuilder defaultCase() {
		return new BlockBuilder(builder, nameCleaner.child(), nameMap, labelScope, this::defaultCase);
	}

	@Override
	public void close() {
		builder.addStatement(new Switch(switchExp, cases, defaultBlock));
	}
}
