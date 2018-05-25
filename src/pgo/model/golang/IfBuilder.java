package pgo.model.golang;

import java.io.Closeable;
import java.util.Map;
import java.util.Set;

import pgo.scope.ChainSet;
import pgo.scope.UID;

public class IfBuilder implements Closeable {

	private ASTBuilder builder;
	private Set<String> variableScope;
	private Set<String> labelScope;
	private Expression condition;
	private Block trueBranch;
	private Block falseBranch;
	private Map<UID, VariableName> nameMap;

	public IfBuilder(ASTBuilder builder, Set<String> variableScope, Map<UID, VariableName> nameMap,
			Set<String> labelScope, Expression condition) {
		this.builder = builder;
		this.variableScope = variableScope;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		this.condition = condition;
		this.trueBranch = null;
		this.falseBranch = null;
	}
	
	private void addTrue(Block block) {
		trueBranch = block;
	}
	
	private void addFalse(Block block) {
		falseBranch = block;
	}
	
	public BlockBuilder whenTrue() {
		return new BlockBuilder(builder, new ChainSet<>(variableScope), nameMap, labelScope, (block) -> addTrue(block));
	}
	
	public BlockBuilder whenFalse() {
		return new BlockBuilder(builder, new ChainSet<>(variableScope), nameMap, labelScope, (block) -> addFalse(block));
	}

	@Override
	public void close() {
		builder.addStatement(new If(condition, trueBranch, falseBranch));
	}

}
