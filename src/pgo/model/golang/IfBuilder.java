package pgo.model.golang;

import java.io.Closeable;
import java.util.Map;
import java.util.Set;

import pgo.scope.UID;

public class IfBuilder implements Closeable {

	private ASTBuilder builder;
	private NameCleaner nameCleaner;
	private NameCleaner labelScope;
	private Expression condition;
	private Block trueBranch;
	private Block falseBranch;
	private Map<UID, VariableName> nameMap;

	public IfBuilder(ASTBuilder builder, NameCleaner nameCleaner, Map<UID, VariableName> nameMap,
			NameCleaner labelScope, Expression condition) {
		this.builder = builder;
		this.nameCleaner = nameCleaner;
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
		return new BlockBuilder(builder, nameCleaner.child(), nameMap, labelScope, this::addTrue);
	}
	
	public BlockBuilder whenFalse() {
		return new BlockBuilder(builder, nameCleaner.child(), nameMap, labelScope, this::addFalse);
	}

	@Override
	public void close() {
		builder.addStatement(new If(condition, trueBranch, falseBranch));
	}

}
