package pgo.model.golang;

import pgo.scope.UID;

import java.util.*;

public class ForRangeBuilder {
	private ASTBuilder parent;
	private NameCleaner nameCleaner;
	private Map<UID, VariableName> nameMap;
	private NameCleaner labelScope;

	private List<Expression> lhs;
	private Expression rangeExpr;

	public ForRangeBuilder(ASTBuilder parent, NameCleaner nameCleaner, Map<UID, VariableName> nameMap, NameCleaner labelScope, Expression rangeExpr) {
		this.parent = parent;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		this.rangeExpr = rangeExpr;
		this.lhs = new ArrayList<>();
	}

	public List<VariableName> initVariables(List<String> nameHints) {
		List<VariableName> names = new ArrayList<>();
		for (String nameHint : nameHints) {
			String actualName = nameCleaner.cleanName(nameHint);
			VariableName name = new VariableName(actualName);
			names.add(name);
			lhs.add(name);
		}
		return names;
	}

	public BlockBuilder getBlockBuilder() {
		return new BlockBuilder(parent, nameCleaner, nameMap, labelScope, block ->
				parent.addStatement(new ForRange(lhs, true, rangeExpr, block)));
	}
}
