package pgo.trans.intermediate;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLASymbol;
import pgo.model.tla.PGoTLAUnary;
import pgo.model.type.PGoType;
import pgo.scope.UID;

import java.util.Collections;
import java.util.Map;

public class CodeGenUtil {
	private CodeGenUtil() {}

	public static Expression invertCondition(BlockBuilder builder, DefinitionRegistry registry,
	                                         Map<UID, PGoType> typeMap,
	                                         GlobalVariableStrategy globalStrategy,
	                                         PGoTLAExpression condition) {
		PGoTLAUnary invertedCond = new PGoTLAUnary(
				condition.getLocation(),
				new PGoTLASymbol(condition.getLocation(), "~"),
				Collections.emptyList(),
				condition);
		return invertedCond.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
	}
}
