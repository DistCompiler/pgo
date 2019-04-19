package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.*;
import pgo.parser.Located;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.util.SourceLocation;

import java.util.*;

public class ModularPlusCalMappingMacroReadExpansionVisitor extends ModularPlusCalCodeGenVisitor {
	protected final TLAGeneralIdentifier dollarVariable;
	protected final UID varUID;
	protected final String nameHint;
	private final TLAExpression index;
	protected final TLAExpressionPlusCalCodeGenVisitor visitor;
	private final TLAGeneralIdentifier temporaryVariable;

	ModularPlusCalMappingMacroReadExpansionVisitor(
			DefinitionRegistry registry, Map<UID, PlusCalVariableDeclaration> params,
			Map<UID, TLAGeneralIdentifier> arguments, Map<UID, ModularPlusCalMappingMacro> mappings,
			Set<UID> expressionArguments, Set<UID> functionMappedVars, TemporaryBinding readTemporaryBinding,
			TemporaryBinding writeTemporaryBinding, ProcedureExpander procedureExpander,
			TLAGeneralIdentifier dollarVariable, UID varUID, String nameHint, TLAExpression index,
			TLAExpressionPlusCalCodeGenVisitor visitor, TLAGeneralIdentifier temporaryVariable) {
		super(
				registry, params, arguments, mappings, expressionArguments, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, visitor);
		this.dollarVariable = dollarVariable;
		this.varUID = varUID;
		this.nameHint = nameHint;
		this.index = index;
		this.visitor = visitor;
		this.temporaryVariable = temporaryVariable;
	}

	private List<PlusCalStatement> substituteStatements(List<PlusCalStatement> statements) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement statement : statements) {
			result.addAll(statement.accept(this));
		}
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		return Collections.singletonList(new PlusCalWhile(
				plusCalWhile.getLocation(),
				plusCalWhile.getCondition().accept(visitor),
				substituteStatements(plusCalWhile.getBody())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		List<PlusCalAssignmentPair> pairs = plusCalAssignment.getPairs();
		List<TLAExpression> rhsList = new ArrayList<>();
		if (pairs.size() > 1) {
			for (PlusCalAssignmentPair pair : pairs) {
				SourceLocation location = pair.getLocation();
				TLAExpression rhs = pair.getRhs().accept(visitor);
				TLAGeneralIdentifier rhsRead = readTemporaryBinding.declare(location, new UID(), "rhsRead");
				result.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(
								location, rhsRead, rhs))));
				rhsList.add(rhsRead);
			}
		} else {
			rhsList.add(pairs.get(0).getRhs().accept(visitor));
		}
		List<PlusCalAssignmentPair> transformedPairs = new ArrayList<>();
		for (int i = 0; i < pairs.size(); i++) {
			PlusCalAssignmentPair pair = pairs.get(i);
			SourceLocation location = pair.getLocation();
			TLAExpression lhs = pair.getLhs();
			TLAExpression rhs = rhsList.get(i);
			if (lhs instanceof TLASpecialVariableVariable) {
				TLAGeneralIdentifier variable = writeTemporaryBinding.lookup(varUID).orElse(dollarVariable);
				lhs = writeTemporaryBinding.declare(lhs.getLocation(), varUID, nameHint);
				if (index != null) {
					rhs = new TLAFunctionSubstitution(
							location,
							variable,
							Collections.singletonList(new TLAFunctionSubstitutionPair(
									location,
									Collections.singletonList(new TLASubstitutionKey(
											location, Collections.singletonList(index))),
									rhs)));
				}
			} else {
				lhs = lhs.accept(visitor);
			}
			transformedPairs.add(new PlusCalAssignmentPair(location, lhs, rhs));
		}
		result.add(new PlusCalAssignment(plusCalAssignment.getLocation(), transformedPairs));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		return Collections.singletonList(new PlusCalReturn(plusCalReturn.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		return Collections.singletonList(new PlusCalSkip(plusCalSkip.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		List<TLAExpression> params = new ArrayList<>();
		for (TLAExpression argument : plusCalCall.getArguments()) {
			params.add(argument.accept(visitor));
		}
		return Collections.singletonList(new PlusCalCall(
				plusCalCall.getLocation(),
				plusCalCall.getTarget(),
				params));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWith plusCalWith) throws RuntimeException {
		List<PlusCalVariableDeclaration> declarations = new ArrayList<>();
		for (PlusCalVariableDeclaration declaration : plusCalWith.getVariables()) {
			TLAGeneralIdentifier fresh = readTemporaryBinding.freshVariable(
					declaration.getLocation(), declaration.getUID(), declaration.getName().getValue());
			declarations.add(new PlusCalVariableDeclaration(
					declaration.getLocation(),
					new Located<>(declaration.getName().getLocation(), fresh.getName().getId()),
					false,
					declaration.isSet(),
					declaration.getValue().accept(visitor)));
		}
		return Collections.singletonList(new PlusCalWith(
				plusCalWith.getLocation(),
				declarations,
				substituteStatements(plusCalWith.getBody())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		return Collections.singletonList(new PlusCalPrint(
				plusCalPrint.getLocation(),
				plusCalPrint.getValue().accept(visitor)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		return Collections.singletonList(new PlusCalAssert(
				plusCalAssert.getLocation(),
				plusCalAssert.getCondition().accept(visitor)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		return Collections.singletonList(new PlusCalAwait(
				plusCalAwait.getLocation(),
				plusCalAwait.getCondition().accept(visitor)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		return Collections.singletonList(new PlusCalGoto(plusCalGoto.getLocation(), plusCalGoto.getTarget()));
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		return Collections.singletonList(new PlusCalAssignment(
				modularPlusCalYield.getLocation(),
				Collections.singletonList(new PlusCalAssignmentPair(
						modularPlusCalYield.getLocation(),
						temporaryVariable,
						modularPlusCalYield.getExpression().accept(visitor)))));
	}
}
