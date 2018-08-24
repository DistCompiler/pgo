package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.model.pcal.*;
import pgo.model.tla.TLABinOp;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAFunctionCall;
import pgo.model.tla.TLAGeneralIdentifier;

import java.util.*;
import java.util.stream.Collectors;

public class PlusCalMacroExpansionVisitor extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {

	private IssueContext ctx;
	private Map<String, PlusCalMacro> macros;
	private Set<String> recursionSet;
	private Map<String, TLAExpression> macroArgs;
	private TLAExpressionMacroSubstitutionVisitor macroSubst;

	public PlusCalMacroExpansionVisitor(IssueContext ctx, Map<String, PlusCalMacro> macros, Set<String> recursionSet, Map<String, TLAExpression> macroArgs) {
		this.ctx = ctx;
		this.macros = macros;
		this.recursionSet = recursionSet;
		this.macroArgs = macroArgs;
		this.macroSubst = new TLAExpressionMacroSubstitutionVisitor(ctx, macroArgs);
	}

	private List<PlusCalStatement> substituteStatements(List<PlusCalStatement> stmts) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement stmt : stmts) {
			result.addAll(stmt.accept(this));
		}
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		return Collections.singletonList(new PlusCalLabeledStatements(labeledStatements.getLocation(),
				labeledStatements.getLabel(), substituteStatements(labeledStatements.getStatements())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		return Collections.singletonList(new PlusCalWhile(
				plusCalWhile.getLocation(), plusCalWhile.getCondition().accept(macroSubst), substituteStatements(plusCalWhile.getBody())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		return Collections.singletonList(new PlusCalIf(
				plusCalIf.getLocation(), plusCalIf.getCondition().accept(macroSubst), substituteStatements(plusCalIf.getYes()), substituteStatements(plusCalIf.getNo())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalEither plusCalEither) throws RuntimeException {
		return Collections.singletonList(new PlusCalEither(
				plusCalEither.getLocation(), plusCalEither.getCases().stream().map(c -> substituteStatements(c)).collect(Collectors.toList())));
	}

	private PlusCalLHS tryConvertExpressionToLHS(TLAExpression subst) {
		if(subst instanceof TLAGeneralIdentifier) {
			TLAGeneralIdentifier substId = (TLAGeneralIdentifier)subst;
			if(!substId.getGeneralIdentifierPrefix().isEmpty()){
				ctx.error(new MacroAssignmentBadLHSIssue(subst));
				return null;
			}
			return new PlusCalLHS(
					subst.getLocation(),
					substId.getName().copy(),
					Collections.emptyList());
		}else if(subst instanceof TLABinOp) {
			TLABinOp substB = (TLABinOp)subst;
			if(!substB.getOperation().getValue().equals(".") || !substB.getPrefix().isEmpty()){
				ctx.error(new MacroAssignmentBadLHSIssue(subst));
				return null;
			}
			PlusCalLHS recLeft = tryConvertExpressionToLHS(substB.getLHS());
			PlusCalLHS recRight = tryConvertExpressionToLHS(substB.getRHS());
			if(recLeft == null || recRight == null) return null;

			// concatenate all sub-parts
			List<PlusCalLHSPart> parts = new ArrayList<>(recLeft.getParts());
			parts.add(PlusCalLHSPart.Dot(recRight.getId().getLocation(), recRight.getId()));
			parts.addAll(recRight.getParts());

			return new PlusCalLHS(
					subst.getLocation(),
					recLeft.getId(),
					parts);
		}else if(subst instanceof TLAFunctionCall) {
			TLAFunctionCall substF = (TLAFunctionCall)subst;
			PlusCalLHS recLeft = tryConvertExpressionToLHS(substF.getFunction());
			if(recLeft == null) return null;
			List<PlusCalLHSPart> parts = new ArrayList<>(recLeft.getParts());
			parts.add(PlusCalLHSPart.Index(substF.getLocation(), substF.getParams()));
			return new PlusCalLHS(subst.getLocation(), recLeft.getId(), parts);
		}else{
			ctx.error(new MacroAssignmentBadLHSIssue(subst));
			return null;
		}
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		List<PlusCalAssignmentPair> pairs = new ArrayList<>();
		for(PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {

			final PlusCalLHS lhs;
			if(macroArgs.containsKey(pair.getLhs().getId().getId())) {
				PlusCalLHS root = tryConvertExpressionToLHS(macroArgs.get(pair.getLhs().getId().getId()));
				List<PlusCalLHSPart> parts = new ArrayList<>(root.getParts());
				// add back any extra parts that were in the original LHS
				parts.addAll(pair.getLhs().getParts().stream().map(PlusCalLHSPart::copy).collect(Collectors.toList()));
				lhs = new PlusCalLHS(root.getLocation(), root.getId(), parts);
			}else{
				lhs = pair.getLhs().copy();
			}
			pairs.add(new PlusCalAssignmentPair(
					pair.getLocation(),
					lhs,
					pair.getRhs().accept(macroSubst)));
		}
		return Collections.singletonList(new PlusCalAssignment(
				plusCalAssignment.getLocation(), pairs));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		return Collections.singletonList(new PlusCalReturn(plusCalReturn.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalSkip skip) throws RuntimeException {
		return Collections.singletonList(new PlusCalSkip(skip.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		return Collections.singletonList(new PlusCalCall(
				plusCalCall.getLocation(), plusCalCall.getTarget(), plusCalCall.getArguments().stream().map(a -> a.accept(macroSubst)).collect(Collectors.toList())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalMacroCall macroCall) throws RuntimeException {
		if (recursionSet.contains(macroCall.getTarget())) {
			ctx.error(new RecursiveMacroCallIssue(macroCall));
		} else if (macros.containsKey(macroCall.getTarget())) {
			PlusCalMacro macro = macros.get(macroCall.getTarget());
			if (macro.getParams().size() != macroCall.getArguments().size()) {
				ctx.error(new MacroArgumentCountMismatchIssue(macroCall, macro));
			} else {
				Map<String, TLAExpression> argsMap = new HashMap<>();
				for (int i = 0; i < macroCall.getArguments().size(); ++i) {
					argsMap.put(macro.getParams().get(i), macroCall.getArguments().get(i));
				}
				Set<String> innerRecursionSet = new HashSet<>(recursionSet);
				innerRecursionSet.add(macro.getName());

				PlusCalMacroExpansionVisitor innerVisitor = new PlusCalMacroExpansionVisitor(ctx.withContext(new ExpandingMacroCall(macroCall)), macros, innerRecursionSet, argsMap);
				List<PlusCalStatement> statements = new ArrayList<>();
				for (PlusCalStatement stmt : macro.getBody()) {
					statements.addAll(stmt.accept(innerVisitor));
				}
				return statements;
			}
		} else {
			ctx.error(new UnresolvableMacroCallIssue(macroCall));
		}
		return Collections.singletonList(new PlusCalSkip(macroCall.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWith with) throws RuntimeException {
		return Collections.singletonList(new PlusCalWith(
				with.getLocation(),
				with.getVariables().stream().map(v -> {
					if (macroArgs.containsKey(v.getName())) {
						// TODO: error reporting in this case?
					}
					return new PlusCalVariableDeclaration(v.getLocation(), v.getName(),
							v.isSet(), v.getValue().accept(macroSubst));
				}).collect(Collectors.toList()),
				substituteStatements(with.getBody())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		return Collections.singletonList(new PlusCalPrint(plusCalPrint.getLocation(), plusCalPrint.getValue().accept(macroSubst)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		return Collections.singletonList(new PlusCalAssert(plusCalAssert.getLocation(), plusCalAssert.getCondition().accept(macroSubst)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		return Collections.singletonList(new PlusCalAwait(plusCalAwait.getLocation(), plusCalAwait.getCondition().accept(macroSubst)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		return Collections.singletonList(new PlusCalGoto(plusCalGoto.getLocation(), plusCalGoto.getTarget()));
	}

}
