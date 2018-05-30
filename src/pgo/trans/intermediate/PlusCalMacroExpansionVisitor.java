package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import pgo.errors.IssueContext;
import pgo.model.pcal.Assert;
import pgo.model.pcal.Assignment;
import pgo.model.pcal.AssignmentPair;
import pgo.model.pcal.Await;
import pgo.model.pcal.Call;
import pgo.model.pcal.Either;
import pgo.model.pcal.Goto;
import pgo.model.pcal.If;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.Macro;
import pgo.model.pcal.MacroCall;
import pgo.model.pcal.Print;
import pgo.model.pcal.Return;
import pgo.model.pcal.Skip;
import pgo.model.pcal.Statement;
import pgo.model.pcal.StatementVisitor;
import pgo.model.pcal.VariableDeclaration;
import pgo.model.pcal.While;
import pgo.model.pcal.With;
import pgo.model.tla.PGoTLAExpression;

public class PlusCalMacroExpansionVisitor extends StatementVisitor<List<Statement>, RuntimeException> {

	private IssueContext ctx;
	private Map<String, Macro> macros;
	private Set<String> recursionSet;
	private Map<String, PGoTLAExpression> macroArgs;
	private TLAExpressionMacroSubstitutionVisitor macroSubst;

	public PlusCalMacroExpansionVisitor(IssueContext ctx, Map<String, Macro> macros, Set<String> recursionSet, Map<String, PGoTLAExpression> macroArgs) {
		this.ctx = ctx;
		this.macros = macros;
		this.recursionSet = recursionSet;
		this.macroArgs = macroArgs;
		this.macroSubst = new TLAExpressionMacroSubstitutionVisitor(ctx, macroArgs);
	}

	private List<Statement> substituteStatements(List<Statement> stmts){
		List<Statement> result = new ArrayList<>();
		for(Statement stmt : stmts) {
			result.addAll(stmt.accept(this));
		}
		return result;
	}

	@Override
	public List<Statement> visit(LabeledStatements labeledStatements) throws RuntimeException {
		return Collections.singletonList(new LabeledStatements(labeledStatements.getLocation(),
				labeledStatements.getLabel(), substituteStatements(labeledStatements.getStatements())));
	}

	@Override
	public List<Statement> visit(While while1) throws RuntimeException {
		return Collections.singletonList(new While(
				while1.getLocation(), while1.getCondition().accept(macroSubst), substituteStatements(while1.getBody())));
	}

	@Override
	public List<Statement> visit(If if1) throws RuntimeException {
		return Collections.singletonList(new If(
				if1.getLocation(), if1.getCondition().accept(macroSubst), substituteStatements(if1.getYes()), substituteStatements(if1.getNo())));
	}

	@Override
	public List<Statement> visit(Either either) throws RuntimeException {
		return Collections.singletonList(new Either(
				either.getLocation(), either.getCases().stream().map(c -> substituteStatements(c)).collect(Collectors.toList())));
	}

	@Override
	public List<Statement> visit(Assignment assignment) throws RuntimeException {
		List<AssignmentPair> pairs = new ArrayList<>();
		for(AssignmentPair pair : assignment.getPairs()) {
			pairs.add(new AssignmentPair(
					pair.getLocation(),
					pair.getLhs().accept(macroSubst),
					pair.getRhs().accept(macroSubst)));
		}
		return Collections.singletonList(new Assignment(
				assignment.getLocation(), pairs));
	}

	@Override
	public List<Statement> visit(Return return1) throws RuntimeException {
		return Collections.singletonList(new Return(return1.getLocation()));
	}

	@Override
	public List<Statement> visit(Skip skip) throws RuntimeException {
		return Collections.singletonList(new Skip(skip.getLocation()));
	}

	@Override
	public List<Statement> visit(Call call) throws RuntimeException {
		return Collections.singletonList(new Call(
				call.getLocation(), call.getTarget(), call.getArguments().stream().map(a -> a.accept(macroSubst)).collect(Collectors.toList())));
	}

	@Override
	public List<Statement> visit(MacroCall macroCall) throws RuntimeException {
		if(recursionSet.contains(macroCall.getTarget())) {
			ctx.error(new RecursiveMacroCallIssue(macroCall));
		}else if(macros.containsKey(macroCall.getTarget())){
			Macro macro = macros.get(macroCall.getTarget());
			if(macro.getParams().size() != macroCall.getArguments().size()) {
				ctx.error(new MacroArgumentCountMismatchIssue(macroCall, macro));
			}else {
				Map<String, PGoTLAExpression> argsMap = new HashMap<>();
				for(int i = 0; i < macroCall.getArguments().size(); ++i) {
					argsMap.put(macro.getParams().get(i), macroCall.getArguments().get(i));
				}
				Set<String> innerRecursionSet = new HashSet<>(recursionSet);
				innerRecursionSet.add(macro.getName());

				PlusCalMacroExpansionVisitor innerVisitor = new PlusCalMacroExpansionVisitor(ctx.withContext(new ExpandingMacroCall(macroCall)), macros, innerRecursionSet, argsMap);
				List<Statement> statements = new ArrayList<>();
				for(Statement stmt : macro.getBody()) {
					statements.addAll(stmt.accept(innerVisitor));
				}
				return statements;
			}
		}else {
			ctx.error(new UnresolvableMacroCallIssue(macroCall));
		}
		return Collections.singletonList(new Skip(macroCall.getLocation()));
	}

	@Override
	public List<Statement> visit(With with) throws RuntimeException {
		VariableDeclaration oldVariable = with.getVariable();
		if(macroArgs.containsKey(oldVariable.getName())) {
			// TODO: error reporting in this case?
		}
		VariableDeclaration newVariable = new VariableDeclaration(oldVariable.getLocation(), oldVariable.getName(),
				oldVariable.isSet(), oldVariable.getValue().accept(macroSubst));
		return Collections.singletonList(new With(with.getLocation(), newVariable, substituteStatements(with.getBody())));
	}

	@Override
	public List<Statement> visit(Print print) throws RuntimeException {
		return Collections.singletonList(new Print(print.getLocation(), print.getValue().accept(macroSubst)));
	}

	@Override
	public List<Statement> visit(Assert assert1) throws RuntimeException {
		return Collections.singletonList(new Assert(assert1.getLocation(), assert1.getCondition().accept(macroSubst)));
	}

	@Override
	public List<Statement> visit(Await await) throws RuntimeException {
		return Collections.singletonList(new Await(await.getLocation(), await.getCondition().accept(macroSubst)));
	}

	@Override
	public List<Statement> visit(Goto goto1) throws RuntimeException {
		return Collections.singletonList(new Goto(goto1.getLocation(), goto1.getTarget()));
	}

}
