package pgo.trans.passes.codegen;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.GlobalVariableStrategy;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;

public class PlusCalStatementCodeGenVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;
	private UID processUID;
	private GoBlockBuilder builder;
	private CriticalSectionTracker criticalSectionTracker;

	private PlusCalStatementCodeGenVisitor(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                       GlobalVariableStrategy globalStrategy, UID processUID, GoBlockBuilder builder,
	                                       CriticalSectionTracker criticalSectionTracker) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
		this.processUID = processUID;
		this.builder = builder;
		this.criticalSectionTracker = criticalSectionTracker;
	}

	public PlusCalStatementCodeGenVisitor(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                      GlobalVariableStrategy globalStrategy, UID processUID, GoBlockBuilder builder) {
		this(registry, typeMap, globalStrategy, processUID, builder, new CriticalSectionTracker(registry, processUID, globalStrategy));
	}

	@Override
	public Void visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		PlusCalLabel label = labeledStatements.getLabel();
		criticalSectionTracker.start(builder, label.getUID(), new GoLabelName(label.getName()));
		for (PlusCalStatement stmt : labeledStatements.getStatements()) {
			stmt.accept(this);
		}
		criticalSectionTracker.end(builder);
		return null;
	}

	@Override
	public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		// note: here we don't directly compile the loop condition into the GoRoutineStatement loop condition due to
		// difficulties with intermediate variables and critical sections (if the condition is false
		// we may have to end the critical section after checking the condition)
		CriticalSectionTracker loopConditionCriticalSectionTracker = criticalSectionTracker.copy();
		Consumer<GoBlockBuilder> actionAtLoopEnd = criticalSectionTracker.actionAtLoopEnd();
		try (GoBlockBuilder fb = builder.forLoop(null)) {
			try(GoIfBuilder loopCondition = fb.ifStmt(CodeGenUtil.invertCondition(
					fb, registry, typeMap, globalStrategy, plusCalWhile.getCondition()))) {
				try (GoBlockBuilder loopConditionBody = loopCondition.whenTrue()) {
					// if there are labels inside the loop, ensure that we end the critical section
					// when the loop condition fails as there must be a new label after the loop
					// if there are no labels inside the loop however, the critical section from before continues
					// uninterrupted
					if (plusCalWhile.accept(new PlusCalStatementContainsLabelVisitor())) {
						loopConditionCriticalSectionTracker.end(loopConditionBody);
					}
					loopConditionBody.addStatement(new GoBreak());
				}
			}
			for (PlusCalStatement statement : plusCalWhile.getBody()) {
				statement.accept(new PlusCalStatementCodeGenVisitor(
						registry, typeMap, globalStrategy, processUID, fb, criticalSectionTracker));
			}
			actionAtLoopEnd.accept(fb);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
		GoExpression condition = plusCalIf.getCondition().accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
		boolean containsLabels = plusCalIf.accept(new PlusCalStatementContainsLabelVisitor());
		try (GoIfBuilder b = builder.ifStmt(condition)) {
			CriticalSectionTracker noTracker = criticalSectionTracker.copy();
			try (GoBlockBuilder yes = b.whenTrue()) {
				for (PlusCalStatement stmt : plusCalIf.getYes()) {
					stmt.accept(new PlusCalStatementCodeGenVisitor(
							registry, typeMap, globalStrategy, processUID, yes, criticalSectionTracker));
				}
				// if an if statement contains a label, then the statement(s) after it must be labeled
				// if the statement after must be labeled, we know this critical section ends here (and
				// may be different between true and false branches). otherwise, leave the critical section
				// as is
				if (containsLabels) {
					criticalSectionTracker.end(yes);
				}
			}
			try (GoBlockBuilder no = b.whenFalse()) {
				for (PlusCalStatement stmt : plusCalIf.getNo()) {
					stmt.accept(new PlusCalStatementCodeGenVisitor(
							registry, typeMap, globalStrategy, processUID, no, noTracker));
				}
				// see description for true case
				if (containsLabels) {
					noTracker.end(no);
				}
			}
			criticalSectionTracker.checkCompatibility(noTracker);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalEither plusCalEither) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		List<GoExpression> lhs = new ArrayList<>();
		List<GoExpression> rhs = new ArrayList<>();
		List<GlobalVariableStrategy.GlobalVariableWrite> lhsWrites = new ArrayList<>();
		for (PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
			GlobalVariableStrategy.GlobalVariableWrite lhsWrite = pair.getLhs().accept(
					new TLAExpressionAssignmentLHSCodeGenVisitor(builder, registry, typeMap, globalStrategy));
			lhsWrites.add(lhsWrite);
			lhs.add(lhsWrite.getValueSink(builder));
			rhs.add(pair.getRhs().accept(
					new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy)));
		}
		builder.assign(lhs, rhs);
		for (GlobalVariableStrategy.GlobalVariableWrite lhsWrite : lhsWrites) {
			lhsWrite.writeAfter(builder);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		builder.addStatement(new GoReturn(Collections.emptyList()));
		return null;
	}

	@Override
	public Void visit(PlusCalSkip skip) throws RuntimeException {
		// nothing to do here
		return null;
	}

	@Override
	public Void visit(PlusCalCall plusCalCall) throws RuntimeException {
		List<GoExpression> arguments = new ArrayList<>();
		List<TLAExpression> args = plusCalCall.getArguments();
		for (int i = 0; i < args.size(); i++) {
			TLAExpression arg = args.get(i);
			GoExpression e = arg.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
			arguments.add(builder.varDecl("arg" + Integer.toString(i + 1), e));
		}
		// the critical section ends here because the procedure has to have a label on the first line of its body
		criticalSectionTracker.end(builder);
		builder.addStatement(new GoExpressionStatement(new GoCall(
				new GoVariableName(plusCalCall.getTarget()),
				arguments)));
		return null;
	}

	@Override
	public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(PlusCalWith with) throws RuntimeException {
		for(PlusCalVariableDeclaration decl : with.getVariables()) {
			GoExpression value = decl.getValue().accept(
					new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
			if (decl.isSet()) {
				value = new GoIndexExpression(value, new GoIntLiteral(0));
			}
			builder.linkUID(decl.getUID(), builder.varDecl(decl.getName().getValue(), value));
		}
		for (PlusCalStatement statement : with.getBody()) {
			statement.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		builder.print(plusCalPrint.getValue().accept(
				new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy)));
		return null;
	}

	@Override
	public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		TLAExpression cond = plusCalAssert.getCondition();
		try (GoIfBuilder ifBuilder = builder.ifStmt(CodeGenUtil.invertCondition(
				builder, registry, typeMap, globalStrategy, cond))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(new GoStringLiteral(cond.toString()));
			}
		}
		return null;
	}

	@Override
	public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		TLAExpression cond = plusCalAwait.getCondition();
		try (GoIfBuilder ifBuilder = builder.ifStmt(CodeGenUtil.invertCondition(
				builder, registry, typeMap, globalStrategy, cond))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				// fork out an execution path for aborting
				CriticalSectionTracker tracker = criticalSectionTracker.copy();
				tracker.abort(yes);
			}
		}
		return null;
	}

	@Override
	public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		// fork out an execution path for this goto
		CriticalSectionTracker tracker = criticalSectionTracker.copy();
		// this critical section ends here
		tracker.end(builder);
		builder.goTo(new GoLabelName(plusCalGoto.getTarget()));
		// continue with the previous critical section
		return null;
	}
}
