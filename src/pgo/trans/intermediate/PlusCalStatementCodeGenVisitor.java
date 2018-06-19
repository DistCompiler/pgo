package pgo.trans.intermediate;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.*;
import pgo.model.pcal.*;
import pgo.model.pcal.Assignment;
import pgo.model.pcal.Call;
import pgo.model.pcal.If;
import pgo.model.pcal.Label;
import pgo.model.pcal.Return;
import pgo.model.pcal.Statement;
import pgo.model.pcal.StatementVisitor;
import pgo.model.pcal.VariableDeclaration;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.passes.codegen.CodeGenUtil;
import pgo.trans.passes.codegen.CriticalSectionTracker;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.stream.Collectors;

public class PlusCalStatementCodeGenVisitor extends StatementVisitor<Void, RuntimeException> {
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;
	private UID processUID;
	private BlockBuilder builder;
	private CriticalSectionTracker criticalSectionTracker;

	private PlusCalStatementCodeGenVisitor(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                       GlobalVariableStrategy globalStrategy, UID processUID, BlockBuilder builder,
	                                       CriticalSectionTracker criticalSectionTracker) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
		this.processUID = processUID;
		this.builder = builder;
		this.criticalSectionTracker = criticalSectionTracker;
	}

	public PlusCalStatementCodeGenVisitor(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                      GlobalVariableStrategy globalStrategy, UID processUID, BlockBuilder builder) {
		this(registry, typeMap, globalStrategy, processUID, builder, new CriticalSectionTracker(registry, processUID, globalStrategy));
	}

	@Override
	public Void visit(LabeledStatements labeledStatements) throws RuntimeException {
		Label label = labeledStatements.getLabel();
		criticalSectionTracker.start(builder, label.getUID(), new LabelName(label.getName()));
		for (Statement stmt : labeledStatements.getStatements()) {
			stmt.accept(this);
		}
		criticalSectionTracker.end(builder);
		return null;
	}

	@Override
	public Void visit(While while1) throws RuntimeException {
		// note: here we don't directly compile the loop condition into the Go loop condition due to
		// difficulties with intermediate variables and critical sections (if the condition is false
		// we may have to end the critical section after checking the condition)
		CriticalSectionTracker loopConditionCriticalSectionTracker = criticalSectionTracker.copy();
		Consumer<BlockBuilder> actionAtLoopEnd = criticalSectionTracker.actionAtLoopEnd();
		try (BlockBuilder fb = builder.forLoop(null)) {
			try(IfBuilder loopCondition = fb.ifStmt(CodeGenUtil.invertCondition(
					fb, registry, typeMap, globalStrategy, while1.getCondition()))) {
				try (BlockBuilder loopConditionBody = loopCondition.whenTrue()) {
					// if there are labels inside the loop, ensure that we end the critical section
					// when the loop condition fails as there must be a new label after the loop
					// if there are no labels inside the loop however, the critical section from before continues
					// uninterrupted
					if (while1.accept(new PlusCalStatementContainsLabelVisitor())) {
						loopConditionCriticalSectionTracker.end(loopConditionBody);
					}
					loopConditionBody.addStatement(new Break());
				}
			}
			for (Statement statement : while1.getBody()) {
				statement.accept(new PlusCalStatementCodeGenVisitor(
						registry, typeMap, globalStrategy, processUID, fb, criticalSectionTracker));
			}
			actionAtLoopEnd.accept(fb);
		}
		return null;
	}

	@Override
	public Void visit(If if1) throws RuntimeException {
		Expression condition = if1.getCondition().accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
		boolean containsLabels = if1.accept(new PlusCalStatementContainsLabelVisitor());
		try (IfBuilder b = builder.ifStmt(condition)) {
			CriticalSectionTracker noTracker = criticalSectionTracker.copy();
			try (BlockBuilder yes = b.whenTrue()) {
				for (Statement stmt : if1.getYes()) {
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
			try (BlockBuilder no = b.whenFalse()) {
				for (Statement stmt : if1.getNo()) {
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
	public Void visit(Either either) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Void visit(Assignment assignment) throws RuntimeException {
		List<Expression> lhs = new ArrayList<>();
		List<Expression> rhs = new ArrayList<>();
		List<GlobalVariableStrategy.GlobalVariableWrite> lhsWrites = new ArrayList<>();
		for (AssignmentPair pair : assignment.getPairs()) {
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
	public Void visit(Return return1) throws RuntimeException {
		builder.addStatement(new pgo.model.golang.Return(Collections.emptyList()));
		return null;
	}

	@Override
	public Void visit(Skip skip) throws RuntimeException {
		// nothing to do here
		return null;
	}

	@Override
	public Void visit(Call call) throws RuntimeException {
		List<Expression> arguments = new ArrayList<>();
		List<PGoTLAExpression> args = call.getArguments();
		for (int i = 0; i < args.size(); i++) {
			PGoTLAExpression arg = args.get(i);
			Expression e = arg.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
			arguments.add(builder.varDecl("arg" + Integer.toString(i + 1), e));
		}
		// the critical section ends here because the procedure has to have a label on the first line of its body
		criticalSectionTracker.end(builder);
		builder.addStatement(new ExpressionStatement(new pgo.model.golang.Call(
				new VariableName(call.getTarget()),
				arguments)));
		return null;
	}

	@Override
	public Void visit(MacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(With with) throws RuntimeException {
		// with statements with multiple declarations such as
		//     with (v1 = e1, v2 \in e2, v3 = e3)
		//         body
		// are structured as
		//     with (v1 = e1)
		//         with (v2 \in e2)
		//             with (v3 = e3)
		//                 body
		while (true) {
			VariableDeclaration decl = with.getVariable();
			Expression value = decl.getValue().accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
			if (decl.isSet()) {
				value = new Index(value, new IntLiteral(0));
			}
			builder.linkUID(decl.getUID(), builder.varDecl(decl.getName(), value));
			if (with.getBody().size() != 1 || !(with.getBody().get(0) instanceof With)) {
				break;
			}
			// flatten out the nested withs
			with = (With) with.getBody().get(0);
		}
		for (Statement statement : with.getBody()) {
			statement.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(Print print) throws RuntimeException {
		builder.print(print.getValue().accept(
				new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy)));
		return null;
	}

	@Override
	public Void visit(Assert assert1) throws RuntimeException {
		PGoTLAExpression cond = assert1.getCondition();
		try (IfBuilder ifBuilder = builder.ifStmt(CodeGenUtil.invertCondition(
				builder, registry, typeMap, globalStrategy, cond))) {
			try (BlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(new StringLiteral(cond.toString()));
			}
		}
		return null;
	}

	@Override
	public Void visit(Await await) throws RuntimeException {
		PGoTLAExpression cond = await.getCondition();
		try (IfBuilder ifBuilder = builder.ifStmt(CodeGenUtil.invertCondition(
				builder, registry, typeMap, globalStrategy, cond))) {
			try (BlockBuilder yes = ifBuilder.whenTrue()) {
				// fork out an execution path for aborting
				CriticalSectionTracker tracker = criticalSectionTracker.copy();
				tracker.abort(yes);
			}
		}
		return null;
	}

	@Override
	public Void visit(Goto goto1) throws RuntimeException {
		// fork out an execution path for this goto
		CriticalSectionTracker tracker = criticalSectionTracker.copy();
		// this critical section ends here
		tracker.end(builder);
		builder.goTo(new LabelName(goto1.getTarget()));
		// continue with the previous critical section
		return null;
	}
}
