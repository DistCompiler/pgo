package pgo.trans.intermediate;

import pgo.model.golang.*;
import pgo.model.pcal.*;
import pgo.model.pcal.Assignment;
import pgo.model.pcal.Call;
import pgo.model.pcal.If;
import pgo.model.pcal.Return;
import pgo.model.pcal.Statement;
import pgo.model.pcal.StatementVisitor;
import pgo.model.pcal.VariableDeclaration;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.type.PGoType;
import pgo.scope.UID;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class PlusCalStatementCodeGenVisitor extends StatementVisitor<Void, RuntimeException> {

	private BlockBuilder builder;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;

	public PlusCalStatementCodeGenVisitor(BlockBuilder builder, DefinitionRegistry registry,
			Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {
		this.builder = builder;
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
	}

	@Override
	public Void visit(LabeledStatements labeledStatements) throws RuntimeException {
		builder.labelIsUnique(labeledStatements.getLabel().getName());
		for(Statement stmt : labeledStatements.getStatements()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(While while1) throws RuntimeException {
		try(BlockBuilder fb = builder.forLoop(
				while1.getCondition().accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy)))){
			for(Statement stmt : while1.getBody()) {
				stmt.accept(new PlusCalStatementCodeGenVisitor(fb, registry, typeMap, globalStrategy));
			}
		}
		return null;
	}

	@Override
	public Void visit(If if1) throws RuntimeException {
		Expression condition = if1.getCondition().accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
		try(IfBuilder b = builder.ifStmt(condition)){
			try(BlockBuilder yes = b.whenTrue()){
				for(Statement stmt : if1.getYes()) {
					stmt.accept(new PlusCalStatementCodeGenVisitor(yes, registry, typeMap, globalStrategy));
				}
			}
			try(BlockBuilder no = b.whenFalse()){
				for(Statement stmt : if1.getNo()) {
					stmt.accept(new PlusCalStatementCodeGenVisitor(no, registry, typeMap, globalStrategy));
				}
			}
		}
		return null;
	}

	@Override
	public Void visit(Either either) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Assignment assignment) throws RuntimeException {
		List<Expression> lhs = new ArrayList<>();
		List<Expression> rhs = new ArrayList<>();
		List<GlobalVariableStrategy.GlobalVariableWrite> lhsWrites = new ArrayList<>();
		for(AssignmentPair pair : assignment.getPairs()) {
			GlobalVariableStrategy.GlobalVariableWrite lhsWrite = pair.getLhs().accept(
					new TLAExpressionAssignmentLHSCodeGenVisitor(builder, registry, typeMap, globalStrategy));
			lhsWrites.add(lhsWrite);
			lhs.add(lhsWrite.getValueSink(builder));
			rhs.add(pair.getRhs().accept(
					new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy)));
		}
		builder.assign(lhs, rhs);
		for(GlobalVariableStrategy.GlobalVariableWrite lhsWrite : lhsWrites) {
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
		builder.addStatement(new ExpressionStatement(new pgo.model.golang.Call(
				new VariableName(call.getTarget()),
				call.getArguments().stream()
						.map(a ->a.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy)))
						.collect(Collectors.toList()))));
		return null;
	}

	@Override
	public Void visit(MacroCall macroCall) throws RuntimeException {
		throw new RuntimeException("unreachable");
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
			statement.accept(new PlusCalStatementCodeGenVisitor(builder, registry, typeMap, globalStrategy));
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
				globalStrategy.awaitFailure().write(yes, cond);
			}
		}
		return null;
	}

	@Override
	public Void visit(Goto goto1) throws RuntimeException {
		builder.goTo(new LabelName(goto1.getTarget()));
		return null;
	}
}
