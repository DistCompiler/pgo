package pgo.trans.intermediate;

import java.util.Collections;
import java.util.Map;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.golang.IfBuilder;
import pgo.model.pcal.Assert;
import pgo.model.pcal.Assignment;
import pgo.model.pcal.Await;
import pgo.model.pcal.Call;
import pgo.model.pcal.Either;
import pgo.model.pcal.Goto;
import pgo.model.pcal.If;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.MacroCall;
import pgo.model.pcal.Print;
import pgo.model.pcal.Return;
import pgo.model.pcal.Skip;
import pgo.model.pcal.Statement;
import pgo.model.pcal.StatementVisitor;
import pgo.model.pcal.While;
import pgo.model.pcal.With;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class PlusCalStatementSingleThreadedCodeGenVisitor extends StatementVisitor<Void, RuntimeException> {

	private BlockBuilder builder;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;

	public PlusCalStatementSingleThreadedCodeGenVisitor(BlockBuilder builder, DefinitionRegistry registry, Map<UID, PGoType> typeMap) {
		this.builder = builder;
		this.registry = registry;
		this.typeMap = typeMap;
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
				while1.getCondition().accept(new TLAExpressionSingleThreadedCodeGenVisitor(builder, registry, typeMap)))){
			for(Statement stmt : while1.getBody()) {
				stmt.accept(new PlusCalStatementSingleThreadedCodeGenVisitor(fb, registry, typeMap));
			}
		}
		return null;
	}

	@Override
	public Void visit(If if1) throws RuntimeException {
		Expression condition = if1.getCondition().accept(new TLAExpressionSingleThreadedCodeGenVisitor(builder, registry, typeMap));
		try(IfBuilder b = builder.ifStmt(condition)){
			try(BlockBuilder yes = b.whenTrue()){
				for(Statement stmt : if1.getYes()) {
					stmt.accept(new PlusCalStatementSingleThreadedCodeGenVisitor(yes, registry, typeMap));
				}
			}
			try(BlockBuilder no = b.whenFalse()){
				for(Statement stmt : if1.getNo()) {
					stmt.accept(new PlusCalStatementSingleThreadedCodeGenVisitor(no, registry, typeMap));
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
		builder.assign(
				Collections.singletonList(
						assignment.getLHS().accept(new TLAExpressionSingleThreadedCodeGenVisitor(builder, registry, typeMap))),
				assignment.getRHS().accept(new TLAExpressionSingleThreadedCodeGenVisitor(builder, registry, typeMap)));
		return null;
	}

	@Override
	public Void visit(Return return1) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Skip skip) throws RuntimeException {
		// nothing to do here
		return null;
	}

	@Override
	public Void visit(Call call) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(MacroCall macroCall) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(With with) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Print print) throws RuntimeException {
		builder.print(print.getValue().accept(
				new TLAExpressionSingleThreadedCodeGenVisitor(builder, registry, typeMap)));
		return null;
	}

	@Override
	public Void visit(Assert assert1) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Await await) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Goto goto1) throws RuntimeException {
		throw new RuntimeException("TODO");
	}
}
