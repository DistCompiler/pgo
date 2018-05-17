package pgo.trans.intermediate;

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
import pgo.model.pcal.StatementVisitor;
import pgo.model.pcal.While;
import pgo.model.pcal.With;

public class PlusCalStatementScopingVisitor extends StatementVisitor<Void, RuntimeException> {
	
	PlusCalScopeBuilder builder;
	
	public PlusCalStatementScopingVisitor(PlusCalScopeBuilder builder) {
		this.builder = builder;
	}

	@Override
	public Void visit(LabeledStatements labeledStatements) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(While while1) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(If if1) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Either either) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Assignment assignment) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Return return1) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Skip skip) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Call call) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(MacroCall macroCall) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(With with) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Print print) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Assert assert1) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Await await) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Goto goto1) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

}
