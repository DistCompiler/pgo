package pgo.trans.intermediate;

import pgo.InternalCompilerError;
import pgo.Unreachable;
import pgo.model.pcal.*;

import javax.swing.plaf.nimbus.State;
import java.util.List;

public class PlusCalStatementContainsLabelVisitor extends StatementVisitor<Boolean, RuntimeException> {
	@Override
	public Boolean visit(LabeledStatements labeledStatements) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(While while1) throws RuntimeException {
		for(Statement stmt : while1.getBody()){
			if(stmt.accept(this)){
				return true;
			}
		}
		return false;
	}

	@Override
	public Boolean visit(If if1) throws RuntimeException {
		for(Statement stmt : if1.getYes()){
			if(stmt.accept(this)){
				return true;
			}
		}
		for(Statement stmt : if1.getNo()){
			if(stmt.accept(this)){
				return true;
			}
		}
		return false;
	}

	@Override
	public Boolean visit(Either either) throws RuntimeException {
		for(List<Statement> stmts : either.getCases()){
			for(Statement stmt : stmts){
				if(stmt.accept(this)){
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public Boolean visit(Assignment assignment) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Return return1) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Skip skip) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Call call) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(MacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Boolean visit(With with) throws RuntimeException {
		for(Statement stmt : with.getBody()){
			if(stmt.accept(this)){
				return true;
			}
		}
		return false;
	}

	@Override
	public Boolean visit(Print print) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Assert assert1) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Await await) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Goto goto1) throws RuntimeException {
		return false;
	}
}
