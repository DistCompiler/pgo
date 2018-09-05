package pgo.trans.passes.codegen;

import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalRead;
import pgo.model.mpcal.ModularPlusCalWrite;
import pgo.model.pcal.*;

import java.util.List;

public class PlusCalStatementContainsLabelVisitor extends PlusCalStatementVisitor<Boolean, RuntimeException> {
	@Override
	public Boolean visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		for(PlusCalStatement stmt : plusCalWhile.getBody()){
			if(stmt.accept(this)){
				return true;
			}
		}
		return false;
	}

	@Override
	public Boolean visit(PlusCalIf plusCalIf) throws RuntimeException {
		for(PlusCalStatement stmt : plusCalIf.getYes()){
			if(stmt.accept(this)){
				return true;
			}
		}
		for(PlusCalStatement stmt : plusCalIf.getNo()){
			if(stmt.accept(this)){
				return true;
			}
		}
		return false;
	}

	@Override
	public Boolean visit(PlusCalEither plusCalEither) throws RuntimeException {
		for(List<PlusCalStatement> stmts : plusCalEither.getCases()){
			for(PlusCalStatement stmt : stmts){
				if(stmt.accept(this)){
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public Boolean visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalSkip skip) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalCall plusCalCall) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Boolean visit(PlusCalWith with) throws RuntimeException {
		for(PlusCalStatement stmt : with.getBody()){
			if(stmt.accept(this)){
				return true;
			}
		}
		return false;
	}

	@Override
	public Boolean visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(ModularPlusCalRead modularPlusCalRead) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(ModularPlusCalWrite modularPlusCalWrite) throws RuntimeException {
		return false;
	}
}
