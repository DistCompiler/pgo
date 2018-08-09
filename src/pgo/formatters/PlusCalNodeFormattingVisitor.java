package pgo.formatters;

import java.io.IOException;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.pcal.*;
import pgo.model.pcal.PlusCalLabel;

public class PlusCalNodeFormattingVisitor extends PlusCalNodeVisitor<Void, IOException> {

	private IndentingWriter out;

	public PlusCalNodeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(PlusCalAlgorithm plusCalAlgorithm) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(PlusCalProcesses processes) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(PlusCalStatement statement) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(PlusCalLabel label) throws IOException {
		switch(label.getModifier()) {
		case MINUS:
			out.write("-");
			break;
		case NONE:
			// pass
			break;
		case PLUS:
			out.write("+");
			break;
		default:
			throw new Unreachable();
		}
		out.write(label.getName());
		out.write(":");
		return null;
	}

	@Override
	public Void visit(PlusCalMacro macro) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(PlusCalProcess plusCalProcess) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(PlusCalProcedure procedure) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(PlusCalVariableDeclaration variableDeclaration) throws IOException {
		out.write(variableDeclaration.getName().getValue());
		if(variableDeclaration.isSet()) {
			out.write(" \\in ");
		}else {
			out.write(" = ");
		}
		variableDeclaration.getValue().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(PlusCalAssignmentPair plusCalAssignmentPair) throws IOException {
		throw new TODO();
	}

}
