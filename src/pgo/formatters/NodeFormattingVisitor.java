package pgo.formatters;

import java.io.IOException;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.AssignmentPair;
import pgo.model.pcal.Label;
import pgo.model.pcal.Macro;
import pgo.model.pcal.NodeVisitor;
import pgo.model.pcal.PcalProcess;
import pgo.model.pcal.Procedure;
import pgo.model.pcal.Processes;
import pgo.model.pcal.Statement;
import pgo.model.pcal.VariableDeclaration;

public class NodeFormattingVisitor extends NodeVisitor<Void, IOException> {

	private IndentingWriter out;

	public NodeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(Algorithm algorithm) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(Processes processes) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(Statement statement) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(Label label) throws IOException {
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
	public Void visit(Macro macro) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(PcalProcess pcalProcess) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(Procedure procedure) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(VariableDeclaration variableDeclaration) throws IOException {
		out.write(variableDeclaration.getName().getValue());
		if(variableDeclaration.isSet()) {
			out.write(" \\in ");
		}else {
			out.write(" = ");
		}
		variableDeclaration.getValue().accept(new PGoTLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(AssignmentPair assignmentPair) throws IOException {
		throw new TODO();
	}

}
