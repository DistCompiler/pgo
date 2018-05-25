package pgo.formatters;

import java.io.IOException;

import pgo.model.pcal.Algorithm;
import pgo.model.pcal.AssignmentPair;
import pgo.model.pcal.Label;
import pgo.model.pcal.Macro;
import pgo.model.pcal.NodeVisitor;
import pgo.model.pcal.PcalProcess;
import pgo.model.pcal.Procedure;
import pgo.model.pcal.Processes;
import pgo.model.pcal.Statement;
import pgo.model.pcal.VariableDecl;

public class NodeFormattingVisitor extends NodeVisitor<Void, IOException> {

	private IndentingWriter out;

	public NodeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(Algorithm algorithm) throws IOException {
		// TODO
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Processes processes) throws IOException {
		// TODO
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Statement statement) throws IOException {
		// TODO
		throw new RuntimeException("TODO");
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
			throw new RuntimeException("unreachable");
		}
		out.write(label.getName());
		out.write(":");
		return null;
	}

	@Override
	public Void visit(Macro macro) throws IOException {
		// TODO
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(PcalProcess pcalProcess) throws IOException {
		// TODO
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Procedure procedure) throws IOException {
		// TODO
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(VariableDecl variableDecl) throws IOException {
		out.write(variableDecl.getName());
		if(variableDecl.isSet()) {
			out.write(" \\in ");
		}else {
			out.write(" = ");
		}
		variableDecl.getValue().accept(new PGoTLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(AssignmentPair assignmentPair) throws IOException {
		throw new RuntimeException("TODO");
	}

}
