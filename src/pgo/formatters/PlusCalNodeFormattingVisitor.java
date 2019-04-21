package pgo.formatters;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.pcal.*;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.tla.TLAUnit;

import java.io.IOException;
import java.util.List;

public class PlusCalNodeFormattingVisitor extends PlusCalNodeVisitor<Void, IOException> {

	private IndentingWriter out;

	public PlusCalNodeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	boolean writeVariableDeclarations(String prefix, List<PlusCalVariableDeclaration> declarations, String postfix)
			throws IOException {
		if (declarations.size() > 0) {
			out.write(prefix);
			for (int i = 0; i < declarations.size(); i++) {
				PlusCalVariableDeclaration declaration = declarations.get(i);
				if (i != 0) {
					out.write(", ");
				}
				declaration.accept(this);
			}
			out.write(postfix);
			return true;
		}
		return false;
	}

	@Override
	public Void visit(PlusCalAlgorithm plusCalAlgorithm) throws IOException {
		out.write("--algorithm ");
		out.write(plusCalAlgorithm.getName().getValue());
		out.write(" {");
		out.newLine();
		try (IndentingWriter.Indent ignored = out.indent()) {
			if (writeVariableDeclarations("variables ", plusCalAlgorithm.getVariables(), ";")) {
				out.newLine();
			}

			List<TLAUnit> units = plusCalAlgorithm.getUnits();
			if (units.size() > 0) {
				out.write("define {");
				out.newLine();
				try (IndentingWriter.Indent ignored1 = out.indent()) {
					for (TLAUnit unit : plusCalAlgorithm.getUnits()) {
						unit.accept(new TLAUnitFormattingVisitor(out));
						out.newLine();
					}
				}
				out.write("}");
				out.newLine();
			}

			for (PlusCalProcedure procedure : plusCalAlgorithm.getProcedures()) {
				procedure.accept(this);
			}

			plusCalAlgorithm.getProcesses().accept(this);

		}
		out.write("}");
		// there should not be a newline after this to match the PlusCal parser
		return null;
	}

	@Override
	public Void visit(PlusCalProcesses processes) throws IOException {
		if (processes instanceof PlusCalSingleProcess) {
			PlusCalSingleProcess singleProcess = (PlusCalSingleProcess) processes;
			out.write("{");
			out.newLine();
			try (IndentingWriter.Indent ignored = out.indent()) {
				for (PlusCalStatement statement : singleProcess.getBody()) {
					statement.accept(this);
				}
			}
			out.newLine();
			out.write("}");
			out.newLine();
		} else {
			PlusCalMultiProcess multiProcess = (PlusCalMultiProcess) processes;
			for (PlusCalProcess process : multiProcess.getProcesses()) {
				process.accept(this);
			}
		}
		return null;
	}

	@Override
	public Void visit(PlusCalStatement statement) throws IOException {
		statement.accept(new PlusCalStatementFormattingVisitor(out));
		return null;
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
		if (plusCalProcess.getFairness() == PlusCalFairness.WEAK_FAIR) {
			out.write("fair ");
		} else if (plusCalProcess.getFairness() == PlusCalFairness.STRONG_FAIR) {
			out.write("fair+ ");
		}

		out.write("process (");
		plusCalProcess.getName().accept(this);
		out.write(")");
		out.newLine();

		if (writeVariableDeclarations("variables ", plusCalProcess.getVariables(), ";")) {
			out.newLine();
		}

		out.write("{");
		out.newLine();
		try (IndentingWriter.Indent ignored = out.indent()) {
			for (PlusCalStatement statement : plusCalProcess.getBody()) {
				statement.accept(this);
			}
		}
		out.newLine();
		out.write("}");
		out.newLine();
		return null;
	}

	@Override
	public Void visit(PlusCalProcedure procedure) throws IOException {
		out.write("procedure ");
		out.write(procedure.getName());
		out.write(" (");
		writeVariableDeclarations("", procedure.getParams(), "");
		out.write(")");
		out.newLine();
		if (writeVariableDeclarations("variables ", procedure.getVariables(), ";")) {
			out.newLine();
		}
		out.write("{");
        out.newLine();
		try (IndentingWriter.Indent ignored = out.indent()) {
			for (PlusCalStatement statement : procedure.getBody()) {
				statement.accept(this);
			}
		}
		out.newLine();
		out.write("}");
		out.newLine();
		return null;
	}

	@Override
	public Void visit(PlusCalVariableDeclaration variableDeclaration) throws IOException {
		out.write(variableDeclaration.getName().getValue());
		if (!(variableDeclaration.getValue() instanceof PlusCalDefaultInitValue)) {
			if (variableDeclaration.isSet()) {
				out.write(" \\in ");
			} else {
				out.write(" = ");
			}
			variableDeclaration.getValue().accept(new TLAExpressionFormattingVisitor(out));
		}
		return null;
	}

	@Override
	public Void visit(PlusCalAssignmentPair plusCalAssignmentPair) throws IOException {
		plusCalAssignmentPair.getLhs().accept(new TLAExpressionFormattingVisitor(out, true));
		out.write(" := ");
		plusCalAssignmentPair.getRhs().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

}
