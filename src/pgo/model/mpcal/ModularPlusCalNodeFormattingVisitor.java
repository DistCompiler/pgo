package pgo.model.mpcal;

import pgo.Unreachable;
import pgo.formatters.IndentingWriter;
import pgo.formatters.PlusCalNodeFormattingVisitor;
import pgo.formatters.TLAExpressionFormattingVisitor;
import pgo.formatters.TLAUnitFormattingVisitor;
import pgo.model.pcal.*;
import pgo.model.tla.TLAUnit;

import java.io.IOException;
import java.util.stream.Collectors;

public class ModularPlusCalNodeFormattingVisitor extends ModularPlusCalNodeVisitor<Void, IOException> {
	private IndentingWriter out;

	public ModularPlusCalNodeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(ModularPlusCalBlock modularPlusCalBlock) throws IOException {
		out.write("--mpcal ");
		out.write(modularPlusCalBlock.name().getId());
		out.write(" {");

		try(IndentingWriter.Indent i_ = out.indent()) {

			if(!modularPlusCalBlock.getUnits().isEmpty()) {
				out.newLine();
				out.write("define {");
				try(IndentingWriter.Indent ii_ = out.indent()) {
					for(TLAUnit unit: modularPlusCalBlock.getUnits()) {
						out.newLine();
						unit.accept(new TLAUnitFormattingVisitor(out));
					}
				}
				out.newLine();
				out.write("}");
			}

			for(PlusCalMacro macro: modularPlusCalBlock.getMacros()) {
				out.newLine();
				macro.accept(new PlusCalNodeFormattingVisitor(out));
			}
			for(PlusCalProcedure proc: modularPlusCalBlock.getProcedures()) {
				out.newLine();
				proc.accept(new PlusCalNodeFormattingVisitor(out));
			}
			for(ModularPlusCalMappingMacro mm: modularPlusCalBlock.getMappingMacros()) {
				out.newLine();
				mm.accept(this);
			}
			for(ModularPlusCalArchetype arch: modularPlusCalBlock.getArchetypes()) {
				out.newLine();
				arch.accept(this);
			}
			if(!modularPlusCalBlock.getVariables().isEmpty()) {
				out.newLine();
			}
			new PlusCalNodeFormattingVisitor(out).writeVariableDeclarations("variables ", modularPlusCalBlock.getVariables(), ";");
			for(ModularPlusCalInstance inst: modularPlusCalBlock.getInstances()) {
				out.newLine();
				inst.accept(this);
			}
			out.newLine();
			modularPlusCalBlock.getProcesses().accept(new PlusCalNodeFormattingVisitor(out));
		}
		out.newLine();
		out.write("}");

		return null;
	}

	@Override
	public Void visit(ModularPlusCalArchetype modularPlusCalArchetype) throws IOException {
		out.write("archetype ");
		out.write(modularPlusCalArchetype.getName());
		out.write("(");
		out.write(modularPlusCalArchetype
				.getParams()
				.stream()
				.map(arg -> (arg.isRef() ? "ref " : "") + arg.getName().getId())
				.collect(Collectors.joining(", ")));
		out.write(")");
		if (modularPlusCalArchetype.getVariables().isEmpty()) {
			out.write(" ");
		} else {
			out.write("variables ");
			out.write(modularPlusCalArchetype
					.getVariables()
					.stream()
					.map(v -> v.getName() + (v.isSet() ? " \\in " : " = ") + v.getValue().toString())
					.collect(Collectors.joining(", ")));
			out.write(";");
			out.newLine();
		}
		out.write("{");
		// TODO write body
		out.write("}");
		return null;
	}

	@Override
	public Void visit(ModularPlusCalInstance modularPlusCalInstance) throws IOException {
		if (modularPlusCalInstance.getFairness() == PlusCalFairness.WEAK_FAIR) {
			out.write("fair ");
		} else if (modularPlusCalInstance.getFairness() == PlusCalFairness.STRONG_FAIR) {
			out.write("fair+ ");
		}

		out.write("process (");
		modularPlusCalInstance.getName().accept(new PlusCalNodeFormattingVisitor(out));
		out.write(")");

		out.write(" == instance ");
		out.write(modularPlusCalInstance.getTarget());

		out.write("(");
		TLAExpressionFormattingVisitor formatter = new TLAExpressionFormattingVisitor(out);
		for (int i = 0; i < modularPlusCalInstance.getArguments().size(); i++) {
			if (i > 0) {
				out.write(", ");
			}

			modularPlusCalInstance.getArguments().get(i).accept(formatter);
		}
		out.write(")");

		for (ModularPlusCalMapping mapping : modularPlusCalInstance.getMappings()) {
			out.newLine();
			out.write("mapping ");
			if (mapping.getVariable() instanceof ModularPlusCalMappingVariableName) {
				out.write(((ModularPlusCalMappingVariableName) mapping.getVariable()).getName());
			} else if (mapping.getVariable() instanceof ModularPlusCalMappingVariablePosition) {
				out.write("@");
				out.write(Integer.toString(
						((ModularPlusCalMappingVariablePosition) mapping.getVariable()).getPosition()));
			} else {
				throw new Unreachable();
			}

			if (mapping.getVariable().isFunctionCall()) {
				out.write("[_]");
			}

			out.write(" via ");
			out.write(mapping.getTarget().getName());
		}

		out.write(";");

		return null;
	}

	@Override
	public Void visit(ModularPlusCalMappingMacro modularPlusCalMappingMacro) throws IOException {
		out.write("mapping macro ");
		out.write(modularPlusCalMappingMacro.getName());
		out.write("{");

		out.newLine();
		out.write("read {");
		try(IndentingWriter.Indent i_ = out.indent()) {
			for (PlusCalStatement s : modularPlusCalMappingMacro.getReadBody()) {
				out.newLine();
				s.accept(new PlusCalNodeFormattingVisitor(out));
			}
		}
		out.newLine();
		out.write("}");

		out.newLine();
		out.write("write {");
		try(IndentingWriter.Indent i_ = out.indent()) {
			for (PlusCalStatement s : modularPlusCalMappingMacro.getWriteBody()) {
				out.newLine();
				s.accept(new PlusCalNodeFormattingVisitor(out));
			}
		}
		out.newLine();
		out.write("}");

		out.newLine();
		out.write("}");
		return null;
	}
}
