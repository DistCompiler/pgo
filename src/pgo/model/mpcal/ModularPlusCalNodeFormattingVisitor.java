package pgo.model.mpcal;

import pgo.TODO;
import pgo.Unreachable;
import pgo.formatters.IndentingWriter;
import pgo.formatters.TypeFormattingVisitor;
import pgo.formatters.PlusCalNodeFormattingVisitor;
import pgo.formatters.TLAExpressionFormattingVisitor;
import pgo.model.pcal.PlusCalFairness;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.type.TypeVariable;

import java.io.IOException;
import java.util.stream.Collectors;

public class ModularPlusCalNodeFormattingVisitor extends ModularPlusCalNodeVisitor<Void, IOException> {
	private IndentingWriter out;

	public ModularPlusCalNodeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(ModularPlusCalBlock modularPlusCalBlock) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(ModularPlusCalArchetype modularPlusCalArchetype) throws IOException {
		out.write("archetype ");
		out.write(modularPlusCalArchetype.getName());
		out.write("(");
		out.write(modularPlusCalArchetype
				.getParams()
				.stream()
				.map(arg -> (arg.isRef() ? "ref " : "") + arg.getName().getValue())
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

		out.write("read {");
		for (PlusCalStatement s : modularPlusCalMappingMacro.getReadBody()) {
			s.accept(new PlusCalNodeFormattingVisitor(out));
		}
		out.write("}");

		out.write("write {");
		for (PlusCalStatement s : modularPlusCalMappingMacro.getWriteBody()) {
			s.accept(new PlusCalNodeFormattingVisitor(out));
		}
		out.write("}");

		out.write("}");
		return null;
	}

	@Override
	public Void visit(ModularPlusCalParameterDeclaration modularPlusCalParameterDeclaration) throws IOException {
        if (modularPlusCalParameterDeclaration.isRef()) {
        	out.write("ref ");
        }
        out.write(modularPlusCalParameterDeclaration.getName().getValue());
        if (!(modularPlusCalParameterDeclaration.getType() instanceof TypeVariable)) {
        	out.write(" : ");
        	modularPlusCalParameterDeclaration.getType().accept(new TypeFormattingVisitor(out));
        }
		return null;
	}
}
