package pgo.model.mpcal;

import pgo.TODO;
import pgo.formatters.IndentingWriter;

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
				.getArguments()
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
		throw new TODO();
	}

	@Override
	public Void visit(ModularPlusCalMappingMacro modularPlusCalMappingMacro) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(ModularPlusCalVariableDeclaration modularPlusCalVariableDeclaration) throws IOException {
		throw new TODO();
	}
}
