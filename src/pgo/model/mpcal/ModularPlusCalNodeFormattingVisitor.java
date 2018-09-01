package pgo.model.mpcal;

import pgo.TODO;
import pgo.formatters.IndentingWriter;

import java.io.IOException;

public class ModularPlusCalNodeFormattingVisitor extends ModularPlusCalNodeVisitor<Void, IOException> {
	private IndentingWriter out;

	public ModularPlusCalNodeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(ModularPlusCalArchetype modularPlusCalArchetype) throws IOException {
		throw new TODO();
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
