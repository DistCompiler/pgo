package pgo.formatters;

import java.io.IOException;
import java.util.List;

import pgo.model.tla.PGoTLAAssumption;
import pgo.model.tla.PGoTLAConstantDeclaration;
import pgo.model.tla.PGoTLAFunctionDefinition;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.model.tla.PGoTLAInstance;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAModuleDefinition;
import pgo.model.tla.PGoTLAOpDecl;
import pgo.model.tla.PGoTLAOperatorDefinition;
import pgo.model.tla.PGoTLAQuantifierBound;
import pgo.model.tla.PGoTLATheorem;
import pgo.model.tla.PGoTLAUnit;
import pgo.model.tla.PGoTLAUnitVisitor;
import pgo.model.tla.PGoTLAVariableDeclaration;

public class PGoTLAUnitFormattingVisitor extends PGoTLAUnitVisitor<Void, IOException> {
	
	IndentingWriter out;
	
	public PGoTLAUnitFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(PGoTLAInstance pGoTLAInstance) throws IOException {
		if(pGoTLAInstance.isLocal()) {
			out.write("LOCAL ");
		}
		out.write("INSTANCE ");
		pGoTLAInstance.getModuleName().accept(new PGoTLANodeFormattingVisitor(out));
		List<PGoTLAInstance.Remapping> remappings = pGoTLAInstance.getRemappings();
		if(!remappings.isEmpty()) {
			out.write(" WITH ");
			FormattingTools.writeCommaSeparated(out, remappings, map -> {
				map.accept(new PGoTLANodeFormattingVisitor(out));
			});
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAFunctionDefinition pGoTLAFunctionDefinition) throws IOException {
		if(pGoTLAFunctionDefinition.isLocal()) {
			out.write("LOCAL ");
		}
		pGoTLAFunctionDefinition.getName().accept(new PGoTLANodeFormattingVisitor(out));
		out.write("[");
		List<PGoTLAQuantifierBound> args = pGoTLAFunctionDefinition.getFunction().getArguments();
		FormattingTools.writeCommaSeparated(out, args, arg -> {
			arg.accept(new PGoTLANodeFormattingVisitor(out));
		});
		out.write("]");
		out.write(" == ");
		pGoTLAFunctionDefinition.getFunction().getBody().accept(new PGoTLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(PGoTLAOperatorDefinition pGoTLAOperator) throws IOException {
		if(pGoTLAOperator.isLocal()) {
			out.write("LOCAL ");
		}
		// TODO: handle infix, etc
		pGoTLAOperator.getName().accept(new PGoTLANodeFormattingVisitor(out));
		List<PGoTLAOpDecl> args = pGoTLAOperator.getArgs();
		if(!args.isEmpty()) {
			out.write("(");
			FormattingTools.writeCommaSeparated(out, args, arg -> {
				arg.accept(new PGoTLANodeFormattingVisitor(out));
			});
			out.write(")");
		}
		out.write(" == ");
		pGoTLAOperator.getBody().accept(new PGoTLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(PGoTLATheorem pGoTLATheorem) throws IOException {
		out.write("THEOREM ");
		pGoTLATheorem.getTheorem().accept(new PGoTLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(PGoTLAModule pGoTLAModule) throws IOException {
		out.write("----");
		pGoTLAModule.getName().accept(new PGoTLANodeFormattingVisitor(out));
		out.write("----");
		out.newLine();
		List<PGoTLAIdentifier> exts = pGoTLAModule.getExtends();
		if(!exts.isEmpty()) {
			out.write("EXTENDS ");
			FormattingTools.writeCommaSeparated(out, exts, ext -> {
				ext.accept(new PGoTLANodeFormattingVisitor(out));
			});
			out.newLine();
		}
		for(PGoTLAUnit unit : pGoTLAModule.getPreTranslationUnits()) {
			unit.accept(this);
			out.newLine();
		}
		out.write("\\* BEGIN TRANSLATION");
		out.newLine();
		for(PGoTLAUnit unit : pGoTLAModule.getTranslatedUnits()) {
			unit.accept(this);
			out.newLine();
		}
		out.write("\\* END TRANSLATION");
		out.newLine();
		for(PGoTLAUnit unit : pGoTLAModule.getPostTranslationUnits()) {
			unit.accept(this);
			out.newLine();
		}
		out.write("====");
		return null;
	}

	@Override
	public Void visit(PGoTLAVariableDeclaration pGoTLAVariableDeclaration) throws IOException {
		out.write("VARIABLES ");
		FormattingTools.writeCommaSeparated(out, pGoTLAVariableDeclaration.getVariables(), var -> {
			var.accept(new PGoTLANodeFormattingVisitor(out));
		});
		return null;
	}

	@Override
	public Void visit(PGoTLAConstantDeclaration pGoTLAConstantDeclaration) throws IOException {
		out.write("CONSTANT ");
		FormattingTools.writeCommaSeparated(out, pGoTLAConstantDeclaration.getConstants(), var -> {
			var.accept(new PGoTLANodeFormattingVisitor(out));
		});
		return null;
	}

	@Override
	public Void visit(PGoTLAModuleDefinition pGoTLAModuleDefinition) throws IOException {
		if(pGoTLAModuleDefinition.isLocal()) {
			out.write("LOCAL ");
		}
		pGoTLAModuleDefinition.getName().accept(new PGoTLANodeFormattingVisitor(out));
		List<PGoTLAOpDecl> args = pGoTLAModuleDefinition.getArgs();
		if(!args.isEmpty()) {
			out.write("(");
			FormattingTools.writeCommaSeparated(out, args, arg -> {
				arg.accept(new PGoTLANodeFormattingVisitor(out));
			});
			out.write(")");
		}
		out.write(" == ");
		pGoTLAModuleDefinition.getInstance().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLAAssumption pGoTLAAssumption) throws IOException {
		out.write("ASSUME ");
		pGoTLAAssumption.getAssumption().accept(new PGoTLAExpressionFormattingVisitor(out));
		return null;
	}
	
}
