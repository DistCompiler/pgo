package pgo.formatters;

import java.io.IOException;
import java.util.List;

import pgo.model.tla.TLAAssumption;
import pgo.model.tla.TLAConstantDeclaration;
import pgo.model.tla.TLAFunctionDefinition;
import pgo.model.tla.TLAIdentifier;
import pgo.model.tla.TLAInstance;
import pgo.model.tla.TLAModule;
import pgo.model.tla.TLAModuleDefinition;
import pgo.model.tla.TLAOpDecl;
import pgo.model.tla.TLAOperatorDefinition;
import pgo.model.tla.TLAQuantifierBound;
import pgo.model.tla.TLATheorem;
import pgo.model.tla.TLAUnit;
import pgo.model.tla.TLAUnitVisitor;
import pgo.model.tla.TLAVariableDeclaration;

public class TLAUnitFormattingVisitor extends TLAUnitVisitor<Void, IOException> {
	
	IndentingWriter out;
	
	public TLAUnitFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(TLAInstance pGoTLAInstance) throws IOException {
		if(pGoTLAInstance.isLocal()) {
			out.write("LOCAL ");
		}
		out.write("INSTANCE ");
		pGoTLAInstance.getModuleName().accept(new TLANodeFormattingVisitor(out));
		List<TLAInstance.Remapping> remappings = pGoTLAInstance.getRemappings();
		if(!remappings.isEmpty()) {
			out.write(" WITH ");
			FormattingTools.writeCommaSeparated(out, remappings, map -> {
				map.accept(new TLANodeFormattingVisitor(out));
			});
		}
		return null;
	}

	@Override
	public Void visit(TLAFunctionDefinition pGoTLAFunctionDefinition) throws IOException {
		if(pGoTLAFunctionDefinition.isLocal()) {
			out.write("LOCAL ");
		}
		pGoTLAFunctionDefinition.getName().accept(new TLANodeFormattingVisitor(out));
		out.write("[");
		List<TLAQuantifierBound> args = pGoTLAFunctionDefinition.getFunction().getArguments();
		FormattingTools.writeCommaSeparated(out, args, arg -> {
			arg.accept(new TLANodeFormattingVisitor(out));
		});
		out.write("]");
		out.write(" == ");
		pGoTLAFunctionDefinition.getFunction().getBody().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLAOperatorDefinition pGoTLAOperator) throws IOException {
		if(pGoTLAOperator.isLocal()) {
			out.write("LOCAL ");
		}
		// TODO: handle infix, etc
		pGoTLAOperator.getName().accept(new TLANodeFormattingVisitor(out));
		List<TLAOpDecl> args = pGoTLAOperator.getArgs();
		if(!args.isEmpty()) {
			out.write("(");
			FormattingTools.writeCommaSeparated(out, args, arg -> {
				arg.accept(new TLANodeFormattingVisitor(out));
			});
			out.write(")");
		}
		out.write(" == ");
		pGoTLAOperator.getBody().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLATheorem pGoTLATheorem) throws IOException {
		out.write("THEOREM ");
		pGoTLATheorem.getTheorem().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLAModule pGoTLAModule) throws IOException {
		out.write("----");
		out.write(" MODULE ");
		pGoTLAModule.getName().accept(new TLANodeFormattingVisitor(out));
		out.write("----");
		out.newLine();
		List<TLAIdentifier> exts = pGoTLAModule.getExtends();
		if(!exts.isEmpty()) {
			out.write("EXTENDS ");
			FormattingTools.writeCommaSeparated(out, exts, ext -> {
				ext.accept(new TLANodeFormattingVisitor(out));
			});
			out.newLine();
		}
		for(TLAUnit unit : pGoTLAModule.getPreTranslationUnits()) {
			unit.accept(this);
			out.newLine();
		}
		out.write("\\* BEGIN TRANSLATION");
		out.newLine();
		for(TLAUnit unit : pGoTLAModule.getTranslatedUnits()) {
			unit.accept(this);
			out.newLine();
		}
		out.write("\\* END TRANSLATION");
		out.newLine();
		for(TLAUnit unit : pGoTLAModule.getPostTranslationUnits()) {
			unit.accept(this);
			out.newLine();
		}
		out.write("====");
		return null;
	}

	@Override
	public Void visit(TLAVariableDeclaration pGoTLAVariableDeclaration) throws IOException {
		out.write("VARIABLES ");
		FormattingTools.writeCommaSeparated(out, pGoTLAVariableDeclaration.getVariables(), var -> {
			var.accept(new TLANodeFormattingVisitor(out));
		});
		return null;
	}

	@Override
	public Void visit(TLAConstantDeclaration TLAConstantDeclaration) throws IOException {
		out.write("CONSTANT ");
		FormattingTools.writeCommaSeparated(out, TLAConstantDeclaration.getConstants(), var -> {
			var.accept(new TLANodeFormattingVisitor(out));
		});
		return null;
	}

	@Override
	public Void visit(TLAModuleDefinition pGoTLAModuleDefinition) throws IOException {
		if(pGoTLAModuleDefinition.isLocal()) {
			out.write("LOCAL ");
		}
		pGoTLAModuleDefinition.getName().accept(new TLANodeFormattingVisitor(out));
		List<TLAOpDecl> args = pGoTLAModuleDefinition.getArgs();
		if(!args.isEmpty()) {
			out.write("(");
			FormattingTools.writeCommaSeparated(out, args, arg -> {
				arg.accept(new TLANodeFormattingVisitor(out));
			});
			out.write(")");
		}
		out.write(" == ");
		pGoTLAModuleDefinition.getInstance().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAAssumption TLAAssumption) throws IOException {
		out.write("ASSUME ");
		TLAAssumption.getAssumption().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}
	
}
