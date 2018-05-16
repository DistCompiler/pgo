package pgo.formatters;

import java.io.IOException;
import java.util.List;

import pgo.model.tla.PGoTLABinOp;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLACase;
import pgo.model.tla.PGoTLACaseArm;
import pgo.model.tla.PGoTLAExistential;
import pgo.model.tla.PGoTLAExpressionVisitor;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.PGoTLAFunctionSet;
import pgo.model.tla.PGoTLAFunctionSubstitution;
import pgo.model.tla.PGoTLAFunctionSubstitutionPair;
import pgo.model.tla.PGoTLAGeneralIdentifier;
import pgo.model.tla.PGoTLAGeneralIdentifierPart;
import pgo.model.tla.PGoTLAIf;
import pgo.model.tla.PGoTLALet;
import pgo.model.tla.PGoTLAMaybeAction;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAOperatorCall;
import pgo.model.tla.PGoTLAQuantifiedExistential;
import pgo.model.tla.PGoTLAQuantifiedUniversal;
import pgo.model.tla.PGoTLARecordConstructor;
import pgo.model.tla.PGoTLARecordSet;
import pgo.model.tla.PGoTLARequiredAction;
import pgo.model.tla.PGoTLASetComprehension;
import pgo.model.tla.PGoTLASetConstructor;
import pgo.model.tla.PGoTLASetRefinement;
import pgo.model.tla.PGoTLAString;
import pgo.model.tla.PGoTLATuple;
import pgo.model.tla.PGoTLAUnary;
import pgo.model.tla.PGoTLAUnit;
import pgo.model.tla.PGoTLAUniversal;
import pgo.parser.TLAParser;

public class PGoTLAExpressionFormattingVisitor extends PGoTLAExpressionVisitor<Void, IOException> {
	
	IndentingWriter out;
	
	public PGoTLAExpressionFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}
	
	private void formatPrefix(List<PGoTLAGeneralIdentifierPart> prefix) throws IOException {
		for(PGoTLAGeneralIdentifierPart part : prefix) {
			part.accept(new PGoTLANodeFormattingVisitor(out));
		}
	}

	@Override
	public Void visit(PGoTLAFunctionCall pGoTLAFunctionCall) throws IOException {
		pGoTLAFunctionCall.getFunction().accept(this);
		out.write("[");
		FormattingTools.writeCommaSeparated(out, pGoTLAFunctionCall.getParams(), param -> {
			param.accept(this);
		});
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTLABinOp pGoTLABinOp) throws IOException {
		out.write("(");
		pGoTLABinOp.getLHS().accept(this);
		out.write(")");
		formatPrefix(pGoTLABinOp.getPrefix());
		out.write(pGoTLABinOp.getOperation());
		out.write("(");
		pGoTLABinOp.getRHS().accept(this);
		out.write(")");
		return null;
	}

	@Override
	public Void visit(PGoTLABool pGoTLABool) throws IOException {
		if(pGoTLABool.getValue()) {
			out.write("TRUE");
		}else {
			out.write("FALSE");
		}
		return null;
	}

	@Override
	public Void visit(PGoTLACase pGoTLACase) throws IOException {
		out.write("CASE ");
		int indentFrom = out.getHorizontalPosition();
		List<PGoTLACaseArm> arms = pGoTLACase.getArms();
		PGoTLACaseArm firstArm = arms.get(0);
		firstArm.getCondition().accept(this);
		out.write(" -> ");
		firstArm.getResult().accept(this);
		try(IndentingWriter.Indent i_ = out.indentToPosition(indentFrom)){
			for(int i = 1; i < arms.size(); ++i) {
				out.newLine();
				PGoTLACaseArm arm = arms.get(i);
				arm.accept(new PGoTLANodeFormattingVisitor(out));
			}
			
			if(pGoTLACase.getOther() != null) {
				out.newLine();
				out.write("[] OTHER -> ");
				pGoTLACase.getOther().accept(this);
			}
		}
		
		return null;
	}

	@Override
	public Void visit(PGoTLAExistential pGoTLAExistential) throws IOException {
		out.write("\\E ");
		FormattingTools.writeCommaSeparated(out, pGoTLAExistential.getIds(), id -> {
			id.accept(new PGoTLANodeFormattingVisitor(out));
		});
		out.write(" : ");
		pGoTLAExistential.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLAFunction pGoTLAFunction) throws IOException {
		out.write("[");
		FormattingTools.writeCommaSeparated(out, pGoTLAFunction.getArguments(), arg -> {
			arg.accept(new PGoTLANodeFormattingVisitor(out));
		});
		out.write("|->");
		pGoTLAFunction.getBody().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws IOException {
		out.write("[");
		pGoTLAFunctionSet.getFrom().accept(this);
		out.write("->");
		pGoTLAFunctionSet.getTo().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws IOException {
		out.write("[ ");
		pGoTLAFunctionSubstitution.getSource().accept(this);
		out.write(" EXCEPT");
		for(PGoTLAFunctionSubstitutionPair p : pGoTLAFunctionSubstitution.getSubstitutions()) {
			out.write(" ");
			p.accept(new PGoTLANodeFormattingVisitor(out));
		}
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTLAIf pGoTLAIf) throws IOException {
		out.write("IF ");
		pGoTLAIf.getCond().accept(this);
		out.write(" THEN ");
		pGoTLAIf.getTval().accept(this);
		out.write(" ELSE ");
		pGoTLAIf.getFval().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLALet pGoTLALet) throws IOException {
		int indentFrom = out.getHorizontalPosition();
		out.write("LET");
		try(IndentingWriter.Indent i_ = out.indent()){
			for(PGoTLAUnit unit : pGoTLALet.getDefinitions()) {
				out.newLine();
				unit.accept(new PGoTLAUnitFormattingVisitor(out));
			}
		}
		out.newLine();
		try(IndentingWriter.Indent i_ = out.indentToPosition(indentFrom)){
			out.write("IN");
			try(IndentingWriter.Indent ii__ = out.indent()){
				pGoTLALet.getBody().accept(this);
			}
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAGeneralIdentifier pGoTLAVariable) throws IOException {
		formatPrefix(pGoTLAVariable.getGeneralIdentifierPrefix());
		pGoTLAVariable.getName().accept(new PGoTLANodeFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(PGoTLATuple pGoTLATuple) throws IOException {
		out.write("<<");
		FormattingTools.writeCommaSeparated(out, pGoTLATuple.getElements(), elem -> {
			elem.accept(this);
		});
		out.write(">>");
		return null;
	}

	@Override
	public Void visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws IOException {
		out.write("[");
		pGoTLAMaybeAction.getBody().accept(this);
		out.write("]_");
		pGoTLAMaybeAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLANumber pGoTLANumber) throws IOException {
		out.write(pGoTLANumber.getVal());
		return null;
	}

	@Override
	public Void visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws IOException {
		formatPrefix(pGoTLAOperatorCall.getPrefix());
		pGoTLAOperatorCall.getName().accept(new PGoTLANodeFormattingVisitor(out));
		out.write("(");
		FormattingTools.writeCommaSeparated(out, pGoTLAOperatorCall.getArgs(), arg -> {
			arg.accept(this);
		});
		out.write(")");
		return null;
	}

	@Override
	public Void visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws IOException {
		out.write("\\E ");
		FormattingTools.writeCommaSeparated(out, pGoTLAQuantifiedExistential.getIds(), id -> {
			id.accept(new PGoTLANodeFormattingVisitor(out));
		});
		out.write(" : ");
		pGoTLAQuantifiedExistential.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws IOException {
		out.write("\\A ");
		FormattingTools.writeCommaSeparated(out, pGoTLAQuantifiedUniversal.getIds(), id -> {
			id.accept(new PGoTLANodeFormattingVisitor(out));
		});
		out.write(" : ");
		pGoTLAQuantifiedUniversal.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws IOException {
		out.write("[");
		FormattingTools.writeCommaSeparated(out, pGoTLARecordConstructor.getFields(), field -> {
			field.accept(new PGoTLANodeFormattingVisitor(out));
		});
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTLARecordSet pGoTLARecordSet) throws IOException {
		out.write("[");
		FormattingTools.writeCommaSeparated(out, pGoTLARecordSet.getFields(), field -> {
			field.accept(new PGoTLANodeFormattingVisitor(out));
		});
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTLARequiredAction pGoTLARequiredAction) throws IOException {
		out.write("<<");
		pGoTLARequiredAction.getBody().accept(this);
		out.write(">>_");
		pGoTLARequiredAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLASetConstructor pGoTLASetConstructor) throws IOException {
		out.write("{");
		FormattingTools.writeCommaSeparated(out, pGoTLASetConstructor.getContents(), member -> {
			member.accept(this);
		});
		out.write("}");
		return null;
	}

	@Override
	public Void visit(PGoTLASetComprehension pGoTLASetComprehension) throws IOException {
		out.write("{");
		pGoTLASetComprehension.getBody().accept(this);
		out.write(" : ");
		FormattingTools.writeCommaSeparated(out, pGoTLASetComprehension.getBounds(), bound -> {
			bound.accept(new PGoTLANodeFormattingVisitor(out));
		});
		out.write("}");
		return null;
	}

	@Override
	public Void visit(PGoTLASetRefinement pGoTLASetRefinement) throws IOException {
		out.write("{");
		pGoTLASetRefinement.getIdent().accept(new PGoTLANodeFormattingVisitor(out));
		out.write(" \\in ");
		pGoTLASetRefinement.getFrom().accept(this);
		out.write(" : ");
		pGoTLASetRefinement.getWhen().accept(this);
		out.write("}");
		return null;
	}

	@Override
	public Void visit(PGoTLAString pGoTLAString) throws IOException {
		out.write("\"");
		out.write(pGoTLAString.getValue());
		out.write("\"");
		return null;
	}

	@Override
	public Void visit(PGoTLAUnary pGoTLAUnary) throws IOException {
		if(TLAParser.PREFIX_OPERATORS.contains(pGoTLAUnary.getOperation())) {
			formatPrefix(pGoTLAUnary.getPrefix());
			out.write(pGoTLAUnary.getOperation());
			out.write("(");
			pGoTLAUnary.getOperand().accept(this);
			out.write(")");
		}else if(TLAParser.POSTFIX_OPERATORS.contains(pGoTLAUnary.getOperation())) {
			out.write("(");
			pGoTLAUnary.getOperand().accept(this);
			out.write(")");
			formatPrefix(pGoTLAUnary.getPrefix());
			out.write(pGoTLAUnary.getOperation());
		}else {
			throw new RuntimeException(pGoTLAUnary.getOperation()+" is not a valid prefix or postfix operator");
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAUniversal pGoTLAUniversal) throws IOException {
		out.write("\\A ");
		FormattingTools.writeCommaSeparated(out, pGoTLAUniversal.getIds(), id -> {
			id.accept(new PGoTLANodeFormattingVisitor(out));
		});
		out.write(" : ");
		pGoTLAUniversal.getBody().accept(this);
		return null;
	}

}
