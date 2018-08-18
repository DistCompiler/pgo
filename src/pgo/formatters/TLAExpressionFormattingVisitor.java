package pgo.formatters;

import pgo.model.tla.*;
import pgo.parser.TLAParser;

import java.io.IOException;
import java.util.List;

public class TLAExpressionFormattingVisitor extends TLAExpressionVisitor<Void, IOException> {
	
	IndentingWriter out;
	
	public TLAExpressionFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}
	
	private void formatPrefix(List<TLAGeneralIdentifierPart> prefix) throws IOException {
		for(TLAGeneralIdentifierPart part : prefix) {
			part.accept(new TLANodeFormattingVisitor(out));
		}
	}

	@Override
	public Void visit(TLAFunctionCall pGoTLAFunctionCall) throws IOException {
		pGoTLAFunctionCall.getFunction().accept(this);
		out.write("[");
		FormattingTools.writeCommaSeparated(out, pGoTLAFunctionCall.getParams(), param -> {
			param.accept(this);
		});
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLABinOp TLABinOp) throws IOException {
		out.write("(");
		TLABinOp.getLHS().accept(this);
		out.write(")");
		formatPrefix(TLABinOp.getPrefix());
		TLABinOp.getOperation().accept(new TLANodeFormattingVisitor(out));
		out.write("(");
		TLABinOp.getRHS().accept(this);
		out.write(")");
		return null;
	}

	@Override
	public Void visit(TLABool TLABool) throws IOException {
		if(TLABool.getValue()) {
			out.write("TRUE");
		}else {
			out.write("FALSE");
		}
		return null;
	}

	@Override
	public Void visit(TLACase TLACase) throws IOException {
		out.write("CASE ");
		int indentFrom = out.getHorizontalPosition();
		List<TLACaseArm> arms = TLACase.getArms();
		TLACaseArm firstArm = arms.get(0);
		firstArm.getCondition().accept(this);
		out.write(" -> ");
		firstArm.getResult().accept(this);
		try(IndentingWriter.Indent i_ = out.indentToPosition(indentFrom)){
			for(int i = 1; i < arms.size(); ++i) {
				out.newLine();
				TLACaseArm arm = arms.get(i);
				arm.accept(new TLANodeFormattingVisitor(out));
			}
			
			if(TLACase.getOther() != null) {
				out.newLine();
				out.write("[] OTHER -> ");
				TLACase.getOther().accept(this);
			}
		}
		
		return null;
	}

	@Override
	public Void visit(TLAExistential TLAExistential) throws IOException {
		out.write("\\E ");
		FormattingTools.writeCommaSeparated(out, TLAExistential.getIds(), id -> {
			id.accept(new TLANodeFormattingVisitor(out));
		});
		out.write(" : ");
		TLAExistential.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAFunction pGoTLAFunction) throws IOException {
		out.write("[");
		FormattingTools.writeCommaSeparated(out, pGoTLAFunction.getArguments(), arg -> {
			arg.accept(new TLANodeFormattingVisitor(out));
		});
		out.write("|->");
		pGoTLAFunction.getBody().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLAFunctionSet pGoTLAFunctionSet) throws IOException {
		out.write("[");
		pGoTLAFunctionSet.getFrom().accept(this);
		out.write("->");
		pGoTLAFunctionSet.getTo().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws IOException {
		out.write("[ ");
		pGoTLAFunctionSubstitution.getSource().accept(this);
		out.write(" EXCEPT");
		for(TLAFunctionSubstitutionPair p : pGoTLAFunctionSubstitution.getSubstitutions()) {
			out.write(" ");
			p.accept(new TLANodeFormattingVisitor(out));
		}
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLAIf pGoTLAIf) throws IOException {
		out.write("IF ");
		pGoTLAIf.getCond().accept(this);
		out.write(" THEN ");
		pGoTLAIf.getTval().accept(this);
		out.write(" ELSE ");
		pGoTLAIf.getFval().accept(this);
		return null;
	}

	@Override
	public Void visit(TLALet pGoTLALet) throws IOException {
		int indentFrom = out.getHorizontalPosition();
		out.write("LET");
		try(IndentingWriter.Indent i_ = out.indent()){
			for(TLAUnit unit : pGoTLALet.getDefinitions()) {
				out.newLine();
				unit.accept(new TLAUnitFormattingVisitor(out));
			}
		}
		out.newLine();
		try(IndentingWriter.Indent i_ = out.indentToPosition(indentFrom)){
			out.write("IN ");
			try(IndentingWriter.Indent ii__ = out.indent()){
				pGoTLALet.getBody().accept(this);
			}
		}
		return null;
	}

	@Override
	public Void visit(TLAGeneralIdentifier pGoTLAVariable) throws IOException {
		formatPrefix(pGoTLAVariable.getGeneralIdentifierPrefix());
		pGoTLAVariable.getName().accept(new TLANodeFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLATuple pGoTLATuple) throws IOException {
		out.write("<<");
		FormattingTools.writeCommaSeparated(out, pGoTLATuple.getElements(), elem -> {
			elem.accept(this);
		});
		out.write(">>");
		return null;
	}

	@Override
	public Void visit(TLAMaybeAction pGoTLAMaybeAction) throws IOException {
		out.write("[");
		pGoTLAMaybeAction.getBody().accept(this);
		out.write("]_");
		pGoTLAMaybeAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(TLANumber pGoTLANumber) throws IOException {
		out.write(pGoTLANumber.getVal());
		return null;
	}

	@Override
	public Void visit(TLAOperatorCall pGoTLAOperatorCall) throws IOException {
		formatPrefix(pGoTLAOperatorCall.getPrefix());
		pGoTLAOperatorCall.getName().accept(new TLANodeFormattingVisitor(out));
		out.write("(");
		FormattingTools.writeCommaSeparated(out, pGoTLAOperatorCall.getArgs(), arg -> {
			arg.accept(this);
		});
		out.write(")");
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws IOException {
		out.write("\\E ");
		FormattingTools.writeCommaSeparated(out, pGoTLAQuantifiedExistential.getIds(), id -> {
			id.accept(new TLANodeFormattingVisitor(out));
		});
		out.write(" : ");
		pGoTLAQuantifiedExistential.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws IOException {
		out.write("\\A ");
		FormattingTools.writeCommaSeparated(out, pGoTLAQuantifiedUniversal.getIds(), id -> {
			id.accept(new TLANodeFormattingVisitor(out));
		});
		out.write(" : ");
		pGoTLAQuantifiedUniversal.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLARecordConstructor pGoTLARecordConstructor) throws IOException {
		out.write("[");
		FormattingTools.writeCommaSeparated(out, pGoTLARecordConstructor.getFields(), field -> {
			field.accept(new TLANodeFormattingVisitor(out));
		});
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLARecordSet pGoTLARecordSet) throws IOException {
		out.write("[");
		FormattingTools.writeCommaSeparated(out, pGoTLARecordSet.getFields(), field -> {
			field.accept(new TLANodeFormattingVisitor(out));
		});
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLARequiredAction pGoTLARequiredAction) throws IOException {
		out.write("<<");
		pGoTLARequiredAction.getBody().accept(this);
		out.write(">>_");
		pGoTLARequiredAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(TLASetConstructor pGoTLASetConstructor) throws IOException {
		out.write("{");
		FormattingTools.writeCommaSeparated(out, pGoTLASetConstructor.getContents(), member -> {
			member.accept(this);
		});
		out.write("}");
		return null;
	}

	@Override
	public Void visit(TLASetComprehension pGoTLASetComprehension) throws IOException {
		out.write("{");
		pGoTLASetComprehension.getBody().accept(this);
		out.write(" : ");
		FormattingTools.writeCommaSeparated(out, pGoTLASetComprehension.getBounds(), bound -> {
			bound.accept(new TLANodeFormattingVisitor(out));
		});
		out.write("}");
		return null;
	}

	@Override
	public Void visit(TLASetRefinement pGoTLASetRefinement) throws IOException {
		out.write("{");
		pGoTLASetRefinement.getIdent().accept(new TLANodeFormattingVisitor(out));
		out.write(" \\in ");
		pGoTLASetRefinement.getFrom().accept(this);
		out.write(" : ");
		pGoTLASetRefinement.getWhen().accept(this);
		out.write("}");
		return null;
	}

	@Override
	public Void visit(TLAString pGoTLAString) throws IOException {
		out.write("\"");
		out.write(pGoTLAString.getValue());
		out.write("\"");
		return null;
	}

	@Override
	public Void visit(TLAUnary pGoTLAUnary) throws IOException {
		if(TLAParser.PREFIX_OPERATORS.contains(pGoTLAUnary.getOperation().getValue())) {
			formatPrefix(pGoTLAUnary.getPrefix());
			out.write(pGoTLAUnary.getOperation().getValue());
			out.write("(");
			pGoTLAUnary.getOperand().accept(this);
			out.write(")");
		}else if(TLAParser.POSTFIX_OPERATORS.contains(pGoTLAUnary.getOperation().getValue())) {
			out.write("(");
			pGoTLAUnary.getOperand().accept(this);
			out.write(")");
			formatPrefix(pGoTLAUnary.getPrefix());
			out.write(pGoTLAUnary.getOperation().getValue());
		}else {
			throw new RuntimeException(pGoTLAUnary.getOperation()+" is not a valid prefix or postfix operator");
		}
		return null;
	}

	@Override
	public Void visit(TLAUniversal pGoTLAUniversal) throws IOException {
		out.write("\\A ");
		FormattingTools.writeCommaSeparated(out, pGoTLAUniversal.getIds(), id -> {
			id.accept(new TLANodeFormattingVisitor(out));
		});
		out.write(" : ");
		pGoTLAUniversal.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws IOException {
		out.write("defaultInitValue");
		return null;
	}

	@Override
	public Void visit(TLAFairness fairness) throws IOException {
		switch(fairness.getType()){
			case WEAK:
				out.write("WF_");
				break;
			case STRONG:
				out.write("SF_");
				break;
		}
		fairness.getVars().accept(this);
		out.write("(");
		fairness.getExpression().accept(this);
		out.write(")");
		return null;
	}

}
