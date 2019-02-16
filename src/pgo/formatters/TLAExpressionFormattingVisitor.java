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
		for (TLAGeneralIdentifierPart part : prefix) {
			part.accept(new TLANodeFormattingVisitor(out));
		}
	}

	@Override
	public Void visit(TLAFunctionCall tlaFunctionCall) throws IOException {
		tlaFunctionCall.getFunction().accept(this);
		out.write("[");
		FormattingTools.writeCommaSeparated(out, tlaFunctionCall.getParams(), param -> param.accept(this));
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLABinOp tlaBinOp) throws IOException {
		out.write("(");
		tlaBinOp.getLHS().accept(this);
		out.write(")");
		formatPrefix(tlaBinOp.getPrefix());
		tlaBinOp.getOperation().accept(new TLANodeFormattingVisitor(out));
		out.write("(");
		tlaBinOp.getRHS().accept(this);
		out.write(")");
		return null;
	}

	@Override
	public Void visit(TLABool tlaBool) throws IOException {
		if (tlaBool.getValue()) {
			out.write("TRUE");
		} else {
			out.write("FALSE");
		}
		return null;
	}

	@Override
	public Void visit(TLACase tlaCase) throws IOException {
		out.write("CASE ");
		int indentFrom = out.getHorizontalPosition();
		List<TLACaseArm> arms = tlaCase.getArms();
		TLACaseArm firstArm = arms.get(0);
		firstArm.getCondition().accept(this);
		out.write(" -> ");
		firstArm.getResult().accept(this);
		try (IndentingWriter.Indent ignored = out.indentToPosition(indentFrom)){
			for (int i = 1; i < arms.size(); ++i) {
				out.newLine();
				TLACaseArm arm = arms.get(i);
				arm.accept(new TLANodeFormattingVisitor(out));
			}

			if (tlaCase.getOther() != null) {
				out.newLine();
				out.write("[] OTHER -> ");
				tlaCase.getOther().accept(this);
			}
		}

		return null;
	}

	@Override
	public Void visit(TLADot tlaDot) throws IOException {
		tlaDot.getExpression().accept(this);
		out.write(".");
		tlaDot.getField().accept(new TLANodeFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLAExistential tlaExistential) throws IOException {
		out.write("\\E ");
		FormattingTools.writeCommaSeparated(
				out, tlaExistential.getIds(), id -> id.accept(new TLANodeFormattingVisitor(out)));
		out.write(" : ");
		tlaExistential.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAFunction tlaFunction) throws IOException {
		out.write("[");
		FormattingTools.writeCommaSeparated(
				out, tlaFunction.getArguments(), arg -> arg.accept(new TLANodeFormattingVisitor(out)));
		out.write(" |-> ");
		tlaFunction.getBody().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLAFunctionSet tlaFunctionSet) throws IOException {
		out.write("[");
		tlaFunctionSet.getFrom().accept(this);
		out.write(" -> ");
		tlaFunctionSet.getTo().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws IOException {
		out.write("[");
		tlaFunctionSubstitution.getSource().accept(this);
		out.write(" EXCEPT");
		for (TLAFunctionSubstitutionPair p : tlaFunctionSubstitution.getSubstitutions()) {
			out.write(" ");
			p.accept(new TLANodeFormattingVisitor(out));
		}
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLAIf tlaIf) throws IOException {
		out.write("IF ");
		tlaIf.getCond().accept(this);
		out.write(" THEN ");
		tlaIf.getTval().accept(this);
		out.write(" ELSE ");
		tlaIf.getFval().accept(this);
		return null;
	}

	@Override
	public Void visit(TLALet tlaLet) throws IOException {
		int indentFrom = out.getHorizontalPosition();
		out.write("LET");
		try (IndentingWriter.Indent ignored = out.indent()){
			for (TLAUnit unit : tlaLet.getDefinitions()) {
				out.newLine();
				unit.accept(new TLAUnitFormattingVisitor(out));
			}
		}
		out.newLine();
		try (IndentingWriter.Indent ignored = out.indentToPosition(indentFrom)){
			out.write("IN ");
			try (IndentingWriter.Indent ignored1 = out.indent()){
				tlaLet.getBody().accept(this);
			}
		}
		return null;
	}

	@Override
	public Void visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws IOException {
		formatPrefix(tlaGeneralIdentifier.getGeneralIdentifierPrefix());
		tlaGeneralIdentifier.getName().accept(new TLANodeFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLATuple tlaTuple) throws IOException {
		out.write("<<");
		FormattingTools.writeCommaSeparated(out, tlaTuple.getElements(), elem -> elem.accept(this));
		out.write(">>");
		return null;
	}

	@Override
	public Void visit(TLAMaybeAction tlaMaybeAction) throws IOException {
		out.write("[");
		tlaMaybeAction.getBody().accept(this);
		out.write("]_");
		tlaMaybeAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(TLANumber tlaNumber) throws IOException {
		out.write(tlaNumber.getVal());
		return null;
	}

	@Override
	public Void visit(TLAOperatorCall tlaOperatorCall) throws IOException {
		formatPrefix(tlaOperatorCall.getPrefix());
		tlaOperatorCall.getName().accept(new TLANodeFormattingVisitor(out));
		out.write("(");
		FormattingTools.writeCommaSeparated(out, tlaOperatorCall.getArgs(), arg -> arg.accept(this));
		out.write(")");
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws IOException {
		out.write("\\E ");
		FormattingTools.writeCommaSeparated(
				out, tlaQuantifiedExistential.getIds(), id -> id.accept(new TLANodeFormattingVisitor(out)));
		out.write(" : ");
		tlaQuantifiedExistential.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws IOException {
		out.write("\\A ");
		FormattingTools.writeCommaSeparated(
				out, tlaQuantifiedUniversal.getIds(), id -> id.accept(new TLANodeFormattingVisitor(out)));
		out.write(" : ");
		tlaQuantifiedUniversal.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLARecordConstructor tlaRecordConstructor) throws IOException {
		out.write("[");
		FormattingTools.writeCommaSeparated(
				out, tlaRecordConstructor.getFields(), field -> field.accept(new TLANodeFormattingVisitor(out)));
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLARecordSet tlaRecordSet) throws IOException {
		out.write("[");
		FormattingTools.writeCommaSeparated(
				out, tlaRecordSet.getFields(), field -> field.accept(new TLANodeFormattingVisitor(out)));
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLARequiredAction tlaRequiredAction) throws IOException {
		out.write("<<");
		tlaRequiredAction.getBody().accept(this);
		out.write(">>_");
		tlaRequiredAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(TLASetConstructor tlaSetConstructor) throws IOException {
		out.write("{");
		FormattingTools.writeCommaSeparated(out, tlaSetConstructor.getContents(), member -> member.accept(this));
		out.write("}");
		return null;
	}

	@Override
	public Void visit(TLASetComprehension tlaSetComprehension) throws IOException {
		out.write("{");
		tlaSetComprehension.getBody().accept(this);
		out.write(" : ");
		FormattingTools.writeCommaSeparated(
				out, tlaSetComprehension.getBounds(), bound -> bound.accept(new TLANodeFormattingVisitor(out)));
		out.write("}");
		return null;
	}

	@Override
	public Void visit(TLASetRefinement tlaSetRefinement) throws IOException {
		out.write("{");
		tlaSetRefinement.getIdent().accept(new TLANodeFormattingVisitor(out));
		out.write(" \\in ");
		tlaSetRefinement.getFrom().accept(this);
		out.write(" : ");
		tlaSetRefinement.getWhen().accept(this);
		out.write("}");
		return null;
	}

	@Override
	public Void visit(TLAString tlaString) throws IOException {
		out.write("\"");
		out.write(tlaString.getValue());
		out.write("\"");
		return null;
	}

	@Override
	public Void visit(TLAUnary tlaUnary) throws IOException {
		if (tlaUnary.getOperation().getValue().equals("-_")) {
			formatPrefix(tlaUnary.getPrefix());
			out.write("-");
			out.write("(");
			tlaUnary.getOperand().accept(this);
			out.write(")");
		} else if (TLAParser.PREFIX_OPERATORS.contains(tlaUnary.getOperation().getValue())) {
			formatPrefix(tlaUnary.getPrefix());
			out.write(tlaUnary.getOperation().getValue());
			out.write("(");
			tlaUnary.getOperand().accept(this);
			out.write(")");
		} else if (TLAParser.POSTFIX_OPERATORS.contains(tlaUnary.getOperation().getValue())) {
			out.write("(");
			tlaUnary.getOperand().accept(this);
			out.write(")");
			formatPrefix(tlaUnary.getPrefix());
			out.write(tlaUnary.getOperation().getValue());
		} else {
			throw new RuntimeException(tlaUnary.getOperation()+" is not a valid prefix or postfix operator");
		}
		return null;
	}

	@Override
	public Void visit(TLAUniversal tlaUniversal) throws IOException {
		out.write("\\A ");
		FormattingTools.writeCommaSeparated(
				out, tlaUniversal.getIds(), id -> id.accept(new TLANodeFormattingVisitor(out)));
		out.write(" : ");
		tlaUniversal.getBody().accept(this);
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

	@Override
	public Void visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws IOException {
		out.write("$variable");
		return null;
	}

	@Override
	public Void visit(TLASpecialVariableValue tlaSpecialVariableValue) throws IOException {
		out.write("$value");
		return null;
	}

	@Override
	public Void visit(TLARef tlaRef) throws IOException {
		out.write("ref ");
		out.write(tlaRef.getTarget());
		return null;
	}

}
