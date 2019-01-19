package pgo.formatters;

import pgo.Unreachable;
import pgo.model.tla.*;

import java.io.IOException;
import java.util.List;

public class TLANodeFormattingVisitor extends TLANodeVisitor<Void, IOException> {
	IndentingWriter out;

	public TLANodeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(TLAExpression TLAExpression) throws IOException {
		TLAExpression.accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLAUnit pGoTLAUnit) throws IOException {
		pGoTLAUnit.accept(new TLAUnitFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLACaseArm TLACaseArm) throws IOException {
		out.write("[] ");
		TLACaseArm.getCondition().accept(new TLAExpressionFormattingVisitor(out));
		out.write(" -> ");
		TLACaseArm.getResult().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLAOpDecl pGoTLAOpDecl) throws IOException {
		switch(pGoTLAOpDecl.getType()) {
			case ID:
				pGoTLAOpDecl.getName().accept(this);
				break;
			case INFIX:
				out.write("_");
				pGoTLAOpDecl.getName().accept(this);
				out.write("_");
				break;
			case NAMED:
				pGoTLAOpDecl.getName().accept(this);
				out.write("(_");
				for(int i = 1; i<pGoTLAOpDecl.getArity(); ++i) {
					out.write(",_");
				}
				out.write(")");
				break;
			case POSTFIX:
				out.write("_");
				pGoTLAOpDecl.getName().accept(this);
				break;
			case PREFIX:
				pGoTLAOpDecl.getName().accept(this);
				out.write("_");
				break;
			default:
				throw new Unreachable();
		}
		return null;
	}

	@Override
	public Void visit(TLASubstitutionKey pGoTLASubstitutionKey) throws IOException {
		out.write("[");
		FormattingTools.writeCommaSeparated(
				out, pGoTLASubstitutionKey.getIndices(), key -> key.accept(new TLAExpressionFormattingVisitor(out)));
		out.write("]");
		return null;
	}

	@Override
	public Void visit(TLARecordSet.Field field) throws IOException {
		field.getName().accept(this);
		out.write(":");
		field.getSet().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLARecordConstructor.Field field) throws IOException {
		field.getName().accept(this);
		out.write(" |-> ");
		field.getValue().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLAQuantifierBound pGoTLAQuantifierBound) throws IOException {
		switch(pGoTLAQuantifierBound.getType()) {
			case IDS:
				FormattingTools.writeCommaSeparated(out, pGoTLAQuantifierBound.getIds(), id -> id.accept(this));
				break;
			case TUPLE:
				out.write("<<");
				FormattingTools.writeCommaSeparated(out, pGoTLAQuantifierBound.getIds(), id -> id.accept(this));
				out.write(">>");
				break;
			default:
				throw new Unreachable();
		}
		out.write(" \\in ");
		pGoTLAQuantifierBound.getSet().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLAInstance.Remapping remapping) throws IOException {
		remapping.getFrom().accept(this);
		out.write(" <- ");
		remapping.getTo().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLAIdentifierOrTuple pGoTLAIdentifierOrTuple) throws IOException {
		if(pGoTLAIdentifierOrTuple.isTuple()) {
			out.write("<<");
			FormattingTools.writeCommaSeparated(out, pGoTLAIdentifierOrTuple.getTuple(), elem -> elem.accept(this));
			out.write(">>");

		}else {
			pGoTLAIdentifierOrTuple.getId().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLAIdentifier pGoTLAIdentifier) throws IOException {
		out.write(pGoTLAIdentifier.getId());
		return null;
	}

	@Override
	public Void visit(TLAGeneralIdentifierPart pGoTLAGeneralIdentifierPart) throws IOException {
		pGoTLAGeneralIdentifierPart.getIdentifier().accept(this);
		List<TLAExpression> params = pGoTLAGeneralIdentifierPart.getParameters();
		if(!params.isEmpty()) {
			out.write("(");
			FormattingTools.writeCommaSeparated(
					out, params, param -> param.accept(new TLAExpressionFormattingVisitor(out)));
			out.write(")");
		}
		out.write("!");
		return null;
	}

	@Override
	public Void visit(TLAFunctionSubstitutionPair pGoTLAFunctionSubstitutionPair) throws IOException {
		out.write("!");
		for(TLASubstitutionKey key : pGoTLAFunctionSubstitutionPair.getKeys()) {
			key.accept(this);
		}
		out.write(" = ");
		pGoTLAFunctionSubstitutionPair.getValue().accept(new TLAExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TLASymbol pGoTLASymbol) throws IOException {
		out.write(pGoTLASymbol.getValue());
		return null;
	}

}
