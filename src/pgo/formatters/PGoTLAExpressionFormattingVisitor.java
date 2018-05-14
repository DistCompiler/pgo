package pgo.formatters;

import java.io.IOException;
import java.util.List;

import pgo.model.tla.PGoTLABinOp;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLACase;
import pgo.model.tla.PGoTLAExistential;
import pgo.model.tla.PGoTLAExpression;
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLAExistential pGoTLAExistential) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLAFunction pGoTLAFunction) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws IOException {
		// TODO Auto-generated method stub
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLALet pGoTLALet) throws IOException {
		// TODO Auto-generated method stub
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLANumber pGoTLANumber) throws IOException {
		out.write(pGoTLANumber.getVal());
		return null;
	}

	@Override
	public Void visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLARecordSet pGoTLARecordSet) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLARequiredAction pGoTLARequiredAction) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLASetConstructor pGoTLASetConstructor) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLASetComprehension pGoTLASetComprehension) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(PGoTLASetRefinement pGoTLASetRefinement) throws IOException {
		// TODO Auto-generated method stub
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
		// TODO Auto-generated method stub
		return null;
	}

}
