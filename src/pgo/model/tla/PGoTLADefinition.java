package pgo.model.tla;

import java.util.List;
import java.util.Vector;

import pcal.TLAExpr;
import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoVariable;
import pgo.model.type.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;
import pgo.trans.PGoTransIllegalConversionException;
import pgo.trans.PGoTransIllegalTypeInferenceException;

/**
 * Represents a TLA definition found in an annotation.
 *
 */
public class PGoTLADefinition extends PGoTLAExpression {

	private String name;
	// name and typing information for params
	private List<PGoVariable> params;
	// the expression this definition evaluates to
	private PGoTLAExpression expr;
	// the type that this expression should have
	private PGoType type;

	public PGoTLADefinition(String name, List<PGoVariable> params, TLAExpr expr, PGoType type, int line)
			throws PGoTransException {
		super(line);
		this.name = name;
		this.params = new Vector<>(params);
		TLAExprParser trans = new TLAExprParser(expr, line);
		assert (trans.getResult().size() == 1);
		this.expr = trans.getResult().get(0);
		this.type = type;
	}

	public String getName() {
		return name;
	}

	public Vector<PGoVariable> getParams() {
		return new Vector<>(params);
	}

	public PGoTLAExpression getExpr() {
		return expr;
	}

	public PGoType getType() {
		return type;
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		// This is not an expression, and we shouldn't try to convert it with
		// this translator anyway.
		throw new PGoTransIllegalConversionException("PGoTLADefinition", getLine());
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		// We shouldn't need to determine the type of this.
		throw new PGoTransIllegalTypeInferenceException("PGoTLADefinition", getLine());
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		throw new RuntimeException("walk(PGoTLADefinition) not implemented");
	}

}
