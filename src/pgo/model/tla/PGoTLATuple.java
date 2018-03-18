package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * << <expr>, <expr>, ... >>
 *
 */
public class PGoTLATuple extends PGoTLAExpression {

	private List<PGoTLAExpression> exprs;
	
	public PGoTLATuple(int line, List<PGoTLAExpression> exprs) {
		super(line);
		this.exprs = exprs;
	}
	
	public List<PGoTLAExpression> getItems(){
		return exprs;
	}
	
	@Override
	public String toString() {
		return "<<"+String.join(", ", exprs.stream().map(e -> e.toString()).collect(Collectors.toList()))+">>";
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		throw new RuntimeException("convert unimplemented");
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		throw new RuntimeException("inferType unimplemented");
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}

}
