package pgo.model.tla;

public class PGoTLABackwardsCompatibilityASTConverter extends PGoTLAExpressionVisitor<PGoTLAExpression> {
	public PGoTLABackwardsCompatibilityASTConverter() {}
	
	@Override
	public PGoTLAExpression visit(PGoTLABinOp expr) {
		String op = expr.getOperation();
		
		switch(op) {
			case "+":
			case "-":
			case "*":
			case "/":
			case "\\div":
			case "%":
			case "^":
				return new PGoTLASimpleArithmetic(
						op,
						expr.getLHS().walk(this),
						expr.getRHS().walk(this),
						expr.getLine());
			case "/\\":
			case "\\land":
			case "\\lor":
			case "\\/":
			case "~":
			case "\\lnot":
			case "\\neg":
			case "#":
			case "/=":
			case "<":
			case ">":
			case "<=":
			case "=<":
			case "\\leq":
			case ">=":
			case "\\geq":
			case "==":
			case "=":
				return new PGoTLABoolOp(
						op,
						expr.getLHS().walk(this),
						expr.getLHS().walk(this),
						expr.getLine());
			case "..":
				return new PGoTLASequence(
						expr.getLHS().walk(this),
						expr.getRHS().walk(this),
						expr.getLine());
			default:
				throw new RuntimeException("unimplemented binop conversion for operator "+op);
		}
	}
	
	@Override
	public PGoTLAExpression visit(PGoTLAVariable expr) {
		return expr;
	}
	
	@Override
	public PGoTLAExpression visit(PGoTLATuple expr) {
		return new PGoTLAArray(expr.getItems(), expr.getLine());
	}
	
	@Override
	public PGoTLAExpression visit(PGoTLANumber expr) {
		return expr;
	}
	
	@Override
	public PGoTLAExpression visit(PGoTLAExpression.PGoTLADefault expr) {
		return expr;
	}
	
	@Override
	public PGoTLAExpression visit(PGoTLAOperatorCall expr) {
		// this is semantically wrong, but is understood as such
		// but the rest of the pipeline
		// TODO: fix this
		return new PGoTLAFunctionCall(
				new PGoTLAVariable(expr.getName(), expr.getLine()),
				expr.getArgs(),
				expr.getLine());
	}
}
