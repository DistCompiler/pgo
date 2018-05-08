package pgo.model.golang;

import java.util.LinkedHashMap;

public class Switch extends Statement {
    Expression switchExp;
    LinkedHashMap<Expression, Statement> cases;
    Statement defaultCase;

    public Switch(Expression exp) {
        this.switchExp = exp;
        this.cases = new LinkedHashMap<>();
    }
    
    public Expression getCondition() {
    	return switchExp;
    }
    
    public LinkedHashMap<Expression, Statement> getCases(){
    	return cases;
    }
    
    public Statement getDefaultCase() {
    	return defaultCase;
    }

    public void addCase(Expression exp, Statement code) {
        cases.put(exp, code);
    }

    public void addDefaultCase(Statement code) {
        defaultCase = code;
    }

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

}
