package pgo.model.golang;

import java.util.List;

public class Switch extends Statement {
    Expression switchExp;
    List<SwitchCase> cases;
    Statement defaultCase;

    public Switch(Expression exp, List<SwitchCase> cases, Statement defaultCase) {
        this.switchExp = exp;
        this.cases = cases;
        this.defaultCase = defaultCase;
    }
    
    public Expression getCondition() {
    	return switchExp;
    }
    
    public List<SwitchCase> getCases(){
    	return cases;
    }
    
    public Statement getDefaultCase() {
    	return defaultCase;
    }

    @Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
