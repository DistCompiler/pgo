package pgo.model.golang;

import java.util.List;

public class Switch extends Statement {
    Expression switchExp;
    List<SwitchCase> cases;
    List<Statement> defaultBlock;

    public Switch(Expression exp, List<SwitchCase> cases, List<Statement> defaultBlock) {
        this.switchExp = exp;
        this.cases = cases;
        this.defaultBlock = defaultBlock;
    }
    
    public Expression getCondition() {
    	return switchExp;
    }
    
    public List<SwitchCase> getCases(){
    	return cases;
    }
    
    public List<Statement> getDefaultBlock() {
    	return defaultBlock;
    }

    @Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
