package pgo.model.golang;

import java.util.List;
import java.util.Objects;

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

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Switch aSwitch = (Switch) o;
		return Objects.equals(switchExp, aSwitch.switchExp) &&
				Objects.equals(cases, aSwitch.cases) &&
				Objects.equals(defaultBlock, aSwitch.defaultBlock);
	}

	@Override
	public int hashCode() {

		return Objects.hash(switchExp, cases, defaultBlock);
	}
}
