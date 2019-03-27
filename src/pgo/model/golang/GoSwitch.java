package pgo.model.golang;

import pgo.InternalCompilerError;
import pgo.model.golang.type.GoTypeName;

import java.util.List;
import java.util.Objects;

public class GoSwitch extends GoStatement {
    private GoExpression switchExp;
	private List<GoSwitchCase> cases;
	private List<GoStatement> defaultBlock;

	public static GoSwitch typeSwitch(GoExpression exp, List<GoSwitchCase> cases, List<GoStatement> defaultBlock) {
		// sanity check: in a type switch, all cases should be types.
		cases.forEach(c -> {
			if (!c.isTypeCase()) {
				throw new InternalCompilerError();
			}
		});

		GoExpression switchExp = new GoTypeCast(new GoTypeName("type"), exp);
		return new GoSwitch(switchExp, cases, defaultBlock);
	}

	public GoSwitch(GoExpression exp, List<GoSwitchCase> cases, List<GoStatement> defaultBlock) {
		this.switchExp = exp;
		this.cases = cases;
		this.defaultBlock = defaultBlock;
	}

    public GoExpression getCondition() {
    	return switchExp;
    }
    
    public List<GoSwitchCase> getCases(){
    	return cases;
    }
    
    public List<GoStatement> getDefaultBlock() {
    	return defaultBlock;
    }

    @Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoSwitch aSwitch = (GoSwitch) o;
		return Objects.equals(switchExp, aSwitch.switchExp) &&
				Objects.equals(cases, aSwitch.cases) &&
				Objects.equals(defaultBlock, aSwitch.defaultBlock);
	}

	@Override
	public int hashCode() {

		return Objects.hash(switchExp, cases, defaultBlock);
	}
}
