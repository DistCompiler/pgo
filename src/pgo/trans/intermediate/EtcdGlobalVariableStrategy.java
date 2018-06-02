package pgo.trans.intermediate;

import pgo.model.golang.*;
import pgo.model.pcal.PcalProcess;
import pgo.scope.UID;

import java.util.Collections;
import java.util.List;

public class EtcdGlobalVariableStrategy extends GlobalVariableStrategy {
	private VariableName selfStr;

	@Override
	public void initPostlude(ModuleBuilder moduleBuilder, BlockBuilder initBuilder) {
		throw new RuntimeException("TODO");
	}

	@Override
	public void processPrelude(BlockBuilder processBody, PcalProcess process, String processName, VariableName self, Type selfType) {
		if (selfType.equals(Builtins.Int)) {
			// selfStr := "processName(" + self + ")"
			selfStr = processBody.varDecl(
					"selfStr",
					new Binop(
							Binop.Operation.PLUS,
							new Binop(
									Binop.Operation.PLUS,
									new StringLiteral(processName + "("),
									self),
							new StringLiteral(")")));
		} else if (selfType.equals(Builtins.String)) {
			processBody.addImport("strconv");
			// selfStr := "processName(" + strconv.Itoa(self) + ")"
			selfStr = processBody.varDecl(
					"selfStr",
					new Binop(
							Binop.Operation.PLUS,
							new Binop(
									Binop.Operation.PLUS,
									new StringLiteral(processName + "("),
									new Call(
											new Selector(new VariableName("strconv"), "Itoa"),
											Collections.singletonList(self))),
							new StringLiteral(")")));
		} else {
			throw new RuntimeException("unreachable");
		}
	}

	@Override
	public void mainPrelude(BlockBuilder builder) {
		throw new RuntimeException("TODO");
	}

	@Override
	public List<FunctionArgument> getExtraProcessArguments() {
		throw new RuntimeException("TODO");
	}

	@Override
	public void startCriticalSection(BlockBuilder builder, UID labelUID, LabelName labelName) {
		throw new RuntimeException("TODO");
	}

	@Override
	public void abortCriticalSection(BlockBuilder builder) {
		throw new RuntimeException("TODO");
	}

	@Override
	public void endCriticalSection(BlockBuilder builder) {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression readGlobalVariable(BlockBuilder builder, UID uid) {
		throw new RuntimeException("TODO");
	}

	@Override
	public GlobalVariableWrite writeGlobalVariable(UID uid) {
		throw new RuntimeException("TODO");
	}

}
