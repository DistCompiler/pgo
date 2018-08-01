package pgo.trans.passes.codegen;

import pgo.model.golang.*;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.PcalProcess;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.GlobalVariableStrategy;
import pgo.trans.intermediate.TLAExpressionCodeGenVisitor;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

// FIXME this strategy, for efficiency reasons, does not implement abortCriticalSection correctly
public class MultithreadedProcessGlobalVariableStrategy extends GlobalVariableStrategy {
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private Algorithm algorithm;
	private UID pGoLockUID;
	private UID pGoWaitUID;
	private UID pGoStartUID;

	private static final Type PGO_LOCK_TYPE = new SliceType(new TypeName("sync.RWMutex"));

	public MultithreadedProcessGlobalVariableStrategy(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                                  Algorithm algorithm) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.algorithm = algorithm;
		this.pGoLockUID = new UID();
		this.pGoWaitUID = new UID();
		this.pGoStartUID = new UID();
	}

	@Override
	public void initPostlude(ModuleBuilder moduleBuilder, BlockBuilder initBuilder) {
		int nLock = registry.getNumberOfLockGroups();
		if (nLock <= 0) {
			// nothing to do
			return;
		}
		moduleBuilder.addImport("sync");
		VariableName pGoLock = moduleBuilder.defineGlobal(pGoLockUID, "pGoLock", PGO_LOCK_TYPE);
		addVariable(pGoLockUID, pGoLock);
		initBuilder.assign(pGoLock, new Make(PGO_LOCK_TYPE, new IntLiteral(nLock), null));
		VariableName pGoStart = moduleBuilder.defineGlobal(pGoStartUID, "pGoStart", new ChanType(Builtins.Bool));
		addVariable(pGoStartUID, pGoStart);
		initBuilder.assign(pGoStart, new Make(new ChanType(Builtins.Bool), null, null));
		VariableName pGoWait = moduleBuilder.defineGlobal(pGoWaitUID, "pGoWait", new TypeName("sync.WaitGroup"));
		addVariable(pGoWaitUID, pGoWait);
	}

	@Override
	public void processPrelude(BlockBuilder processBody, PcalProcess process, String processName, VariableName self,
	                           Type selfType) {
		processBody.deferStmt(new Call(
				new Selector(findVariable(pGoWaitUID), "Done"),
				Collections.emptyList()));
		processBody.addStatement(new Unary(Unary.Operation.RECV, findVariable(pGoStartUID)));
	}

	@Override
	public void mainPrelude(BlockBuilder builder) {
		for (PcalProcess process : ((MultiProcess) algorithm.getProcesses()).getProcesses()) {
			String processName = process.getName().getName().getValue();
			Expression value = process.getName().getValue().accept(
					new TLAExpressionCodeGenVisitor(builder, registry, typeMap, this));
			if (process.getName().isSet()) {
				ForRangeBuilder forRangeBuilder = builder.forRange(value);
				VariableName v = forRangeBuilder.initVariables(Arrays.asList("_", "v")).get(1);
				try (BlockBuilder forBody = forRangeBuilder.getBlockBuilder()) {
					forBody.addStatement(new Call(
							new Selector(findVariable(pGoWaitUID), "Add"),
							Collections.singletonList(new IntLiteral(1))));
					forBody.goStmt(new Call(new VariableName(processName), Collections.singletonList(v)));
				}
				continue;
			}
			builder.addStatement(new Call(
					new Selector(findVariable(pGoWaitUID), "Add"),
					Collections.singletonList(new IntLiteral(1))));
			builder.goStmt(new Call(new VariableName(processName), Collections.singletonList(value)));
		}
		builder.addStatement(new Call(
				new VariableName("close"),
				Collections.singletonList(findVariable(pGoStartUID))));
		VariableName pGoWait = findVariable(pGoWaitUID);
		builder.addStatement(new Call(new Selector(pGoWait, "Wait"), Collections.emptyList()));
	}

	@Override
	public void startCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		String functionName = "Lock";
		if (registry.getVariableWritesInLockGroup(lockGroup).isEmpty()) {
			functionName = "RLock";
		}
		builder.addStatement(new Call(
				new Selector(new Index(findVariable(pGoLockUID), new IntLiteral(lockGroup)), functionName),
				Collections.emptyList()));
	}

	@Override
	public void abortCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		// FIXME
		endCriticalSection(builder, processUID, lockGroup, labelUID, labelName);
	}

	@Override
	public void endCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		String functionName = "Unlock";
		if (registry.getVariableWritesInLockGroup(lockGroup).isEmpty()) {
			functionName = "RUnlock";
		}
		builder.addStatement(new Call(
				new Selector(new Index(findVariable(pGoLockUID), new IntLiteral(lockGroup)), functionName),
				Collections.emptyList()));
	}

	@Override
	public Expression readGlobalVariable(BlockBuilder builder, UID uid) {
		return builder.findUID(uid);
	}

	@Override
	public GlobalVariableWrite writeGlobalVariable(UID uid) {
		return new GlobalVariableWrite() {
			@Override
			public Expression getValueSink(BlockBuilder builder) {
				return builder.findUID(uid);
			}

			@Override
			public void writeAfter(BlockBuilder builder) {
				// pass
			}
		};
	}
}
