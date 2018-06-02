package pgo.trans.intermediate;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.PcalProcess;
import pgo.model.type.PGoType;
import pgo.scope.UID;

import java.util.*;

public class MultithreadedProcessGlobalVariableStrategy extends GlobalVariableStrategy {
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private Map<UID, Integer> labelsToLockGroups;
	private Algorithm algorithm;
	private UID pGoLockUID;
	private UID pGoWaitUID;
	private UID pGoStartUID;
	private Map<UID, VariableName> synchronizedVariables;
	private int currentLockGroup;
	private LabelName currentLabelName;

	private static final Type PGO_LOCK_TYPE = new SliceType(new TypeName("sync.Mutex"));

	private void addSynchronizedVariable(UID uid, VariableName name) {
		if (synchronizedVariables.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		synchronizedVariables.put(uid, name);
	}

	private VariableName findSynchronizedVariable(UID uid) {
		if (!synchronizedVariables.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		return synchronizedVariables.get(uid);
	}

	public MultithreadedProcessGlobalVariableStrategy(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                                  Map<UID, Integer> labelsToLockGroups, Algorithm algorithm) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.labelsToLockGroups = labelsToLockGroups;
		this.algorithm = algorithm;
		this.pGoLockUID = new UID();
		this.pGoWaitUID = new UID();
		this.pGoStartUID = new UID();
		this.synchronizedVariables = new HashMap<>();
		this.currentLockGroup = -1;
		this.currentLabelName = null;
	}

	@Override
	public void initPostlude(ModuleBuilder moduleBuilder, BlockBuilder initBuilder) {
		int nLock = 1 + labelsToLockGroups.values().stream()
				.max(Comparator.comparingInt(Integer::intValue))
				.orElse(-1);
		if (nLock <= 0) {
			// nothing to do
			return;
		}
		moduleBuilder.addImport("sync");
		VariableName pGoLock = moduleBuilder.defineGlobal(pGoLockUID, "pGoLock", PGO_LOCK_TYPE);
		addSynchronizedVariable(pGoLockUID, pGoLock);
		initBuilder.assign(pGoLock, new Make(PGO_LOCK_TYPE, new IntLiteral(nLock), null));
		VariableName pGoStart = moduleBuilder.defineGlobal(pGoStartUID, "pGoStart", new ChanType(Builtins.Bool));
		addSynchronizedVariable(pGoStartUID, pGoStart);
		initBuilder.assign(pGoStart, new Make(new ChanType(Builtins.Bool), null, null));
		VariableName pGoWait = moduleBuilder.defineGlobal(pGoWaitUID, "pGoWait", new TypeName("sync.WaitGroup"));
		addSynchronizedVariable(pGoWaitUID, pGoWait);
	}

	@Override
	public void processPrelude(BlockBuilder processBody, PcalProcess process, String processName, VariableName self,
	                           Type selfType) {
		processBody.deferStmt(new Call(
				new Selector(findSynchronizedVariable(pGoWaitUID), "Done"),
				Collections.emptyList()));
		processBody.addStatement(new Unary(Unary.Operation.RECV, findSynchronizedVariable(pGoStartUID)));
		generateLocalVariableDefinitions(registry, typeMap, processBody, process.getVariables());
	}

	@Override
	public void mainPrelude(BlockBuilder builder) {
		for (PcalProcess process : ((MultiProcess) algorithm.getProcesses()).getProcesses()) {
			String processName = process.getName().getName();
			Expression value = process.getName().getValue().accept(
					new TLAExpressionCodeGenVisitor(builder, registry, typeMap, this));
			if (process.getName().isSet()) {
				ForRangeBuilder forRangeBuilder = builder.forRange(value);
				VariableName v = forRangeBuilder.initVariables(Arrays.asList("_", "v")).get(1);
				try (BlockBuilder forBody = forRangeBuilder.getBlockBuilder()) {
					forBody.addStatement(new Call(
							new Selector(findSynchronizedVariable(pGoWaitUID), "Add"),
							Collections.singletonList(new IntLiteral(1))));
					forBody.goStmt(new Call(new VariableName(processName), Collections.singletonList(v)));
				}
				continue;
			}
			builder.addStatement(new Call(
					new Selector(findSynchronizedVariable(pGoWaitUID), "Add"),
					Collections.singletonList(new IntLiteral(1))));
			builder.goStmt(new Call(new VariableName(processName), Collections.singletonList(value)));
		}
		builder.addStatement(new Call(
				new VariableName("close"),
				Collections.singletonList(findSynchronizedVariable(pGoStartUID))));
		VariableName pGoWait = findSynchronizedVariable(pGoWaitUID);
		builder.addStatement(new Call(new Selector(pGoWait, "Wait"), Collections.emptyList()));
	}

	@Override
	public List<FunctionArgument> getExtraProcessArguments() {
		throw new TODO();
	}

	@Override
	public void startCriticalSection(BlockBuilder builder, UID labelUID, LabelName labelName) {
		int lockGroup = labelsToLockGroups.getOrDefault(labelUID, -1);
		if (currentLockGroup != -1 && currentLockGroup != lockGroup) {
			throw new InternalCompilerError();
		}
		if (currentLockGroup == lockGroup) {
			// TODO recursive lock
			return;
		}
		builder.addStatement(new Call(
				new Selector(
						new Index(findSynchronizedVariable(pGoLockUID),
								new IntLiteral(lockGroup)),"Lock"),
				Collections.emptyList()));
		currentLockGroup = lockGroup;
		currentLabelName = labelName;
	}

	@Override
	public void abortCriticalSection(BlockBuilder builder) {
		if (currentLockGroup == -1) {
			// nothing to do
			return;
		}
		builder.addStatement(new Call(
				new Selector(
						new Index(findSynchronizedVariable(pGoLockUID),
								new IntLiteral(currentLockGroup)),"Unlock"),
				Collections.emptyList()));
		builder.goTo(currentLabelName);
	}

	@Override
	public void endCriticalSection(BlockBuilder builder) {
		if (currentLockGroup == -1) {
			// nothing to do
			return;
		}
		builder.addStatement(new Call(
				new Selector(
						new Index(findSynchronizedVariable(pGoLockUID),
								new IntLiteral(currentLockGroup)),"Unlock"),
				Collections.emptyList()));
		currentLockGroup = -1;
		currentLabelName = null;
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
