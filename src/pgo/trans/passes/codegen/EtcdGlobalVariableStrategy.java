package pgo.trans.passes.codegen;

import pgo.PGoNetOptions;
import pgo.Unreachable;
import pgo.model.golang.*;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.PcalProcess;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.GlobalVariableStrategy;

import java.util.*;
import java.util.stream.Collectors;

public class EtcdGlobalVariableStrategy extends GlobalVariableStrategy {
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private PGoNetOptions.StateOptions stateOptions;
	private Algorithm algorithm;
	private GoCommandLineArgumentParser commandLineArgumentParser;
	private UID processNameUID;
	private UID processArgumentUID;
	private UID errUID;
	private UID globalStateUID;

	public EtcdGlobalVariableStrategy(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                  PGoNetOptions.StateOptions stateOptions, Algorithm algorithm) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.stateOptions = stateOptions;
		this.algorithm = algorithm;
		this.commandLineArgumentParser = new GoCommandLineArgumentParser();
		this.processNameUID = new UID();
		this.processArgumentUID = new UID();
		this.errUID = new UID();
		this.globalStateUID = new UID();
	}

	@Override
	public void initPostlude(ModuleBuilder moduleBuilder, BlockBuilder initBuilder) {
		VariableName processName = moduleBuilder.defineGlobal(processNameUID, "processName", Builtins.String);
		addVariable(processNameUID, processName);
		VariableName processArgument = moduleBuilder.defineGlobal(processArgumentUID, "processArgument", Builtins.String);
		addVariable(processArgumentUID, processArgument);
		commandLineArgumentParser.addPositionalArgument("processPlusArgument", "processName(processArgument)");
		commandLineArgumentParser.addPositionalArgument("ipPort", "ip:port");
		List<VariableName> commandLineArguments = commandLineArgumentParser.generateArgumentParsingCode(initBuilder);
		VariableName processPlusArgument = commandLineArguments.get(0);
		VariableName ipPort = commandLineArguments.get(1);
		CodeGenUtil.generateArgumentParsing(initBuilder, processPlusArgument, processName, processArgument);

		moduleBuilder.addImport("pgo/distsys");
		VariableName err = moduleBuilder.defineGlobal(errUID, "err", Builtins.Error);
		addVariable(errUID, err);
		VariableName globalState = moduleBuilder.defineGlobal(
				globalStateUID, "globalState", new PtrType(new TypeName("distsys.EtcdState")));
		addVariable(globalStateUID, globalState);
		VariableName peers = initBuilder.varDecl(
				"peers",
				new SliceLiteral(
						Builtins.String,
						stateOptions.peers.stream().map(StringLiteral::new) .collect(Collectors.toList())));
		VariableName coordinator = initBuilder.varDecl("coordinator", new Index(peers, new IntLiteral(0)));
		initBuilder.assign(
				Arrays.asList(globalState, err),
				new Call(
						new Selector(new VariableName("distsys"), "NewEtcdState"),
						Arrays.asList(
								new SliceLiteral(
										Builtins.String,
										stateOptions.endpoints.stream()
												.map(e -> new StringLiteral("http://" + e))
												.collect(Collectors.toList())),
								new IntLiteral(stateOptions.timeout),
								peers,
								ipPort,
								coordinator,
								new MapLiteral(
										Builtins.String,
										Builtins.Interface,
										new HashMap<Expression, Expression>() {{
											for (UID varUID : registry.protectedGlobalVariables()) {
												VariableName variableName = initBuilder.findUID(varUID);
												put(new StringLiteral(variableName.getName()), variableName);
											}
										}}))));
		try (IfBuilder ifBuilder = initBuilder.ifStmt(new Binop(Binop.Operation.NEQ, err, Builtins.Nil))) {
			try (BlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(err);
			}
		}
	}

	@Override
	public void processPrelude(BlockBuilder processBody, PcalProcess process, String processName, VariableName self, Type selfType) {
		VariableName selfStr;
		if (selfType.equals(Builtins.Int)) {
			// selfStr := "processName(" + strconv.Itoa(self) + ")"
			processBody.addImport("strconv");
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
		} else if (selfType.equals(Builtins.String)) {
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
		} else {
			throw new Unreachable();
		}
		addVariable(process.getName().getUID(), selfStr);
	}

	@Override
	public void mainPrelude(BlockBuilder builder) {
		StateServerGlobalVariableStrategy.generateProcessSwitch(
				typeMap, algorithm, builder, findVariable(processNameUID), findVariable(processArgumentUID));
	}

	@Override
	public void startCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		Set<UID> readSet = new HashSet<>(registry.getVariableReadsInLockGroup(lockGroup));
		Set<UID> writeSet = registry.getVariableWritesInLockGroup(lockGroup);
		readSet.removeAll(writeSet);
		VariableName globalState = findVariable(globalStateUID);
		builder.addStatement(new Call(
				new Selector(findVariable(globalStateUID), "Lock"),
				Arrays.asList(findVariable(processUID), new StringLiteral(Integer.toString(lockGroup)))));
		for (UID varUID : writeSet) {
			VariableName variableName = builder.findUID(varUID);
			builder.addStatement(new Call(
					new Selector(globalState, "Get"),
					Arrays.asList(
							new StringLiteral(variableName.getName()),
							new Unary(Unary.Operation.ADDR, variableName))));
		}
		for (UID varUID : readSet) {
			VariableName variableName = builder.findUID(varUID);
			builder.addStatement(new Call(
					new Selector(globalState, "Get"),
					Arrays.asList(
							new StringLiteral(variableName.getName()),
							new Unary(Unary.Operation.ADDR, variableName))));
		}
	}

	@Override
	public void abortCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		builder.addStatement(new Call(
				new Selector(findVariable(globalStateUID), "Unlock"),
				Arrays.asList(findVariable(processUID), new StringLiteral(Integer.toString(lockGroup)))));
	}

	@Override
	public void endCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		VariableName globalState = findVariable(globalStateUID);
		for (UID varUID : registry.getVariableWritesInLockGroup(lockGroup)) {
			VariableName variableName = builder.findUID(varUID);
			builder.addStatement(new Call(
					new Selector(globalState, "Set"),
					Arrays.asList(
							new StringLiteral(variableName.getName()),
							variableName)));
		}
		builder.addStatement(new Call(
				new Selector(findVariable(globalStateUID), "Unlock"),
				Arrays.asList(findVariable(processUID), new StringLiteral(Integer.toString(lockGroup)))));
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

			}
		};
	}
}
