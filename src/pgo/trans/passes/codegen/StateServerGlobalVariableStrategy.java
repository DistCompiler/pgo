package pgo.trans.passes.codegen;

import pgo.PGoNetOptions;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.*;
import pgo.model.golang.type.MapType;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.PcalProcess;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.GlobalVariableStrategy;
import pgo.trans.intermediate.PGoTypeGoTypeConversionVisitor;

import java.util.*;
import java.util.stream.Collectors;

public class StateServerGlobalVariableStrategy extends GlobalVariableStrategy {
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private PGoNetOptions.StateOptions stateOptions;
	private Algorithm algorithm;
	private GoCommandLineArgumentParser commandLineArgumentParser;
	private UID processNameUID;
	private UID processArgumentUID;
	private UID errUID;
	private UID globalStateUID;
	private UID remoteLockUID;
	private UID remoteVarsUID;

	public StateServerGlobalVariableStrategy(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
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
		this.remoteLockUID = new UID();
		this.remoteVarsUID = new UID();
	}

	static void generateProcessSwitch(Map<UID, PGoType> typeMap, Algorithm algorithm, BlockBuilder builder,
	                                  VariableName processName, VariableName processArgument) {
		try (SwitchBuilder switchBuilder = builder.switchStmt(processName)) {
			for (PcalProcess process : ((MultiProcess) algorithm.getProcesses()).getProcesses()) {
				String name = process.getName().getName();
				Type type = typeMap.get(process.getName().getUID()).accept(new PGoTypeGoTypeConversionVisitor());
				try (BlockBuilder caseBody = switchBuilder.addCase(new StringLiteral(name))) {
					if (type.equals(Builtins.Int)) {
						builder.addImport("strconv");
						List<VariableName> names = caseBody.varDecl(
								Arrays.asList("i", "err"),
								new Call(
										new Selector(new VariableName("strconv"), "Atoi"),
										Collections.singletonList(processArgument)));
						VariableName i = names.get(0);
						VariableName err = names.get(1);
						try (IfBuilder ifBuilder = caseBody.ifStmt(new Binop(Binop.Operation.NEQ, err, Builtins.Nil))) {
							try (BlockBuilder yes = ifBuilder.whenTrue()) {
								yes.addPanic(new Binop(
										Binop.Operation.PLUS,
										new StringLiteral("Process " + name +
												" requires an integer argument; err = "),
										new Call(new Selector(err, "Error"), Collections.emptyList())));
							}
						}
						caseBody.addStatement(new Call(new VariableName(name), Collections.singletonList(i)));
					} else if (type.equals(Builtins.String)) {
						caseBody.addStatement(new Call(
								new VariableName(name),
								Collections.singletonList(processArgument)));
					} else {
						throw new Unreachable();
					}
				}
			}
			try (BlockBuilder defaultCaseBody = switchBuilder.defaultCase()) {
				defaultCaseBody.addPanic(new Binop(
						Binop.Operation.PLUS,
						new StringLiteral("Unknown process "),
						processName));
			}
		}
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
				globalStateUID, "globalState", new TypeName("distsys.StateServer"));
		addVariable(globalStateUID, globalState);
		VariableName peers = initBuilder.varDecl(
				"peers",
				new SliceLiteral(Builtins.String, stateOptions.peers.stream()
						.map(StringLiteral::new)
						.collect(Collectors.toList())));
		VariableName coordinator = initBuilder.varDecl("coordinator", new Index(peers, new IntLiteral(0)));
		initBuilder.assign(
				Arrays.asList(globalState, err),
				new Call(
						new Selector(new VariableName("distsys"), "NewStateServer"),
						Arrays.asList(
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
										}}),
								new Call(
										new Selector(new VariableName("distsys"), "NewRandomMigrate"),
										Collections.singletonList(ipPort)))));
		try (IfBuilder ifBuilder = initBuilder.ifStmt(new Binop(Binop.Operation.NEQ, err, Builtins.Nil))) {
			try (BlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(err);
			}
		}
		VariableName remoteLock = moduleBuilder.defineGlobal(
				remoteLockUID, "remoteLock", new PtrType(new TypeName("distsys.ReleaseSet")));
		addVariable(remoteLockUID, remoteLock);
		VariableName remoteVars = moduleBuilder.defineGlobal(
				remoteVarsUID, "remoteVars", new MapType(Builtins.String, Builtins.Interface));
		addVariable(remoteVarsUID, remoteVars);
	}

	@Override
	public void processPrelude(BlockBuilder processBody, PcalProcess process, String processName, VariableName self, Type selfType) {
		// nothing to do
	}

	@Override
	public void mainPrelude(BlockBuilder builder) {
		generateProcessSwitch(
				typeMap, algorithm, builder, findVariable(processNameUID), findVariable(processArgumentUID));
	}

	@Override
	public void startCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		ArrayList<UID> variableUIDs = new ArrayList<>(registry.getVariablesInLockGroup(lockGroup));
		variableUIDs.sort(Comparator.comparing(a -> builder.findUID(a).getName()));
		List<VariableName> variableNames = variableUIDs.stream().map(builder::findUID).collect(Collectors.toList());
		List<Expression> variableNameStrings = variableNames.stream()
				.map(v -> new StringLiteral(v.getName()))
				.collect(Collectors.toList());
		VariableName remoteVars = findVariable(remoteVarsUID);
		VariableName err = findVariable(errUID);
		builder.assign(
				Arrays.asList(findVariable(remoteLockUID), remoteVars, err),
				new Call(
						new Selector(findVariable(globalStateUID), "Acquire"),
						Collections.singletonList(new StructLiteral(
								new TypeName("distsys.AcquireSet"),
								Arrays.asList(
										new StructLiteralField(
												"ReadNames",
												new SliceLiteral(Builtins.String, variableNameStrings)),
										new StructLiteralField(
												"WriteNames",
												new SliceLiteral(Builtins.String, variableNameStrings)))))));
		try (IfBuilder ifBuilder = builder.ifStmt(new Binop(Binop.Operation.NEQ, err, Builtins.Nil))) {
			try (BlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(err);
			}
		}
		// pull all values out of the map and into globals
		for (int i = 0; i < variableNames.size(); i++) {
			builder.assign(
					variableNames.get(i),
					new TypeAssertion(
							new Index(remoteVars, variableNameStrings.get(i)),
							registry.getGlobalVariableType(variableUIDs.get(i))));
		}
	}

	@Override
	public void abortCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		builder.goTo(labelName);
		throw new TODO();
	}

	@Override
	public void endCriticalSection(BlockBuilder builder, UID processUID, int lockGroup, UID labelUID, LabelName labelName) {
		ArrayList<UID> variableUIDs = new ArrayList<>(registry.getVariablesInLockGroup(lockGroup));
		variableUIDs.sort(Comparator.comparing(a -> builder.findUID(a).getName()));
		List<Expression> arguments = new ArrayList<>();
		arguments.add(findVariable(remoteLockUID));
		for (UID varUID : variableUIDs) {
			arguments.add(builder.findUID(varUID));
		}
		VariableName err = findVariable(errUID);
		builder.assign(err, new Call(new Selector(findVariable(globalStateUID), "Release"), arguments));
		try (IfBuilder ifBuilder = builder.ifStmt(new Binop(Binop.Operation.NEQ, err, Builtins.Nil))) {
			try (BlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(err);
			}
		}
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