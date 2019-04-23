package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.PGoOptions;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoFunctionDeclarationBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.GoMapType;
import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeName;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalNode;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.tla.TLAExpression;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

public class ModularPlusCalGoCodeGenPass {
    private ModularPlusCalGoCodeGenPass() {}

    private static void generateLocalVariableDefinitions(DefinitionRegistry registry, Map<UID, Type> typeMap, LocalVariableStrategy localStrategy,
                                                         GlobalVariableStrategy globalStrategy, GoBlockBuilder processBody,
                                                         List<PlusCalVariableDeclaration> variableDeclarations) {
        for (PlusCalVariableDeclaration variableDeclaration : variableDeclarations) {
            GoVariableName name;
            GoType varType;

            if (variableDeclaration.getValue() instanceof PlusCalDefaultInitValue) {
                Type inferredType = typeMap.get(variableDeclaration.getUID());

                varType = inferredType.accept(new TypeConversionVisitor());
                name = processBody.varDecl(variableDeclaration.getName().getValue(), varType);
            } else {
                GoExpression value = variableDeclaration.getValue().accept(
                        new TLAExpressionCodeGenVisitor(processBody, registry, typeMap, localStrategy, globalStrategy));
                if (variableDeclaration.isSet()) {
                    value = new GoIndexExpression(value, new GoIntLiteral(0));
                }

                name = processBody.varDecl(variableDeclaration.getName().getValue(), value);
            }
            processBody.linkUID(variableDeclaration.getUID(), name);
        }
    }

    private static void generateInit(ModularPlusCalBlock modularPlusCalBlock, GoModuleBuilder module,
                                     DefinitionRegistry registry, Map<UID, Type> typeMap,
                                     LocalVariableStrategy localStrategy, GlobalVariableStrategy globalStrategy) {
        Map<String, Type> constants = new TreeMap<>(); // sort constants for deterministic compiler output
        Map<String, UID> constantIds = new HashMap<>();
        for (UID uid : registry.getConstants().stream().filter(c -> registry.getConstantValue(c).isPresent()).collect(Collectors.toSet())) {
            String name = registry.getConstantName(uid);
            constants.put(name, typeMap.get(uid));
            constantIds.put(name, uid);
        }

        try (GoBlockBuilder initBuilder = module.defineFunction("init").getBlockBuilder()) {
            // generate constant definitions and initializations
            for (Map.Entry<String, Type> pair : constants.entrySet()) {
                // get() here is safe by construction
                TLAExpression value = registry.getConstantValue(constantIds.get(pair.getKey())).get();
                Type type = typeMap.get(constantIds.get(pair.getKey()));
                GoVariableName name = module.defineGlobal(
                        constantIds.get(pair.getKey()),
                        pair.getKey(),
                        type.accept(new TypeConversionVisitor()));
                initBuilder.assign(
                        name,
                        value.accept(new TLAExpressionCodeGenVisitor(initBuilder, registry, typeMap, localStrategy, globalStrategy)));
            }

            // Given an archetype resource type, returns whether or not TLA+ record support should
            // be registered with the runtime (i.e.. whether the type itself is a record, or a container
            // of records).
            Function<Type, Boolean> requiresRecords = type -> {
                if (type instanceof ArchetypeResourceType) {
                    return ((ArchetypeResourceType) type).getReadType() instanceof RecordType ||
                            ((ArchetypeResourceType) type).getWriteType() instanceof RecordType;
                }
                if (type instanceof ArchetypeResourceCollectionType) {
                    return ((ArchetypeResourceCollectionType) type).getReadType() instanceof RecordType ||
                            ((ArchetypeResourceCollectionType) type).getWriteType() instanceof RecordType;
                }
                throw new InternalCompilerError();
            };

            // if the write type of any archetype resource is a record, define our record representation
            // (map[string]interface{}) with the runtime
            boolean writesRecord = modularPlusCalBlock
                    .getInstantiatedArchetypes()
                    .stream()
                    .map(ModularPlusCalArchetype::getParams)
                    .flatMap(Collection::stream)
                    .map(PlusCalNode::getUID)
                    .anyMatch(uid -> requiresRecords.apply(typeMap.get(uid)));

            if (writesRecord) {
                GoExpression registerRecord = new GoCall(
                        new GoSelectorExpression(new GoVariableName("distsys"), "DefineCustomType"),
                        Collections.singletonList(
                                new GoMapLiteral(GoBuiltins.String, GoBuiltins.Interface, Collections.emptyMap())
                        )
                );

                // TODO: we should only register []map[string]interface{} if this is ever transmitted over the wire
                GoExpression registerListOfRecords = new GoCall(
                        new GoSelectorExpression(new GoVariableName("distsys"), "DefineCustomType"),
                        Collections.singletonList(
                                new GoSliceLiteral(
                                        new GoMapType(GoBuiltins.String, GoBuiltins.Interface, Collections.emptyMap()),
                                        Collections.emptyList()
                                )
                        )
                );

                initBuilder.addStatement(registerRecord);
                initBuilder.addStatement(registerListOfRecords);
            }

            // sets rand seed for unique random numbers on every execution
            GoExpression timeNow = new GoCall(
                    new GoSelectorExpression(new GoVariableName("time"), "Now"),
                    Collections.emptyList()
            );
            GoExpression unixNano = new GoCall(
                    new GoSelectorExpression(timeNow, "UnixNano"),
                    Collections.emptyList()
            );
            GoExpression randSeed = new GoCall(
                    new GoSelectorExpression(new GoVariableName("rand"), "Seed"),
                    Collections.singletonList(unixNano)
            );

            initBuilder.addStatement(randSeed);
        }
    }

    // Creates the following function, used to check whether the error
    // returned by an archetype resource implementation should cause the
    // running action to abort, or the entire process should terminate.

    // func shouldRetry(err error) bool {
    // 	switch err.(type) {
    // 	case *distsys.AbortRetryError:
    //     t := rand.Intn(sleepMax - sleepMin) + sleepMin
    //     time.Sleep(time.Duration(t) * time.Millisecond)
    //
    // 		return true
    // 	case *distsys.ResourceInternalError:
    // 		return false
    // 	default:
    //      // Archetype resource should return errors of the previous two types only
    // 		panic(fmt.Sprintf("Invalid error returned by Archetype Resource: %v", err))
    // 	}
    // }
    private static void defineShouldRetry(GoModuleBuilder module, GoVariableName sleepMin, GoVariableName sleepMax) {
        module.addImport("fmt");
        module.addImport("time");
        module.addImport("math/rand");

        GoFunctionDeclarationBuilder builder = module.defineFunction("shouldRetry");
        GoVariableName err = builder.addParameter("err", GoBuiltins.Error);
        builder.addReturn(GoBuiltins.Bool);

        GoExpression sprintf = new GoCall(
                new GoSelectorExpression(new GoVariableName("fmt"), "Sprintf"),
                Arrays.asList(
                        new GoStringLiteral("Invalid error returned by Archetype Resource: %v"),
                        err
                )
        );
        GoExpression panic = new GoCall(new GoVariableName("panic"), Collections.singletonList(sprintf));

        GoType abortRetry = new GoPtrType(new GoTypeName("distsys.AbortRetryError"));
        GoType internalError = new GoPtrType(new GoTypeName("distsys.ResourceInternalError"));

        try (GoBlockBuilder fnBody = builder.getBlockBuilder()) {
            GoExpression rand = new GoCall(
                    new GoSelectorExpression(new GoVariableName("rand"), "Intn"),
                    Collections.singletonList(new GoBinop(GoBinop.Operation.MINUS, sleepMax, sleepMin))
            );
            GoVariableName t = fnBody.varDecl("t", new GoBinop(GoBinop.Operation.PLUS, rand, sleepMin));
            GoExpression tDuration = new GoCall(
                    new GoSelectorExpression(new GoVariableName("time"), "Duration"),
                    Collections.singletonList(t)
            );
            GoExpression millisecond = new GoSelectorExpression(new GoVariableName("time"), "Millisecond");
            GoStatement sleep = new GoExpressionStatement(new GoCall(
                    new GoSelectorExpression(new GoVariableName("time"), "Sleep"),
                    Collections.singletonList(new GoBinop(GoBinop.Operation.TIMES, tDuration, millisecond))
            ));

            List<GoStatement> sleepAndReturn = Arrays.asList(
                    sleep,
                    new GoReturn(Collections.singletonList(GoBuiltins.True))
            );

            fnBody.addStatement(GoSwitch.typeSwitch(
                    err,
                    Arrays.asList(
                            new GoSwitchCase(abortRetry, sleepAndReturn),
                            new GoSwitchCase(internalError, Collections.singletonList(new GoReturn(Collections.singletonList(GoBuiltins.False))))
                    ),
                    Collections.singletonList(new GoExpressionStatement(panic))
                    )
            );
        }
    }

    public static GoModule perform(DefinitionRegistry registry, Map<UID, Type> typeMap, PGoOptions opts,
                                   ModularPlusCalBlock modularPlusCalBlock) {
        GoModuleBuilder module = new GoModuleBuilder(modularPlusCalBlock.getName().getValue(), opts.buildPackage);
        SnapshottingLocalVariableStrategy localStrategy = new SnapshottingLocalVariableStrategy(registry, typeMap);
        GlobalVariableStrategy globalStrategy = new ArchetypeResourcesGlobalVariableStrategy(registry, typeMap, localStrategy, null);

        GoVariableName sleepMin = module.defineGlobal(new UID(), "sleepMin", new GoIntLiteral(100));
        GoVariableName sleepMax = module.defineGlobal(new UID(), "sleepMax", new GoIntLiteral(300));

        generateInit(modularPlusCalBlock, module, registry, typeMap, localStrategy, globalStrategy);
        defineShouldRetry(module, sleepMin, sleepMax);

        for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getInstantiatedArchetypes()) {
            globalStrategy = new ArchetypeResourcesGlobalVariableStrategy(registry, typeMap, localStrategy, archetype.getUID());

            GoFunctionDeclarationBuilder fn = module.defineFunction(archetype.getUID(), archetype.getName());
            fn.addReturn(GoBuiltins.Error);

            Map<String, GoVariableName> argMap = new HashMap<>();

            // all archetypes have a `self` parameter
            GoVariableName selfVariable = fn.addParameter("self", GoBuiltins.Int);

            for (PlusCalVariableDeclaration arg : archetype.getParams()) {
                module.addImport("pgo/distsys");

                // find out if archetype resource should be passed as resource collection
                // if it is used like a TLA+ function in the archetype's body
                GoType argType;
                if (typeMap.get(arg.getUID()) instanceof ArchetypeResourceCollectionType) {
                    argType = new GoTypeName("distsys.ArchetypeResourceCollection");
                } else {
                    argType = new GoTypeName("distsys.ArchetypeResource");
                }

                argMap.put(arg.getName().getValue(), fn.addParameter(arg.getName().getValue(), argType));
            }

            try (GoBlockBuilder fnBody = fn.getBlockBuilder()) {
                // link the 'self' parameter
                fnBody.linkUID(archetype.getSelfVariableUID(), selfVariable);

                for (PlusCalVariableDeclaration arg : archetype.getParams()) {
                    fnBody.linkUID(arg.getUID(), argMap.get(arg.getName().getValue()));
                }

                generateLocalVariableDefinitions(registry, typeMap, localStrategy, globalStrategy, fnBody, archetype.getVariables());
                localStrategy.initArchetype(fnBody, archetype);

                // TODO: this should probably be a separate method in GlobalVariableStrategy
                globalStrategy.processPrelude(fnBody, null, archetype.getName(), selfVariable, GoBuiltins.Int);

                PlusCalStatementCodeGenVisitor codeGen = new PlusCalStatementCodeGenVisitor(
                        registry, typeMap, localStrategy, globalStrategy, archetype.getUID(), fnBody
                );
                for (PlusCalStatement statement : archetype.getBody()) {
                    statement.accept(codeGen);
                }

                fnBody.returnStmt(GoBuiltins.Nil);
            }
        }

        return module.getModule();
    }
}