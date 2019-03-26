package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoForRangeBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.*;
import pgo.model.pcal.PlusCalProcess;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAFunctionCall;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.type.Type;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

public class ArchetypeResourcesGlobalVariableStrategy extends GlobalVariableStrategy {
    private DefinitionRegistry registry;
    private Map<UID, Type> typeMap;
    private LocalVariableStrategy localStrategy;
    private UID archetype;
    private GoVariableName err;
    private GoVariableName acquiredResources;
    private Set<String> functionMappedResourceNames;
    private int currentLockGroup;
    private boolean functionMaps;

    private static final String RELEASE = "ReleaseResources";
    private static final String ABORT = "AbortResources";

    public ArchetypeResourcesGlobalVariableStrategy(DefinitionRegistry registry, Map<UID, Type> typeMap,
                                                    LocalVariableStrategy localStrategy, UID archetype) {
        this.registry = registry;
        this.typeMap = typeMap;
        this.localStrategy = localStrategy;
        this.currentLockGroup = -1;
        this.functionMaps = false;
        this.archetype = archetype;
        this.acquiredResources = null;
    }

    @Override
    public void initPostlude(GoModuleBuilder moduleBuilder, GoBlockBuilder initBuilder) {
        throw new TODO();
    }

    @Override
    public void processPrelude(GoBlockBuilder builder, PlusCalProcess ignored, String archetypeName, GoVariableName self, GoType selfType) {
        this.err = builder.varDecl("err", GoBuiltins.Error);

        if (!registry.getSignature(archetype).isPresent()) {
            throw new InternalCompilerError();
        }

        // if the archetype has any resource that is function-mapped, declared archetypeResources
        // to keep track of acquired resources for each lock group
        boolean[] signature = registry.getSignature(archetype).get();
        for (int i = 0; i < signature.length; i++) {
            if (signature[i]) {
                functionMaps = true;
                break;
            }
        }

        if (functionMaps) {
            GoType type = new GoMapType(
                    GoBuiltins.String,
                    new GoMapType(GoBuiltins.Interface, GoBuiltins.Bool)
            );

            this.acquiredResources = builder.varDecl("acquiredResources", type);
        }
    }

    @Override
    public void mainPrelude(GoBlockBuilder builder) {
        throw new TODO();
    }

    @Override
    public void startCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
        Function<Set<GoExpression>, Consumer<TLAExpression>> generateLocalBinding = s -> e -> {
            GoExpression resource;

            if (e instanceof TLAGeneralIdentifier) {
                resource = builder.findUID(registry.followReference(e.getUID()));
                s.add(resource);
            } else if (!(e instanceof TLAFunctionCall)) {
                throw new Unreachable();
            }
        };

        Set<GoExpression> readExps = new HashSet<>();
        Set<GoExpression> writeExps = new HashSet<>();

        registry.getResourceReadsInLockGroup(lockGroup).forEach(generateLocalBinding.apply(readExps));
        registry.getResourceWritesInLockGroup(lockGroup).forEach(generateLocalBinding.apply(writeExps));

        // err = distsys.AcquireResources(distys.READ_ACCESS, ...{readExps})
        // if err != nil { return err }
        BiConsumer<String, Set<GoExpression>> acquire = (permission, resources) -> {
            if (!resources.isEmpty()) {
                ArrayList<GoExpression> args = new ArrayList<>(
                        Arrays.asList(distsys(permission))
                );
                args.addAll(resources);
                GoExpression acquireCall = new GoCall(distsys("AcquireResources"), args);
                builder.assign(err, acquireCall);
                checkErr(builder);
            }
        };

        // reset acquired resources
        if (functionMaps) {
            builder.assign(
                    acquiredResources,
                    new GoMapLiteral(
                            GoBuiltins.String,
                            new GoMapType(GoBuiltins.Interface, GoBuiltins.Bool), Collections.emptyMap()
                    )
            );
        }

        // keeps track of the function-mapped resources read or written
        // in this label so that they can be released at the end of the label.
        this.functionMappedResourceNames = new HashSet<>();

        // keep track of the current lock group so that function-mapped
        // resources can be properly acquired when accessed
        this.currentLockGroup = lockGroup;

        localStrategy.actionPrelude(builder, labelUID);

        acquire.accept("READ_ACCESS", readExps);
        acquire.accept("WRITE_ACCESS", writeExps);
    }

    @Override
    public void abortCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
        terminateCriticalSection(builder, lockGroup, ABORT, false);
    }

    @Override
    public void endCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
        terminateCriticalSection(builder, lockGroup, RELEASE, false);
        localStrategy.actionPostlude(builder, labelUID);
    }

    @Override
    public GoExpression readGlobalVariable(GoBlockBuilder builder, UID uid) {
        throw new TODO();
    }

    @Override
    public GlobalVariableWrite writeGlobalVariable(UID uid) {
        throw new TODO();
    }

    @Override
    public GoExpression readArchetypeResource(GoBlockBuilder builder, TLAExpression resource) {
        UID ref;
        boolean isCall = false;
        GoExpression target;

        if (resource instanceof TLAGeneralIdentifier) {
            ref = registry.followReference(resource.getUID());
            target = builder.findUID(ref);
        } else if (resource instanceof TLAFunctionCall) {
            ref = registry.followReference(((TLAFunctionCall) resource).getFunction().getUID());
            TLAFunctionCall fnCall = (TLAFunctionCall) resource;

            target = ensureResourceAcquired(builder, fnCall);
            isCall = true;
        } else {
            throw new Unreachable();
        }

        GoType resourceType = typeMap.get(ref).accept(new TypeConversionVisitor());

        // if this a function call being mapped, the read type used when casting should be
        // the value you get out of the slice or map inferred by the type system.
        GoType readType;
        if (isCall) {
            readType = ((GoArchetypeResourceCollectionType) resourceType).getReadType();
        } else {
            readType = ((GoArchetypeResourceType) resourceType).getReadType();
        }

        // if the read type is inferred to be a TLA+ record, use a map[string]interface{}
        // to represent it instead
        if (readType instanceof GoStructType) {
            readType = new GoMapType(GoBuiltins.String, GoBuiltins.Interface);
        }

        GoExpression readCall = new GoCall(
                new GoSelectorExpression(target, "Read"),
                Collections.emptyList()
        );

        GoVariableName readTemp = builder.varDecl("readTemp", GoBuiltins.Interface);
        GoStatement assignRead = new GoAssignmentStatement(
                Arrays.asList(readTemp, err),
                false,
                Collections.singletonList(readCall)
        );
        builder.addStatement(assignRead);
        checkErr(builder);

        // only do type casting if the inferred type is meaningful
        if (readType.equals(GoBuiltins.Interface)) {
            return readTemp;
        } else {
            return new GoTypeCast(new GoTypeName(readType.toString()), readTemp);
        }
    }

    @Override
    public GlobalVariableWrite writeArchetypeResource(GoBlockBuilder builder, TLAExpression resource) {
        GoExpression target = getResource(builder, resource);
        GoVariableName tempVar = builder.varDecl("resourceWrite", GoBuiltins.Interface);

        return new GlobalVariableWrite() {
            @Override
            public GoExpression getValueSink(GoBlockBuilder builder) {
                return tempVar;
            }

            @Override
            public void writeAfter(GoBlockBuilder builder) {
                GoExpression write = new GoCall(
                        new GoSelectorExpression(target, "Write"),
                        Collections.singletonList(tempVar)
                );
                builder.assign(err, write);
                checkErr(builder);
            }
        };
    }

    private void checkErr(GoBlockBuilder builder) {
        GoExpression errNotNil = new GoBinop(GoBinop.Operation.NEQ, err, GoBuiltins.Nil);
        try (GoIfBuilder ifBuilder = builder.ifStmt(errNotNil)) {
            try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
                terminateCriticalSection(yes, currentLockGroup, ABORT, true);
                yes.returnStmt(err);
            }
        }
    }

    private GoSelectorExpression distsys(String target) {
        return new GoSelectorExpression(
                new GoVariableName("distsys"),
                target
        );
    }

        // Releases/aborts resources
    private void terminateCriticalSection(GoBlockBuilder builder, int lockGroup, String method, boolean isError) {
        if (currentLockGroup != lockGroup) {
            throw new InternalCompilerError();
        }

        // release all non-function mapped resources in order
        Set<TLAExpression> varMapped = new HashSet<>();
        Consumer<TLAExpression> collectVariableMapped = e -> {
            if (e instanceof TLAGeneralIdentifier) {
                varMapped.add(e);
            }
        };

        registry.getResourceReadsInLockGroup(currentLockGroup).forEach(collectVariableMapped);
        registry.getResourceWritesInLockGroup(currentLockGroup).forEach(collectVariableMapped);

        List<GoExpression> varMappedExpressions = varMapped
                .stream()
                .map(e -> this.getResource(builder, e))
                .collect(Collectors.toList());

        if (varMapped.size() > 0) {
            GoExpression release = new GoCall(distsys(method), varMappedExpressions);

            // do not assign to `err` variable if inside an error handling situation
            if (isError) {
                builder.addStatement(release);
            } else {
                builder.assign(err, release);
                checkErr(builder);
            }
        }

        // release each function mapped resource used in this label
        for (String resourceName : functionMappedResourceNames) {
            // for _, r := range acquiredResources["{name}"] {
            //     releaseResource(r)
            // }

            GoExpression resources = new GoIndexExpression(acquiredResources, new GoStringLiteral(resourceName));
            GoForRangeBuilder rangeBuilder = builder.forRange(resources);
            GoVariableName r = rangeBuilder.initVariables(Arrays.asList("r", "_")).get(0);
            try (GoBlockBuilder rangeBody = rangeBuilder.getBlockBuilder()) {
                GoExpression resourceGet = new GoCall(
                        new GoSelectorExpression(new GoVariableName(resourceName), "Get"),
                        Collections.singletonList(r)
                );

                GoExpression release = new GoCall(distsys(method), Collections.singletonList(resourceGet));

                if (isError) {
                    rangeBody.addStatement(release);
                } else {
                    rangeBody.assign(err, release);
                    checkErr(rangeBody);
                }
            }
        }
    }

    // Ensures that a function-mapped resource has been acquired before use:
    //
    // if ~(arg \in acquiredResources) {
    //     call distsys.AcquireResources()
    //     add resource to acquiredResources
    // }
    private GoExpression ensureResourceAcquired(GoBlockBuilder builder, TLAFunctionCall fnCall) {
        // archetype resources are functions with only one argument,
        // necessarily
        if (fnCall.getParams().size() != 1) {
            throw new InternalCompilerError();
        }

        TLAExpression arg = fnCall.getParams().get(0);
        GoExpression goArg = codegen(builder, arg);

        String resourceName;
        if (fnCall.getFunction() instanceof TLAGeneralIdentifier) {
            resourceName = ((TLAGeneralIdentifier) fnCall.getFunction()).getName().getId();
        } else {
            throw new InternalCompilerError();
        }

        functionMappedResourceNames.add(resourceName);

        // if _, ok := acquiredResources["{name}"]; !ok {
        //     acquiredResources["{name}"] = []interface{}{}
        // }
        // {name}Acquired := acquiredResources["{name}"]
        GoExpression currentlyAcquired = new GoIndexExpression(acquiredResources, new GoStringLiteral(resourceName));
        try (GoIfBuilder ifBuilder = builder.ifStmt(null)) {
            GoVariableName ok = ifBuilder.initialAssignment(Arrays.asList("_", "ok"), currentlyAcquired).get(1);
            ifBuilder.setCondition(new GoUnary(GoUnary.Operation.NOT, ok));

            try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
                yes.assign(
                        currentlyAcquired,
                        new GoMapLiteral(GoBuiltins.Interface, GoBuiltins.Bool, Collections.emptyMap())
                );
            }
        }

        GoExpression resourceGet = new GoCall(
                new GoSelectorExpression(codegen(builder, fnCall.getFunction()), "Get"),
                Collections.singletonList(goArg)
        );

        try (GoIfBuilder ifBuilder = builder.ifStmt(null)) {
            GoExpression argAcquired = new GoIndexExpression(currentlyAcquired, goArg);
            GoVariableName acquired = ifBuilder.initialAssignment(Arrays.asList("_", "acquired"), argAcquired).get(1);

            ifBuilder.setCondition(new GoUnary(GoUnary.Operation.NOT, acquired));

            try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
                String permission;

                if (registry.getResourceReadsInLockGroup(currentLockGroup).contains(fnCall)) {
                    permission = "READ_ACCESS";
                } else if (registry.getResourceWritesInLockGroup(currentLockGroup).contains(fnCall)) {
                    permission = "WRITE_ACCESS";
                } else {
                    throw new InternalCompilerError();
                }

                yes.assign(err, new GoCall(
                        distsys("AcquireResources"),
                        Arrays.asList(
                                distsys(permission),
                                resourceGet
                        )
                ));
                checkErr(yes);

                yes.assign(argAcquired, GoBuiltins.True);
            }
        }

        return resourceGet;
    }

    private GoExpression getResource(GoBlockBuilder builder, TLAExpression resource) {
        if (resource instanceof TLAGeneralIdentifier) {
            UID ref = registry.followReference(resource.getUID());
            return builder.findUID(ref);
        } else if (resource instanceof TLAFunctionCall) {
            TLAFunctionCall fnCall = (TLAFunctionCall) resource;
            return ensureResourceAcquired(builder, fnCall);
        } else {
            throw new Unreachable();
        }
    }

    private GoExpression codegen(GoBlockBuilder builder, TLAExpression e) {
        return e.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, localStrategy, this));
    }
}