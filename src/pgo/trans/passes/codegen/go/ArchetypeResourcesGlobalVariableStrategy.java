package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.GoMapType;
import pgo.model.golang.type.GoSliceType;
import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeName;
import pgo.model.pcal.PlusCalProcess;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAFunctionCall;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

public class ArchetypeResourcesGlobalVariableStrategy extends GlobalVariableStrategy {
    private DefinitionRegistry registry;
    private Map<TLAExpression, GoExpression> resourceExpressions;
    private Map<UID, PGoType> typeMap;
    private GoVariableName err;
    private GoVariableName distsys;

    public ArchetypeResourcesGlobalVariableStrategy(DefinitionRegistry registry, Map<UID, PGoType> typeMap) {
        this.registry = registry;
        this.typeMap = typeMap;
        this.resourceExpressions = new HashMap<>();
        this.distsys = new GoVariableName("distsys");
    }

    @Override
    public void initPostlude(GoModuleBuilder moduleBuilder, GoBlockBuilder initBuilder) {
        throw new TODO();
    }

    @Override
    public void processPrelude(GoBlockBuilder builder, PlusCalProcess ignored, String archetypeName, GoVariableName self, GoType selfType) {
        this.err = builder.varDecl("err", GoBuiltins.Error);
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
            } else if (e instanceof TLAFunctionCall) {
                TLAFunctionCall fnCall = (TLAFunctionCall) e;

                // archetype resources are functions with only one parameter
                // necessarily
                if (fnCall.getParams().size() != 1) {
                    throw new InternalCompilerError();
                }

                TLAExpressionCodeGenVisitor codegen = new TLAExpressionCodeGenVisitor(builder, registry, typeMap, this);
                resource = new GoIndexExpression(
                        fnCall.getFunction().accept(codegen),
                        fnCall.getParams().get(0).accept(codegen)
                );
            } else {
                throw new Unreachable();
            }

            this.resourceExpressions.put(e, resource);
            s.add(resource);
        };

        Set<GoExpression> readExps = new HashSet<>();
        Set<GoExpression> writeExps = new HashSet<>();

        registry.getResourceReadsInLockGroup(lockGroup).forEach(generateLocalBinding.apply(readExps));
        registry.getResourceWritesInLockGroup(lockGroup).forEach(generateLocalBinding.apply(writeExps));

        // err = distsys.AcquireResources(distys.READ_ACCESS, ...{readExps})
        // if err != nil { return err }
        BiConsumer<String, Set<GoExpression>> acquire = (permission, resources) -> {
            if (resources.size() > 0) {
                ArrayList<GoExpression> args = new ArrayList<>(
                        Arrays.asList(new GoSelectorExpression(distsys, permission))
                );
                args.addAll(resources);
                GoExpression acquireCall = new GoCall(new GoSelectorExpression(distsys, "AcquireResources"), args);
                builder.assign(err, acquireCall);
                checkErr(builder);
            }
        };

        acquire.accept("READ_ACCESS", readExps);
        acquire.accept("WRITE_ACCESS", writeExps);
    }

    @Override
    public void abortCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
        throw new TODO();
    }

    @Override
    public void endCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
        Function<Set<TLAExpression>, List<GoExpression>> findVars = (exps) ->
            exps.stream().map(resourceExpressions::get).collect(Collectors.toList());

        List<GoExpression> usedVars = findVars.apply(
                registry.getResourceReadsInLockGroup(lockGroup)
        );
        usedVars.addAll(
                findVars.apply(registry.getResourceWritesInLockGroup(lockGroup))
        );

        if (usedVars.size() > 0) {
            GoExpression release = new GoCall(new GoSelectorExpression(distsys, "ReleaseResources"), usedVars);
            builder.assign(err, release);
            checkErr(builder);
        }
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

        if (resource instanceof TLAGeneralIdentifier) {
            ref = registry.followReference(resource.getUID());
        } else if (resource instanceof TLAFunctionCall) {
            ref = registry.followReference(((TLAFunctionCall) resource).getFunction().getUID());
            isCall = true;
        } else {
            throw new Unreachable();
        }
        GoType readType = registry.getReadValueType(ref).accept(new PGoTypeGoTypeConversionVisitor());

        // if this a function call being mapped, the read type used when casting should be
        // the value you get out of the slice or map inferred by the type system.
        if (isCall) {
            if (readType instanceof GoSliceType) {
                readType = ((GoSliceType) readType).getElementType();
            } else if (readType instanceof GoMapType) {
                readType = ((GoMapType) readType).getValueType();
            } else {
                throw new InternalCompilerError();
            }
        }

        GoExpression target = resourceExpressions.get(resource);
        GoExpression readCall = new GoCall(
                new GoSelectorExpression(target, "Read"),
                Collections.emptyList()
        );

        // only do type casting if the inferred type is meaningful
        if (readType.equals(GoBuiltins.Interface)) {
            return readCall;
        } else {
            return new GoTypeCast(new GoTypeName(readType.toString()), readCall);
        }
    }

    @Override
    public GlobalVariableWrite writeArchetypeResource(GoBlockBuilder builder, TLAExpression resource) {
        GoExpression target = resourceExpressions.get(resource);
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

                builder.addStatement(write);
            }
        };
    }

    private void checkErr(GoBlockBuilder builder) {
        GoExpression errNotNil = new GoBinop(GoBinop.Operation.NEQ, err, GoBuiltins.Nil);
        try (GoIfBuilder ifBuilder = builder.ifStmt(errNotNil)) {
            try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
                yes.returnStmt(err);
            }
        }
    }
}