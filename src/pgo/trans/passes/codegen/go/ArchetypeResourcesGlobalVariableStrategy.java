package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.GoType;
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
    private Map<TLAExpression, GoVariableName> resourceVariables;
    private Map<UID, PGoType> typeMap;
    private GoVariableName err;
    private GoVariableName distsys;

    public ArchetypeResourcesGlobalVariableStrategy(DefinitionRegistry registry, Map<UID, PGoType> typeMap) {
        this.registry = registry;
        this.typeMap = typeMap;
        this.resourceVariables = new HashMap<>();
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
        Function<Set<GoVariableName>, Consumer<TLAExpression>> generateLocalBinding = s -> e -> {
            GoVariableName name;

            if (e instanceof TLAGeneralIdentifier) {
                name = builder.findUID(registry.followReference(e.getUID()));
            } else if (e instanceof TLAFunctionCall) {
                TLAFunctionCall fnCall = (TLAFunctionCall) e;

                // archetype resources are functions with only one parameter
                // necessarily
                if (fnCall.getParams().size() != 1) {
                    throw new InternalCompilerError();
                }

                TLAExpressionCodeGenVisitor codegen = new TLAExpressionCodeGenVisitor(builder, registry, typeMap, this);
                GoExpression index = new GoIndexExpression(
                        fnCall.getFunction().accept(codegen),
                        fnCall.getParams().get(0).accept(codegen)
                );

                name = builder.varDecl("archetypeResource", index);
            } else {
                throw new Unreachable();
            }

            this.resourceVariables.put(e, name);
            s.add(name);
        };

        Set<GoVariableName> readVars = new HashSet<>();
        Set<GoVariableName> writeVars = new HashSet<>();

        registry.getResourceReadsInLockGroup(lockGroup).forEach(generateLocalBinding.apply(readVars));
        registry.getResourceWritesInLockGroup(lockGroup).forEach(generateLocalBinding.apply(writeVars));

        // err = distsys.AcquireResources(distys.READ_ACCESS, ...{readVars})
        // if err != nil { return err }
        BiConsumer<String, Set<GoVariableName>> acquire = (permission, resources) -> {
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

        acquire.accept("READ_ACCESS", readVars);
        acquire.accept("WRITE_ACCESS", writeVars);
    }

    @Override
    public void abortCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
        throw new TODO();
    }

    @Override
    public void endCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
        Function<Set<TLAExpression>, List<GoExpression>> findVars = (exps) ->
            exps.stream().map(resourceVariables::get).collect(Collectors.toList());

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

    private void checkErr(GoBlockBuilder builder) {
        GoExpression errNotNil = new GoBinop(GoBinop.Operation.NEQ, err, GoBuiltins.Nil);
        try (GoIfBuilder ifBuilder = builder.ifStmt(errNotNil)) {
            try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
                yes.returnStmt(err);
            }
        }
    }
}