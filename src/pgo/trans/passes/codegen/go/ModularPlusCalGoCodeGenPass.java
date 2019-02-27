package pgo.trans.passes.codegen.go;

import pgo.PGoOptions;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoFunctionDeclarationBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.GoMapType;
import pgo.model.golang.type.GoSliceType;
import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeName;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.tla.TLAExpression;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeMap;
import pgo.model.type.PGoTypeRecord;
import pgo.model.type.PGoTypeSlice;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

public class ModularPlusCalGoCodeGenPass {
    private ModularPlusCalGoCodeGenPass() {}

    private static void generateLocalVariableDefinitions(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
                                                         GlobalVariableStrategy globalStrategy, GoBlockBuilder processBody,
                                                         List<PlusCalVariableDeclaration> variableDeclarations) {
        for (PlusCalVariableDeclaration variableDeclaration : variableDeclarations) {
            GoVariableName name;
            GoType varType;

            if (variableDeclaration.getValue() instanceof PlusCalDefaultInitValue) {
                PGoType inferredType = typeMap.get(variableDeclaration.getUID());

                // if the type of a variable is inferred to be a TLA+ record, use a map[string]interface{}
                // to represent it. This avoids issues around sending and receiving of these variables
                // through different archetype resources (e.g., RPC-based) and wrong casts
                // when we cannot infer the correct type of the message on the receiving end
                if (inferredType instanceof PGoTypeRecord) {
                    varType = new GoMapType(GoBuiltins.String, GoBuiltins.Interface);
                } else {
                    varType = inferredType.accept(new PGoTypeGoTypeConversionVisitor());
                }

                name = processBody.varDecl(variableDeclaration.getName().getValue(), varType);
            } else {
                GoExpression value = variableDeclaration.getValue().accept(
                        new TLAExpressionCodeGenVisitor(processBody, registry, typeMap, globalStrategy));
                if (variableDeclaration.isSet()) {
                    value = new GoIndexExpression(value, new GoIntLiteral(0));
                }

                name = processBody.varDecl(variableDeclaration.getName().getValue(), value);
            }
            processBody.linkUID(variableDeclaration.getUID(), name);
        }
    }

    private static void generateInit(ModularPlusCalBlock modularPlusCalBlock, GoModuleBuilder module, DefinitionRegistry registry, Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {
        Map<String, PGoType> constants = new TreeMap<>(); // sort constants for deterministic compiler output
        Map<String, UID> constantIds = new HashMap<>();
        for (UID uid : registry.getConstants().stream().filter(c -> registry.getConstantValue(c).isPresent()).collect(Collectors.toSet())) {
            String name = registry.getConstantName(uid);
            constants.put(name, typeMap.get(uid));
            constantIds.put(name, uid);
        }

        try (GoBlockBuilder initBuilder = module.defineFunction("init").getBlockBuilder()) {
            // generate constant definitions and initializations
            for (Map.Entry<String, PGoType> pair : constants.entrySet()) {
                // get() here is safe by construction
                TLAExpression value = registry.getConstantValue(constantIds.get(pair.getKey())).get();
                PGoType type = typeMap.get(constantIds.get(pair.getKey()));
                GoVariableName name = module.defineGlobal(
                        constantIds.get(pair.getKey()),
                        pair.getKey(),
                        type.accept(new PGoTypeGoTypeConversionVisitor()));
                initBuilder.assign(
                        name,
                        value.accept(new TLAExpressionCodeGenVisitor(initBuilder, registry, typeMap, globalStrategy)));
            }

            // Given an archetype resource type, returns whether or not TLA+ record support should
            // be registered with the runtime (i.e.. whether the type itself is a record, or a container
            // of records).
            Function<PGoType, Boolean> requiresRecords = type -> {
                if (type instanceof PGoTypeRecord) {
                    return true;
                }

                if (type instanceof PGoTypeSlice) {
                    return ((PGoTypeSlice) type).getElementType() instanceof PGoTypeRecord;
                }

                if (type instanceof PGoTypeMap) {
                    return ((PGoTypeMap) type).getValueType() instanceof PGoTypeRecord;
                }

                return false;
            };

            // if the write type of any archetype resource is a record, define our record representation
            // (map[string]interface{}) with the runtime
            boolean writesRecord = modularPlusCalBlock
                    .getArchetypes()
                    .stream()
                    .map(a -> a.getParams())
                    .flatMap(Collection::stream)
                    .map(varDecl -> varDecl.getUID())
                    .anyMatch(uid -> requiresRecords.apply(registry.getWrittenValueType(uid)) ||
                            requiresRecords.apply(registry.getReadValueType(uid)));

            if (writesRecord) {
                GoExpression register = new GoCall(
                        new GoSelectorExpression(new GoVariableName("distsys"), "DefineCustomType"),
                        Collections.singletonList(
                                new GoMapLiteral(GoBuiltins.String, GoBuiltins.Interface, Collections.emptyMap())
                        )
                );

                initBuilder.addStatement(register);
            }
        }
    }

    public static GoModule perform(DefinitionRegistry registry, Map<UID, PGoType> typeMap, PGoOptions opts,
                                   ModularPlusCalBlock modularPlusCalBlock) {
        GoModuleBuilder module = new GoModuleBuilder(modularPlusCalBlock.getName().getValue(), opts.buildPackage);
        GlobalVariableStrategy globalStrategy = new ArchetypeResourcesGlobalVariableStrategy(registry, typeMap);

        generateInit(modularPlusCalBlock, module, registry, typeMap, globalStrategy);

        for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
            GoFunctionDeclarationBuilder fn = module.defineFunction(archetype.getUID(), archetype.getName());
            fn.addReturn(GoBuiltins.Error);

            Map<String, GoVariableName> argMap = new HashMap<>();

            // all archetypes have a `self` parameter
            GoVariableName selfVariable = fn.addParameter("self", GoBuiltins.Int);
            GoType resourceType = new GoTypeName("distsys.ArchetypeResource");

            for (PlusCalVariableDeclaration arg : archetype.getParams()) {
                module.addImport("pgo/distsys");

                // find out if archetype resource should be passed as a slice if it is used
                // like a TLA+ function in the archetype's body
                GoType argType = resourceType;
                if (typeMap.get(arg.getUID()) instanceof PGoTypeMap) {
                    argType = new GoSliceType(resourceType);
                }

                argMap.put(arg.getName().getValue(), fn.addParameter(arg.getName().getValue(), argType));
            }

            try (GoBlockBuilder fnBody = fn.getBlockBuilder()) {
                // link the 'self' parameter
                fnBody.linkUID(archetype.getSelfVariableUID(), selfVariable);

                for (PlusCalVariableDeclaration arg : archetype.getParams()) {
                    fnBody.linkUID(arg.getUID(), argMap.get(arg.getName().getValue()));
                }

                generateLocalVariableDefinitions(registry, typeMap, globalStrategy, fnBody, archetype.getVariables());

                // TODO: this should probably be a separate method in GlobalVariableStrategy
                globalStrategy.processPrelude(fnBody, null, archetype.getName(), selfVariable, GoBuiltins.Int);

                PlusCalStatementCodeGenVisitor codeGen = new PlusCalStatementCodeGenVisitor(
                        registry, typeMap, globalStrategy, archetype.getUID(), fnBody
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