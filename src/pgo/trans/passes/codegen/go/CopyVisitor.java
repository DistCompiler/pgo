package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoForRangeBuilder;
import pgo.model.golang.type.*;

import java.util.*;
import java.util.stream.Collectors;

public class CopyVisitor extends GoTypeVisitor<GoVariableName, RuntimeException> {

    private final GoBlockBuilder builder;
    private final GoVariableName source;

    public CopyVisitor(GoBlockBuilder builder, GoVariableName source) {
        this.builder = builder;
        this.source = source;
    }

    private GoVariableName createCopy(GoExpression value) {
        return builder.varDecl(source.getName() + "Copy", value);
    }

    @Override
    public GoVariableName visit(GoTypeName typeName) throws RuntimeException {
        if (typeName.isBuiltin()) {
            return createCopy(source);
        }

        throw new TODO();
    }

    @Override
    public GoVariableName visit(GoArchetypeResourceType archetypeResourceType) throws RuntimeException {
        throw new InternalCompilerError();
    }

    @Override
    public GoVariableName visit(GoArchetypeResourceCollectionType archetypeResourceCollectionType) throws RuntimeException {
        throw new InternalCompilerError();
    }

    @Override
    public GoVariableName visit(GoStructType structType) throws RuntimeException {
        Map<String, GoExpression> memberCopies = new HashMap<>();
        for(GoStructTypeField field : structType.getFields()) {
            GoVariableName fieldVar = builder.varDecl("field", new GoSelectorExpression(source, field.getName()));
            memberCopies.put(field.getName(), field.getType().accept(new CopyVisitor(builder, fieldVar)));
        }

        GoExpression copy = new GoStructLiteral(
                structType,
                structType
                        .getFields()
                        .stream()
                        .map(field -> new GoStructLiteralField(field.getName(), memberCopies.get(field.getName())))
                        .collect(Collectors.toList())
        );

        return createCopy(copy);
    }

    @Override
    public GoVariableName visit(GoPtrType ptrType) throws RuntimeException {
        GoVariableName deref = builder.varDecl("deref", new GoUnary(GoUnary.Operation.DEREF, source));
        return ptrType.getPointee().accept(new CopyVisitor(builder, deref));
    }

    @Override
    public GoVariableName visit(GoSliceType sliceType) throws RuntimeException {
        GoExpression make = new GoMakeExpression(sliceType, new GoCall(new GoVariableName("len"), Collections.singletonList(source)));
        GoVariableName copy = createCopy(make);

        GoForRangeBuilder rangeBuilder = builder.forRange(source);
        List<GoVariableName> initVars = rangeBuilder.initVariables(Arrays.asList("i", "e"));
        GoVariableName i = initVars.get(0);
        GoVariableName e = initVars.get(1);

        try (GoBlockBuilder rangeBody = rangeBuilder.getBlockBuilder()) {
            GoExpression target = new GoIndexExpression(copy, i);

            rangeBody.assign(target, sliceType.getElementType().accept(new CopyVisitor(rangeBody, e)));
        }

        return copy;
    }

    @Override
    public GoVariableName visit(GoChanType chanType) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public GoVariableName visit(GoMapType mapType) throws RuntimeException {
        GoExpression make = new GoMakeExpression(mapType, new GoCall(new GoVariableName("len"), Collections.singletonList(source)));
        GoVariableName copy = createCopy(make);

        GoForRangeBuilder rangeBuilder = builder.forRange(source);
        List<GoVariableName> initVars = rangeBuilder.initVariables(Arrays.asList("k", "v"));
        GoVariableName k = initVars.get(0);
        GoVariableName v = initVars.get(1);

        try (GoBlockBuilder rangeBody = rangeBuilder.getBlockBuilder()) {
            GoExpression target = new GoIndexExpression(copy, k);

            rangeBody.assign(target, mapType.getValueType().accept(new CopyVisitor(rangeBody, v)));
        }

        return copy;
    }

    @Override
    public GoVariableName visit(GoInterfaceType interfaceType) throws RuntimeException {
        // best effort case: assign to copy.
        // Safe copy of interface{} type in Go requires use of the `reflect` package
        return createCopy(source);
    }

}