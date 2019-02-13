package pgo.trans.intermediate;

import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoAnonymousFunctionBuilder;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoForRangeBuilder;
import pgo.model.golang.builder.GoForStatementClauseBuilder;
import pgo.model.golang.type.GoSliceType;
import pgo.model.golang.type.GoType;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.passes.codegen.go.EqCodeGenVisitor;
import pgo.trans.passes.codegen.go.LessThanCodeGenVisitor;
import pgo.trans.passes.codegen.go.PGoTypeGoTypeConversionVisitor;
import pgo.trans.passes.codegen.go.TLAExpressionCodeGenVisitor;
import pgo.util.Origin;

import java.util.*;

public class TLABuiltins {
	private TLABuiltins() {}

	public static GoType getSetElementType(PGoType setType) {
		PGoType elementType = ((PGoTypeSet)setType).getElementType();
		return elementType.accept(new PGoTypeGoTypeConversionVisitor());
	}

	public static PGoTypeVariable getPolymorphicNumberType(Origin origin, PGoTypeSolver solver,
	                                                       PGoTypeGenerator generator) {
		PGoTypeVariable fresh = generator.get();
		solver.addConstraint(new PGoTypePolymorphicConstraint(origin, Arrays.asList(
				Collections.singletonList(
						new PGoTypeEqualityConstraint(fresh, new PGoTypeInt(Collections.singletonList(origin)))),
				Collections.singletonList(
						new PGoTypeEqualityConstraint(fresh, new PGoTypeDecimal(Collections.singletonList(origin)))))));
		return fresh;
	}

	private static PGoType constraintNumberOperation(Origin origin, List<PGoType> args, PGoTypeSolver solver,
	                                                 PGoTypeGenerator generator) {
		PGoTypeVariable fresh = getPolymorphicNumberType(origin, solver, generator);
		solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
		return fresh;
	}

	private static PGoType constraintBooleanNumberOperation(Origin origin, List<PGoType> args, PGoTypeSolver solver,
	                                                        PGoTypeGenerator generator) {
		constraintNumberOperation(origin, args, solver, generator);
		return new PGoTypeBool(Collections.singletonList(origin));
	}

	public static void ensureUniqueSorted(GoBlockBuilder builder, GoType elementType, GoVariableName set) {
		builder.addImport("sort");
		String sortFunction;
		if (elementType.equals(GoBuiltins.Int)) {
			sortFunction = "Ints";
		} else if (elementType.equals(GoBuiltins.Float64)) {
			sortFunction = "Float64s";
		} else if (elementType.equals(GoBuiltins.String)) {
			sortFunction = "Strings";
		} else {
			sortFunction = "Slice";
		}
		if (sortFunction.equals("Slice")) {
			GoAnonymousFunctionBuilder comparatorBuilder = builder.anonymousFunction();
			GoVariableName i = comparatorBuilder.addArgument("i", GoBuiltins.Int);
			GoVariableName j = comparatorBuilder.addArgument("j", GoBuiltins.Int);
			comparatorBuilder.addReturn(GoBuiltins.Bool);
			try (GoBlockBuilder comparatorBody = comparatorBuilder.getBlockBuilder()) {
				comparatorBody.addStatement(
						new GoReturn(
								Collections.singletonList(
										elementType.accept(
												new LessThanCodeGenVisitor(
														comparatorBody,
														new GoIndexExpression(set, i),
														new GoIndexExpression(set, j))))));
			}
			builder.addStatement(new GoExpressionStatement(new GoCall(
					new GoSelectorExpression(new GoVariableName("sort"), sortFunction),
					Arrays.asList(
							set,
							comparatorBuilder.getFunction()))));
		}else {
			builder.addStatement(new GoExpressionStatement(new GoCall(
					new GoSelectorExpression(new GoVariableName("sort"), sortFunction), Collections.singletonList(set))));
		}
		// make elements unique with the following GoRoutineStatement code
		//
		// if len(set) > 1 {
		// 	previousValue := set[0]
		// 	currentIndex := 1
		// 	for i, v := range set[1:] {
		// 		if v != previousValue {
		// 			set[currentIndex] = v
		// 			currentIndex++
		// 		}
		// 		previousValue = v
		// 	}
		// 	set = set[:currentIndex]
		// }
		try (GoIfBuilder ifBuilder = builder.ifStmt(new GoBinop(
				GoBinop.Operation.GT,
				new GoCall(new GoVariableName("len"), Collections.singletonList(set)),
				new GoIntLiteral(1)))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				GoVariableName previousValue = yes.varDecl(
						"previousValue", new GoIndexExpression(set, new GoIntLiteral(0)));
				GoVariableName currentIndex = yes.varDecl("currentIndex", new GoIntLiteral(1));
				GoForRangeBuilder forRangeBuilder = yes.forRange(new GoSliceOperator(set, new GoIntLiteral(1), null, null));
				GoVariableName v = forRangeBuilder.initVariables(Arrays.asList("_", "v")).get(1);
				try (GoBlockBuilder forBody = forRangeBuilder.getBlockBuilder()) {
					try (GoIfBuilder innerIf = forBody.ifStmt(elementType.accept(
							new EqCodeGenVisitor(forBody, previousValue, v, true)))) {
						try (GoBlockBuilder innerYes = innerIf.whenTrue()) {
							innerYes.assign(new GoIndexExpression(set, currentIndex), v);
							innerYes.addStatement(new GoIncDec(true, currentIndex));
						}
					}
					forBody.assign(previousValue, v);
				}
				yes.assign(set, new GoSliceOperator(set, null, currentIndex, null));
			}
		}
	}

	private static BuiltinModule universalBuiltIns = new BuiltinModule();
	static {
		universalBuiltIns.addOperator("=", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), args.get(1)));
					return new PGoTypeBool(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap, globalStrategy) -> {
					GoExpression lhs = arguments.get(0).accept(
							new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
					GoExpression rhs = arguments.get(1).accept(
							new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
					return typeMap.get(arguments.get(0).getUID())
							.accept(new PGoTypeGoTypeConversionVisitor())
							.accept(new EqCodeGenVisitor(builder, lhs, rhs, false));
				}));
		universalBuiltIns.addOperators(Arrays.asList("#", "/="), new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), args.get(1)));
					return new PGoTypeBool(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap, globalStrategy) -> {
					GoExpression lhs = arguments.get(0).accept(
							new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
					GoExpression rhs = arguments.get(1).accept(
							new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
					return typeMap.get(arguments.get(0).getUID())
							.accept(new PGoTypeGoTypeConversionVisitor())
							.accept(new EqCodeGenVisitor(builder, lhs, rhs, true));
				}));
		universalBuiltIns.addOperator("\\in", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoTypeVariable memberType = generator.get();
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), memberType));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(
							origin, args.get(1), new PGoTypeSet(memberType, Collections.singletonList(origin))));
					return new PGoTypeBool(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap, globalStrategy) -> {
					throw new TODO();
				}
				));
		universalBuiltIns.addOperator("\\", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeSet(generator.get(), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap, globalStrategy) -> {
					// lenLhs = len(lhs)
					// tmpSet := make([]type, 0, lenLhs)
					// for _, v := range lhs {
					// 	index := sort.SearchTypes(rhs, v)
					// 	if index < len(rhs) {
					//		if rhs[index] == v {
					//			continue
					//		}
					// 	}
					//  // keep the element
					//  tmpSet = append(tmpSet, v)
					// }
					builder.addImport("sort");
					GoType elementType = getSetElementType(typeMap.get(origin.getUID()));
					String searchFunction;
					if (elementType.equals(GoBuiltins.Int)) {
						searchFunction = "SearchInts";
					} else if (elementType.equals(GoBuiltins.Float64)) {
						searchFunction = "SearchFloat64s";
					} else if (elementType.equals(GoBuiltins.String)) {
						searchFunction = "SearchStrings";
					} else {
						searchFunction = "Search";
					}
					GoExpression lhs = arguments.get(0).accept(
							new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
					GoExpression rhs = arguments.get(1).accept(
							new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));

					// special case: rhs is an empty literal, compiles to noop
					if(rhs instanceof GoSliceLiteral && ((GoSliceLiteral)rhs).getInitializers().size() == 0){
						return lhs;
					}

					GoExpression lenLhs = new GoCall(new GoVariableName("len"), Collections.singletonList(lhs));
					GoExpression lenRhs = new GoCall(new GoVariableName("len"), Collections.singletonList(rhs));
					GoVariableName tmpSet = builder.varDecl(
							"tmpSet",
							new GoMakeExpression(
									new GoSliceType(elementType),
									new GoIntLiteral(0),
									lenLhs));
					GoForRangeBuilder forBuilder = builder.forRange(lhs);
					GoVariableName v = forBuilder.initVariables(Arrays.asList("_", "v")).get(1);
					try (GoBlockBuilder forBody = forBuilder.getBlockBuilder()) {
						// special case where rhs is a slice literal, we just unroll the entire literal instead
						// of searching through it
						if(rhs instanceof GoSliceLiteral){
							GoSliceLiteral rhsLiteral = (GoSliceLiteral)rhs;
							GoExpression condition = null;
							for(GoExpression option : rhsLiteral.getInitializers()){
								GoExpression part = elementType.accept(new EqCodeGenVisitor(
										forBody, v, option, true));
								if(condition == null){
									condition = part;
								}else{
									condition = new GoBinop(GoBinop.Operation.AND, condition, part);
								}
							}
							try(GoIfBuilder shouldIncludeBuilder = forBody.ifStmt(condition)){
								try(GoBlockBuilder shouldIncludeBody = shouldIncludeBuilder.whenTrue()){
									shouldIncludeBody.assign(
											tmpSet, new GoCall(new GoVariableName("append"), Arrays.asList(tmpSet, v)));
								}
							}
							return tmpSet;
						}

						// general case, requires search operation
						GoVariableName index;
						if (searchFunction.equals("Search")) {
							GoAnonymousFunctionBuilder checkBuilder = forBody.anonymousFunction();
							GoVariableName j = checkBuilder.addArgument("j", GoBuiltins.Int);
							checkBuilder.addReturn(GoBuiltins.Bool);
							try (GoBlockBuilder checkBody = checkBuilder.getBlockBuilder()) {
								checkBody.addStatement(
										new GoReturn(
												Collections.singletonList(
														new GoUnary(
																GoUnary.Operation.NOT,
																elementType.accept(new LessThanCodeGenVisitor(
																		checkBody,
																		new GoIndexExpression(rhs, j),
																		v))))));
							}
							index = forBody.varDecl(
									"index",
									new GoCall(
											new GoSelectorExpression(
													new GoVariableName("sort"), "Search"),
											Arrays.asList(
													new GoCall(new GoVariableName("len"), Collections.singletonList(rhs)),
													checkBuilder.getFunction())));
						}else {
							index = forBody.varDecl(
									"index",
									new GoCall(
											new GoSelectorExpression(new GoVariableName("sort"), searchFunction),
											Arrays.asList(rhs, v)));
						}
						try (GoIfBuilder ifBuilder = forBody.ifStmt(
								new GoBinop(GoBinop.Operation.LT, index, lenRhs))) {
							try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
								try (GoIfBuilder isEqBuilder = yes.ifStmt(elementType.accept(
												new EqCodeGenVisitor(
														yes,
														new GoIndexExpression(rhs, index),
														v,
														false)))) {
									try (GoBlockBuilder yes2 = isEqBuilder.whenTrue()) {
										yes2.addStatement(new GoContinue());
									}
								}
							}
						}
						forBody.assign(tmpSet, new GoCall(new GoVariableName("append"), Arrays.asList(tmpSet, v)));
					}
					return tmpSet;
				}));
		universalBuiltIns.addOperators(Arrays.asList("~", "\\lnot", "\\neg"), new TypelessBuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeBool(Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new GoUnary(
						GoUnary.Operation.NOT, arguments.get(0))
				));
		universalBuiltIns.addOperators(Arrays.asList("\\/", "\\lor"), new TypelessBuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeBool(Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new GoBinop(
						GoBinop.Operation.OR, arguments.get(0), arguments.get(1))
				));
		universalBuiltIns.addOperators(Arrays.asList("/\\", "\\land"), new TypelessBuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeBool(Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new GoBinop(
						GoBinop.Operation.AND, arguments.get(0), arguments.get(1))
				));
		universalBuiltIns.addOperators(Arrays.asList("\\union", "\\cup"), new TypelessBuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeSet(generator.get(), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> {
					GoType elementType = getSetElementType(typeMap.get(origin.getUID()));
					GoExpression lhs = arguments.get(0);
					GoExpression rhs = arguments.get(1);
					GoExpression lhsLen = new GoCall(new GoVariableName("len"), Collections.singletonList(lhs));
					GoExpression combinedLen = new GoBinop(
							GoBinop.Operation.PLUS,
							lhsLen,
							new GoCall(new GoVariableName("len"), Collections.singletonList(rhs)));
					GoVariableName tmpSet = builder.varDecl(
							"tmpSet",
							new GoMakeExpression(new GoSliceType(elementType), lhsLen, combinedLen));
					// since append may re-use the same memory, we have to copy lhs in order to be sure
					// that we are not going to overwrite the original slice when we sort
					builder.addStatement(new GoCall(new GoVariableName("copy"), Arrays.asList(tmpSet, lhs)));
					builder.assign(tmpSet, new GoCall(new GoVariableName("append"), Arrays.asList(tmpSet, rhs), true));
					ensureUniqueSorted(builder, elementType, tmpSet);
					return tmpSet;
				}));
	}

	private static Map<String, BuiltinModule> builtinModules = new HashMap<>();
	static {
		BuiltinModule TLC = new BuiltinModule();
		builtinModules.put("TLC", TLC);


		BuiltinModule Sequences = new BuiltinModule();
		builtinModules.put("Sequences", Sequences);
		Sequences.addOperator("Len", new TypelessBuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					solver.addConstraint(new PGoTypePolymorphicConstraint(origin, Arrays.asList(
							Collections.singletonList(new PGoTypeEqualityConstraint(
									args.get(0), new PGoTypeString(Collections.singletonList(origin)))),
							Collections.singletonList(new PGoTypeEqualityConstraint(
									args.get(0), new PGoTypeSlice(generator.get(), Collections.singletonList(origin))))
					)));
					return new PGoTypeInt(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap) -> new GoCall(
						new GoVariableName("len"), Collections.singletonList(arguments.get(0)))
				));
		Sequences.addOperator("Append", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoTypeVariable elementType = generator.get();
					PGoType fresh = new PGoTypeSlice(elementType, Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), elementType));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap, globalStrategy) -> {
					GoType baseType = typeMap.get(arguments.get(0).getUID()).accept(new PGoTypeGoTypeConversionVisitor());
					GoExpression base = arguments.get(0).accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
					GoExpression extra = arguments.get(1).accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));

					GoExpression baseLen = new GoCall(new GoVariableName("len"), Collections.singletonList(base));
					// since append may reuse the underlying slice, it is possible that appending two different
					// things to the same original slice will causes unintended mutations in the results of previous
					// appends. copy the original slice to be sure.
					GoVariableName tmpSlice = builder.varDecl(
							"tmpSlice",
							new GoMakeExpression(
									baseType,
									baseLen,
									new GoBinop(GoBinop.Operation.PLUS, baseLen, new GoIntLiteral(1))));
					builder.addStatement(new GoCall(new GoVariableName("copy"), Arrays.asList(tmpSlice, base)));
					builder.assign(tmpSlice, new GoCall(new GoVariableName("append"), Arrays.asList(tmpSlice, extra)));
					return tmpSlice;
				}));
		Sequences.addOperator("Head", new TypelessBuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					PGoTypeVariable elementType = generator.get();
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), new PGoTypeSlice(elementType, Collections.singletonList(origin))));
					return elementType;
				},
				(builder, origin, registry, arguments, typeMap) -> new GoIndexExpression(arguments.get(0), new GoIntLiteral(0))
				));
		Sequences.addOperator("Tail", new TypelessBuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					PGoTypeVariable elementType = generator.get();
					PGoType fresh = new PGoTypeSlice(elementType, Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new GoSliceOperator(
						arguments.get(0), new GoIntLiteral(1), null, null)
				));

		BuiltinModule Naturals = new BuiltinModule();
		builtinModules.put("Naturals", Naturals);
		Naturals.addOperator("-", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new GoBinop(
						GoBinop.Operation.MINUS, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("+", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new GoBinop(
						GoBinop.Operation.PLUS, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("%", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new GoBinop(
						GoBinop.Operation.MOD, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("*", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new GoBinop(
						GoBinop.Operation.TIMES, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("<", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintBooleanNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new GoBinop(
						GoBinop.Operation.LT, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator(">", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintBooleanNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new GoBinop(
						GoBinop.Operation.GT, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperators(Arrays.asList("<=", "\\leq"), new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintBooleanNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new GoBinop(
						GoBinop.Operation.LEQ, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperators(Arrays.asList(">=", "\\geq"), new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintBooleanNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new GoBinop(
						GoBinop.Operation.GEQ, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("Nat", new TypelessBuiltinOperator(
				0,
				(origin, args, solver, generator) -> new PGoTypeNonEnumerableSet(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin)),
				(builder, origin, registry, arguments, typeMap) -> {
					throw new TODO();
				}
				));
		Naturals.addOperator("..", new TypelessBuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType intType = new PGoTypeInt(Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), intType));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), intType));
					return new PGoTypeSet(intType, Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap) -> {
					GoExpression from = arguments.get(0);
					GoExpression to = arguments.get(1);
					GoExpression tmpRange = builder.varDecl("tmpRange", new GoMakeExpression(
							new GoSliceType(GoBuiltins.Int),
							new GoBinop(
									GoBinop.Operation.PLUS,
									new GoBinop(GoBinop.Operation.MINUS, to, from),
									new GoIntLiteral(1)),
							null));

					GoForStatementClauseBuilder clauseBuilder = builder.forLoopWithClauses();
					GoVariableName acc = clauseBuilder.initVariable("i", from);
					clauseBuilder.setCondition(new GoBinop(GoBinop.Operation.LEQ, acc, to));
					clauseBuilder.setInc(new GoIncDec(true, acc));

					try (GoBlockBuilder body = clauseBuilder.getBlockBuilder()) {
						body.assign(
								new GoIndexExpression(tmpRange, new GoBinop(GoBinop.Operation.MINUS, acc, from)),
								acc);
					}
					return tmpRange;
				}));

		BuiltinModule Integers = new BuiltinModule(Naturals);
		builtinModules.put("Integers", Integers);
		Integers.addOperator("-_", new TypelessBuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					PGoTypeVariable fresh = getPolymorphicNumberType(origin, solver, generator);
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) ->
						new GoUnary(GoUnary.Operation.NEG, arguments.get(0))));
		Integers.addOperator("Int", new TypelessBuiltinOperator(
				0,
				(origin, args, solver, generator) -> new PGoTypeNonEnumerableSet(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin)),
				(builder, origin, registry, arguments, typeMap) -> {
					throw new TODO();
				}));

		BuiltinModule FiniteSets = new BuiltinModule();
		builtinModules.put("FiniteSets", FiniteSets);
		FiniteSets.addOperator("Cardinality", new TypelessBuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					throw new TODO();
				},
				(builder, origin, registry, arguments, typeMap) -> {
					throw new TODO();
				}
		));

	}

	public static BuiltinModule getUniversalBuiltIns() {
		return universalBuiltIns;
	}

	public static BuiltinModule findBuiltinModule(String name) {
		return builtinModules.get(name);
	}

	public static boolean isBuiltinModule(String name) {
		return builtinModules.containsKey(name);
	}

	public static Map<QualifiedName, UID> getInitialDefinitions() {
		Map<QualifiedName, UID> defs = new HashMap<>();
		for(Map.Entry<String, OperatorAccessor> op : universalBuiltIns.getOperators().entrySet()) {
			defs.put(new QualifiedName(op.getKey()), op.getValue().getUID());
		}
		return defs;
	}
}
