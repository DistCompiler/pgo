package pgo.trans.intermediate;

import java.util.*;

import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.util.Origin;

public class TLABuiltins {
	private TLABuiltins() {}

	public static Type getSetElementType(PGoType setType) {
		PGoType elementType = ((PGoTypeSet)setType).getElementType();
		return elementType.accept(new PGoTypeGoTypeConversionVisitor());
	}

	private static PGoType constraintNumberOperation(Origin origin, List<PGoType> args, PGoTypeSolver solver, PGoTypeGenerator generator) {
		PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
		return fresh;
	}

	private static PGoType constraintBooleanNumberOperation(Origin origin, List<PGoType> args, PGoTypeSolver solver, PGoTypeGenerator generator) {
		constraintNumberOperation(origin, args, solver, generator);
		return new PGoTypeBool(Collections.singletonList(origin));
	}

	public static void ensureUniqueSorted(BlockBuilder builder, Type elementType, VariableName set) {
		builder.addImport("sort");
		String sortFunction;
		if (elementType.equals(Builtins.Int)) {
			sortFunction = "Ints";
		} else if (elementType.equals(Builtins.Float64)) {
			sortFunction = "Float64s";
		} else if (elementType.equals(Builtins.String)) {
			sortFunction = "Strings";
		} else {
			sortFunction = "Slice";
		}
		if (sortFunction.equals("Slice")) {
			AnonymousFunctionBuilder comparatorBuilder = builder.anonymousFunction();
			VariableName i = comparatorBuilder.addArgument("i", Builtins.Int);
			VariableName j = comparatorBuilder.addArgument("j", Builtins.Int);
			comparatorBuilder.addReturn(Builtins.Bool);
			try (BlockBuilder comparatorBody = comparatorBuilder.getBlockBuilder()) {
				comparatorBody.addStatement(
						new Return(
								Collections.singletonList(
										elementType.accept(
												new LessThanCodeGenVisitor(
														comparatorBody,
														new Index(set, i),
														new Index(set, j))))));
			}
			builder.addStatement(new ExpressionStatement(new Call(
					new Selector(new VariableName("sort"), sortFunction),
					Arrays.asList(
							set,
							comparatorBuilder.getFunction()))));
		}else {
			builder.addStatement(new ExpressionStatement(new Call(
					new Selector(new VariableName("sort"), sortFunction), Collections.singletonList(set))));
		}
		// make elements unique with the following Go code
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
		try (IfBuilder ifBuilder = builder.ifStmt(new Binop(
				Binop.Operation.GT,
				new Call(new VariableName("len"), Collections.singletonList(set)),
				new IntLiteral(1)))) {
			try (BlockBuilder yes = ifBuilder.whenTrue()) {
				VariableName previousValue = yes.varDecl(
						"previousValue", new Index(set, new IntLiteral(0)));
				VariableName currentIndex = yes.varDecl("currentIndex", new IntLiteral(1));
				ForRangeBuilder forRangeBuilder = yes.forRange(new SliceOperator(set, new IntLiteral(1), null, null));
				VariableName v = forRangeBuilder.initVariables(Arrays.asList("_", "v")).get(1);
				try (BlockBuilder forBody = forRangeBuilder.getBlockBuilder()) {
					try (IfBuilder innerIf = forBody.ifStmt(elementType.accept(
							new EqCodeGenVisitor(forBody, previousValue, v, true)))) {
						try (BlockBuilder innerYes = innerIf.whenTrue()) {
							innerYes.assign(new Index(set, currentIndex), v);
							innerYes.addStatement(new IncDec(true, currentIndex));
						}
					}
					forBody.assign(previousValue, v);
				}
				yes.assign(set, new SliceOperator(set, null, currentIndex, null));
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
					Expression lhs = arguments.get(0).accept(
							new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
					Expression rhs = arguments.get(1).accept(
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
					Expression lhs = arguments.get(0).accept(
							new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
					Expression rhs = arguments.get(1).accept(
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
					Type elementType = getSetElementType(typeMap.get(origin.getUID()));
					String searchFunction;
					if (elementType.equals(Builtins.Int)) {
						searchFunction = "SearchInts";
					} else if (elementType.equals(Builtins.Float64)) {
						searchFunction = "SearchFloat64s";
					} else if (elementType.equals(Builtins.String)) {
						searchFunction = "SearchStrings";
					} else {
						searchFunction = "Search";
					}
					Expression lhs = arguments.get(0).accept(
							new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
					Expression rhs = arguments.get(1).accept(
							new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));

					// special case: rhs is an empty literal, compiles to noop
					if(rhs instanceof SliceLiteral && ((SliceLiteral)rhs).getInitializers().size() == 0){
						return lhs;
					}

					Expression lenLhs = new Call(new VariableName("len"), Collections.singletonList(lhs));
					Expression lenRhs = new Call(new VariableName("len"), Collections.singletonList(rhs));
					VariableName tmpSet = builder.varDecl(
							"tmpSet",
							new Make(
									new SliceType(elementType),
									new IntLiteral(0),
									lenLhs));
					ForRangeBuilder forBuilder = builder.forRange(lhs);
					VariableName v = forBuilder.initVariables(Arrays.asList("_", "v")).get(1);
					try (BlockBuilder forBody = forBuilder.getBlockBuilder()) {
						// special case where rhs is a slice literal, we just unroll the entire literal instead
						// of searching through it
						if(rhs instanceof SliceLiteral){
							SliceLiteral rhsLiteral = (SliceLiteral)rhs;
							Expression condition = null;
							for(Expression option : rhsLiteral.getInitializers()){
								Expression part = elementType.accept(new EqCodeGenVisitor(
										forBody, v, option, true));
								if(condition == null){
									condition = part;
								}else{
									condition = new Binop(Binop.Operation.AND, condition, part);
								}
							}
							try(IfBuilder shouldIncludeBuilder = forBody.ifStmt(condition)){
								try(BlockBuilder shouldIncludeBody = shouldIncludeBuilder.whenTrue()){
									shouldIncludeBody.assign(
											tmpSet, new Call(new VariableName("append"), Arrays.asList(tmpSet, v)));
								}
							}
							return tmpSet;
						}

						// general case, requires search operation
						VariableName index;
						if (searchFunction.equals("Search")) {
							AnonymousFunctionBuilder checkBuilder = forBody.anonymousFunction();
							VariableName j = checkBuilder.addArgument("j", Builtins.Int);
							checkBuilder.addReturn(Builtins.Bool);
							try (BlockBuilder checkBody = checkBuilder.getBlockBuilder()) {
								checkBody.addStatement(
										new Return(
												Collections.singletonList(
														new Unary(
																Unary.Operation.NOT,
																elementType.accept(new LessThanCodeGenVisitor(
																		checkBody,
																		new Index(rhs, j),
																		v))))));
							}
							index = forBody.varDecl(
									"index",
									new Call(
											new Selector(
													new VariableName("sort"), "Search"),
											Arrays.asList(
													new Call(new VariableName("len"), Collections.singletonList(rhs)),
													checkBuilder.getFunction())));
						}else {
							index = forBody.varDecl(
									"index",
									new Call(
											new Selector(new VariableName("sort"), searchFunction),
											Arrays.asList(rhs, v)));
						}
						try (IfBuilder ifBuilder = forBody.ifStmt(
								new Binop(Binop.Operation.LT, index, lenRhs))) {
							try (BlockBuilder yes = ifBuilder.whenTrue()) {
								try (IfBuilder isEqBuilder = yes.ifStmt(elementType.accept(
												new EqCodeGenVisitor(
														yes,
														new Index(rhs, index),
														v,
														false)))) {
									try (BlockBuilder yes2 = isEqBuilder.whenTrue()) {
										yes2.addStatement(new Continue());
									}
								}
							}
						}
						forBody.assign(tmpSet, new Call(new VariableName("append"), Arrays.asList(tmpSet, v)));
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
				(builder, origin, registry, arguments, typeMap) -> new Unary(
						Unary.Operation.NOT, arguments.get(0))
				));
		universalBuiltIns.addOperators(Arrays.asList("\\/", "\\lor"), new TypelessBuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeBool(Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.OR, arguments.get(0), arguments.get(1))
				));
		universalBuiltIns.addOperators(Arrays.asList("/\\", "\\land"), new TypelessBuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeBool(Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.AND, arguments.get(0), arguments.get(1))
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
					Type elementType = getSetElementType(typeMap.get(origin.getUID()));
					Expression lhs = arguments.get(0);
					Expression rhs = arguments.get(1);
					Expression lhsLen = new Call(new VariableName("len"), Collections.singletonList(lhs));
					Expression combinedLen = new Binop(
							Binop.Operation.PLUS,
							lhsLen,
							new Call(new VariableName("len"), Collections.singletonList(rhs)));
					VariableName tmpSet = builder.varDecl(
							"tmpSet",
							new Make(new SliceType(elementType), lhsLen, combinedLen));
					// since append may re-use the same memory, we have to copy lhs in order to be sure
					// that we are not going to overwrite the original slice when we sort
					builder.addStatement(new Call(new VariableName("copy"), Arrays.asList(tmpSet, lhs)));
					builder.assign(tmpSet, new Call(new VariableName("append"), Arrays.asList(tmpSet, rhs), true));
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
				(builder, origin, registry, arguments, typeMap) -> new Call(
						new VariableName("len"), Collections.singletonList(arguments.get(0)))
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
					Type baseType = typeMap.get(arguments.get(0).getUID()).accept(new PGoTypeGoTypeConversionVisitor());
					Expression base = arguments.get(0).accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));
					Expression extra = arguments.get(1).accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, globalStrategy));

					Expression baseLen = new Call(new VariableName("len"), Collections.singletonList(base));
					// since append may reuse the underlying slice, it is possible that appending two different
					// things to the same original slice will causes unintended mutations in the results of previous
					// appends. copy the original slice to be sure.
					VariableName tmpSlice = builder.varDecl(
							"tmpSlice",
							new Make(
									baseType,
									baseLen,
									new Binop(Binop.Operation.PLUS, baseLen, new IntLiteral(1))));
					builder.addStatement(new Call(new VariableName("copy"), Arrays.asList(tmpSlice, base)));
					builder.assign(tmpSlice, new Call(new VariableName("append"), Arrays.asList(tmpSlice, extra)));
					return tmpSlice;
				}));
		Sequences.addOperator("Head", new TypelessBuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					PGoTypeVariable elementType = generator.get();
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), new PGoTypeSlice(elementType, Collections.singletonList(origin))));
					return elementType;
				},
				(builder, origin, registry, arguments, typeMap) -> new Index(arguments.get(0), new IntLiteral(0))
				));
		Sequences.addOperator("Tail", new TypelessBuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					PGoTypeVariable elementType = generator.get();
					PGoType fresh = new PGoTypeSlice(elementType, Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new SliceOperator(
						arguments.get(0), new IntLiteral(1), null, null)
				));

		BuiltinModule Naturals = new BuiltinModule();
		builtinModules.put("Naturals", Naturals);
		Naturals.addOperator("-", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.MINUS, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("+", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.PLUS, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("%", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.MOD, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("*", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.TIMES, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("<", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintBooleanNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.LT, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator(">", new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintBooleanNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.GT, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperators(Arrays.asList("<=", "\\leq"), new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintBooleanNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.LEQ, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperators(Arrays.asList(">=", "\\geq"), new TypelessBuiltinOperator(
				2,
				TLABuiltins::constraintBooleanNumberOperation,
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.GEQ, arguments.get(0), arguments.get(1))
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
					Expression from = arguments.get(0);
					Expression to = arguments.get(1);
					Expression tmpRange = builder.varDecl("tmpRange", new Make(
							new SliceType(Builtins.Int),
							new Binop(
									Binop.Operation.PLUS,
									new Binop(Binop.Operation.MINUS, to, from),
									new IntLiteral(1)),
							null));

					ForStatementClauseBuilder clauseBuilder = builder.forLoopWithClauses();
					VariableName acc = clauseBuilder.initVariable("i", from);
					clauseBuilder.setCondition(new Binop(Binop.Operation.LEQ, acc, to));
					clauseBuilder.setInc(new IncDec(true, acc));

					try (BlockBuilder body = clauseBuilder.getBlockBuilder()) {
						body.assign(
								new Index(tmpRange, new Binop(Binop.Operation.MINUS, acc, from)),
								acc);
					}
					return tmpRange;
				}));

		BuiltinModule Integers = new BuiltinModule(Naturals);
		builtinModules.put("Integers", Integers);
		Integers.addOperator("-_", new TypelessBuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) ->
						new Unary(Unary.Operation.NEG, arguments.get(0))));
		Integers.addOperator("Int", new TypelessBuiltinOperator(
				0,
				(origin, args, solver, generator) -> new PGoTypeNonEnumerableSet(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin)),
				(builder, origin, registry, arguments, typeMap) -> {
					throw new TODO();
				}));

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
