package pgo.trans.intermediate;

import java.util.*;

import pgo.model.golang.*;
import pgo.model.type.*;
import pgo.scope.UID;

public class TLABuiltins {

	private TLABuiltins() {}

	public static Type ensureSetType(Map<UID, PGoType> typeMap, UID uid) {
		Type elementType = ((PGoTypeSet) typeMap.get(uid)).getElementType().accept(new PGoTypeGoTypeConversionVisitor());
		if (!elementType.equals(Builtins.Int) && !elementType.equals(Builtins.Float64) && !elementType.equals(Builtins.String)) {
			throw new RuntimeException("TODO");
		}
		return elementType;
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
			throw new RuntimeException("unreachable");
		}
		builder.addStatement(new ExpressionStatement(new Call(
				new Selector(new VariableName("sort"), sortFunction), Collections.singletonList(set))));
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
				List<VariableName> names = forRangeBuilder.initVariables(Arrays.asList("i", "v"));
				VariableName i = names.get(0);
				VariableName v = names.get(1);
				try (BlockBuilder forBody = forRangeBuilder.getBlockBuilder()) {
					try (IfBuilder innerIf = forBody.ifStmt(new Binop(Binop.Operation.NEQ, v, previousValue))) {
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

	private static BuiltinModule universalBuiltins = new BuiltinModule();
	static {
		universalBuiltins.addOperator("=", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), args.get(1)));
					return new PGoTypeBool(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap) -> typeMap.get(origin.getUID()).accept(
						new PGoTypeEqualityCodeGenVisitor(
								builder, false, registry, arguments.get(0), arguments.get(1)))
				));
		universalBuiltins.addOperator("#", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), args.get(1)));
					return new PGoTypeBool(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap) -> typeMap.get(origin.getUID()).accept(
						new PGoTypeEqualityCodeGenVisitor(
								builder, true, registry, arguments.get(0), arguments.get(1)))
				));
		universalBuiltins.addOperator("\\in", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoTypeVariable memberType = generator.get();
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), memberType));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(
							origin, args.get(1), new PGoTypeSet(memberType, Collections.singletonList(origin))));
					return new PGoTypeBool(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap) -> {
					throw new RuntimeException("TODO");
				}
				));
		universalBuiltins.addOperator("\\", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeSet(generator.get(), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> {
					// lenLhs = len(lhs)
					// tmpSet := make([]type, lenLhs)
					// currentIndex := 0
					// for i := 0; i < lenLhs; i++ {
					// 	index := sort.SearchTypes(rhs, lhs[i])
					// 	if index >= lenLhs || rhs[index] != lhs[i] {
					// 		// keep lhs[i]
					// 		lhs[currentIndex] = lhs[i]
					// 		currentIndex += 1
					// 	}
					// }
					// tmpSet = tmpSet[:currentIndex]
					builder.addImport("sort");
					Type elementType = ensureSetType(typeMap, origin.getUID());
					String searchFunction;
					if (elementType.equals(Builtins.Int)) {
						searchFunction = "SearchInts";
					} else if (elementType.equals(Builtins.Float64)) {
						searchFunction = "SearchFloat64s";
					} else if (elementType.equals(Builtins.String)) {
						searchFunction = "SearchStrings";
					} else {
						throw new RuntimeException("unreachable");
					}
					Expression lhs = arguments.get(0);
					Expression rhs = arguments.get(1);
					VariableName lenLhs = builder.varDecl(
							"lenLhs",
							new Call(new VariableName("len"), Collections.singletonList(lhs)));
					VariableName tmpSet = builder.varDecl(
							"tmpSet",
							new Make(
									new SliceType(elementType),
									lenLhs,
									null));
					VariableName currentIndex = builder.varDecl("currentIndex", new IntLiteral(0));
					ForStatementClauseBuilder forBuilder = builder.forLoopWithClauses();
					VariableName i = forBuilder.initVariable("i", new IntLiteral(0));
					forBuilder.setCondition(new Binop(Binop.Operation.LT, i, lenLhs));
					forBuilder.setInc(new IncDec(true, i));
					try (BlockBuilder forBody = forBuilder.getBlockBuilder()) {
						VariableName index = forBody.varDecl(
								"index",
								new Call(
										new Selector(new VariableName("sort"), searchFunction),
										Arrays.asList(rhs, new Index(lhs, i))));
						try (IfBuilder ifBuilder = forBody.ifStmt(
								new Binop(Binop.Operation.OR,
										new Binop(Binop.Operation.GEQ, index, lenLhs),
										new Binop(Binop.Operation.NEQ, new Index(rhs, index), new Index(lhs, i))))) {
							try (BlockBuilder yes = ifBuilder.whenTrue()) {
								yes.assign(new Index(tmpSet, currentIndex), new Index(lhs, i));
								yes.addStatement(new IncDec(true, currentIndex));
							}
						}
					}
					builder.assign(tmpSet, new SliceOperator(tmpSet, null, currentIndex, null));
					return tmpSet;
				}));
		universalBuiltins.addOperator("~", new BuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeBool(Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Unary(Unary.Operation.NOT, arguments.get(0))
				));
		universalBuiltins.addOperator("\\/", new BuiltinOperator(
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
		universalBuiltins.addOperator("/\\", new BuiltinOperator(
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
		universalBuiltins.addOperator("\\union", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeSet(generator.get(), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> {
					Type elementType = ensureSetType(typeMap, origin.getUID());
					Expression lhs = arguments.get(0);
					Expression rhs = arguments.get(1);
					VariableName tmpSet = builder.varDecl(
							"tmpSet",
							new Call(new VariableName("append"), Arrays.asList(lhs, rhs), true));
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
		Sequences.addOperator("Len", new BuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					solver.addConstraint(new PGoTypePolymorphicConstraint(origin, Arrays.asList(
							new PGoTypeEqualityConstraint(args.get(0), new PGoTypeString(Collections.singletonList(origin))),
							new PGoTypeEqualityConstraint(args.get(0), new PGoTypeSlice(generator.get(), Collections.singletonList(origin))),
							new PGoTypeEqualityConstraint(args.get(0), new PGoTypeUnrealizedTuple(Collections.singletonList(origin)))
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
				(builder, origin, registry, arguments, typeMap) -> new Call(
						new VariableName("append"), Arrays.asList(arguments.get(0), arguments.get(1)))
				));
		Sequences.addOperator("Head", new BuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					PGoTypeVariable elementType = generator.get();
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), new PGoTypeSlice(elementType, Collections.singletonList(origin))));
					return elementType;
				},
				(builder, origin, registry, arguments, typeMap) -> new Index(arguments.get(0), new IntLiteral(0))
				));
		Sequences.addOperator("Tail", new BuiltinOperator(
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
		Naturals.addOperator("-", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.MINUS, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("+", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.PLUS, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("%", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.MOD, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("*", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.TIMES, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("<", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return new PGoTypeBool(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.LT, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator(">", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return new PGoTypeBool(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.GT, arguments.get(0), arguments.get(1))
				));
		// TODO: \leq =<
		Naturals.addOperator("<=", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return new PGoTypeBool(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.LEQ, arguments.get(0), arguments.get(1))
				));
		// TODO: \geq
		Naturals.addOperator(">=", new BuiltinOperator(
				2,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(1), fresh));
					return new PGoTypeBool(Collections.singletonList(origin));
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.GEQ, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("Nat", new BuiltinOperator(
				0,
				(origin, args, solver, generator) -> new PGoTypeNonEnumerableSet(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin)),
				(builder, origin, registry, arguments, typeMap) -> {
					throw new RuntimeException("TODO");
				}
				));
		Naturals.addOperator("..", new BuiltinOperator(
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

					try(BlockBuilder body = clauseBuilder.getBlockBuilder()){
						body.assign(
								new Index(tmpRange, new Binop(Binop.Operation.MINUS, acc, from)),
								acc);
					}
					return tmpRange;
				}));

		BuiltinModule Integers = new BuiltinModule(Naturals);
		builtinModules.put("Integers", Integers);
		Integers.addOperator("-", new BuiltinOperator(
				1,
				(origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin));
					solver.addConstraint(new PGoTypeMonomorphicConstraint(origin, args.get(0), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Unary(Unary.Operation.NEG, arguments.get(0))
				));
		Integers.addOperator("Int", new BuiltinOperator(
				0,
				(origin, args, solver, generator) -> new PGoTypeNonEnumerableSet(new PGoTypeInt(Collections.singletonList(origin)), Collections.singletonList(origin)),
				(builder, origin, registry, arguments, typeMap) -> {
					throw new RuntimeException("TODO");
				}
				));

	}

	public static BuiltinModule getUniversalBuiltins() {
		return universalBuiltins;
	}

	public static BuiltinModule findBuiltinModule(String name) {
		return builtinModules.get(name);
	}

	public static boolean isBuiltinModule(String name) {
		return builtinModules.containsKey(name);
	}

	public static Map<QualifiedName, UID> getInitialDefinitions() {
		Map<QualifiedName, UID> defs = new HashMap<>();
		for(Map.Entry<String, OperatorAccessor> op : universalBuiltins.getOperators().entrySet()) {
			defs.put(new QualifiedName(op.getKey()), op.getValue().getUID());
		}
		return defs;
	}

}
