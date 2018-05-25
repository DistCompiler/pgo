package pgo.trans.intermediate;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import pgo.model.golang.Assignment;
import pgo.model.golang.Binop;
import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Builtins;
import pgo.model.golang.Call;
import pgo.model.golang.Expression;
import pgo.model.golang.IncDec;
import pgo.model.golang.Index;
import pgo.model.golang.IntLiteral;
import pgo.model.golang.Make;
import pgo.model.golang.SliceOperator;
import pgo.model.golang.SliceType;
import pgo.model.golang.Unary;
import pgo.model.golang.VariableName;
import pgo.model.type.*;
import pgo.scope.UID;

public class TLABuiltins {

	private TLABuiltins() {}

	private static BuiltinModule universalBuiltins = new BuiltinModule();
	static {
		universalBuiltins.addOperator("=", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), args.get(1)));
					return new PGoTypeBool(origin);
				},
				(builder, origin, registry, arguments, typeMap) -> {
					return typeMap.get(origin.getUID()).accept(
							new PGoTypeEqualityCodeGenVisitor(
									builder, false, registry, arguments.get(0), arguments.get(1)));
				}
				));
		universalBuiltins.addOperator("#", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), args.get(1)));
					return new PGoTypeBool(origin);
				},
				(builder, origin, registry, arguments, typeMap) -> {
					return typeMap.get(origin.getUID()).accept(
							new PGoTypeEqualityCodeGenVisitor(
									builder, true, registry, arguments.get(0), arguments.get(1)));
				}
				));
		universalBuiltins.addOperator("\\in", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoTypeVariable memberType = generator.get();
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), memberType));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), new PGoTypeSet(memberType)));
					return new PGoTypeBool(origin);
				},
				(builder, origin, registry, arguments, typeMap) -> {
					throw new RuntimeException("TODO");
				}
				));
		universalBuiltins.addOperator("\\", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoTypeVariable memberType = generator.get();
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), new PGoTypeSet(memberType)));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), new PGoTypeSet(memberType)));
					return new PGoTypeSet(memberType, origin);
				},
				(builder, origin, registry, arguments, typeMap) -> {
					throw new RuntimeException("TODO");
				}
				));
		universalBuiltins.addOperator("~", new BuiltinOperator(
				1,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeBool(origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					return new PGoTypeBool(origin);
				},
				(builder, origin, registry, arguments, typeMap) -> new Unary(Unary.Operation.NOT, arguments.get(0))
				));
		universalBuiltins.addOperator("\\/", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeBool(origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return new PGoTypeBool(origin);
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.OR, arguments.get(0), arguments.get(1))
				));
		universalBuiltins.addOperator("/\\", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeBool(origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return new PGoTypeBool(origin);
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.AND, arguments.get(0), arguments.get(1))
				));
		universalBuiltins.addOperator("\\union", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoTypeVariable memberType = generator.get();
					PGoType fresh = new PGoTypeSet(memberType, origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return new PGoTypeSet(memberType, origin);
				},
				(builder, origin, registry, arguments, typeMap) -> {
					throw new RuntimeException("TODO");
				}
				));
	}

	private static Map<String, BuiltinModule> builtinModules = new HashMap<>();
	static {
		BuiltinModule TLC = new BuiltinModule();
		builtinModules.put("TLC", TLC);


		BuiltinModule Sequences = new BuiltinModule();
		builtinModules.put("Sequences", Sequences);
		Sequences.addOperator("Len", new PolymorphicBuiltinOperator(
				1,
				Arrays.asList(
					(ctx, origin, args, solver, generator) -> {
						solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), new PGoTypeString(origin)));
						return new PGoTypeInt(origin);
					},
					(ctx, origin, args, solver, generator) -> {
						solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), new PGoTypeSlice(generator.get(), origin)));
						return new PGoTypeInt(origin);
					},
					(ctx, origin, args, solver, generator) -> {
						solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), new PGoTypeUnrealizedTuple(new PGoTypeNatural(origin), origin)));
						return new PGoTypeInt(origin);
					}),
				(builder, origin, registry, arguments, typeMap) -> new Call(
						new VariableName("len"), Collections.singletonList(arguments.get(0)))
				));
		Sequences.addOperator("Append", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoTypeVariable elementType = generator.get();
					PGoType fresh = new PGoTypeSlice(elementType, origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), elementType));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Call(
						new VariableName("append"), Arrays.asList(arguments.get(0), arguments.get(1)))
				));
		Sequences.addOperator("Head", new BuiltinOperator(
				1,
				(ctx, origin, args, solver, generator) -> {
					PGoTypeVariable elementType = generator.get();
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), new PGoTypeSlice(elementType, origin)));
					return elementType;
				},
				(builder, origin, registry, arguments, typeMap) -> new Index(arguments.get(0), new IntLiteral(0))
				));
		Sequences.addOperator("Tail", new BuiltinOperator(
				1,
				(ctx, origin, args, solver, generator) -> {
					PGoTypeVariable elementType = generator.get();
					PGoType fresh = new PGoTypeSlice(elementType, origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new SliceOperator(
						arguments.get(0), new IntLiteral(1), null, null)
				));

		BuiltinModule Naturals = new BuiltinModule();
		builtinModules.put("Naturals", Naturals);
		Naturals.addOperator("-", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.MINUS, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("+", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.PLUS, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("%", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.MOD, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("*", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.TIMES, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("<", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return new PGoTypeBool(origin);
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.LT, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator(">", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return new PGoTypeBool(origin);
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.GT, arguments.get(0), arguments.get(1))
				));
		// TODO: \leq =<
		Naturals.addOperator("<=", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return new PGoTypeBool(origin);
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.LEQ, arguments.get(0), arguments.get(1))
				));
		// TODO: \geq
		Naturals.addOperator(">=", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return new PGoTypeBool(origin);
				},
				(builder, origin, registry, arguments, typeMap) -> new Binop(
						Binop.Operation.GEQ, arguments.get(0), arguments.get(1))
				));
		Naturals.addOperator("Nat", new BuiltinOperator(
				0,
				(ctx, origin, args, solver, generator) -> new PGoTypeNonEnumerableSet(new PGoTypeNatural(origin), origin),
				(builder, origin, registry, arguments, typeMap) -> {
					throw new RuntimeException("TODO");
				}
				));
		Naturals.addOperator("..", new BuiltinOperator(
				2,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = PGoTypeUnrealizedNumber.integralType(origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
					return new PGoTypeSet(fresh);
				},
				(builder, origin, registry, arguments, typeMap) -> {
					Expression from = arguments.get(0);
					Expression to = arguments.get(1);
					Expression tmpRange = builder.varDecl("tmpRange", new Make(
							new SliceType(Builtins.Int), new Binop(Binop.Operation.MINUS, to, from), null));
					// TODO scope i correctly
					Expression acc = builder.getFreshName("i");
					try(BlockBuilder body = builder.forLoop(
							new Assignment(Collections.singletonList(acc), true, Collections.singletonList(from)),
							new Binop(Binop.Operation.LEQ, acc, to),
							new IncDec(true, acc))){
						body.assign(Collections.singletonList(new Index(tmpRange, acc)), Collections.singletonList(acc));
					}
					return tmpRange;
				}));

		BuiltinModule Integers = new BuiltinModule(Naturals);
		builtinModules.put("Integers", Integers);
		Integers.addOperator("-", new BuiltinOperator(
				1,
				(ctx, origin, args, solver, generator) -> {
					PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(origin), origin);
					solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
					return fresh;
				},
				(builder, origin, registry, arguments, typeMap) -> new Unary(Unary.Operation.NEG, arguments.get(0))
				));
		Integers.addOperator("Int", new BuiltinOperator(
				0,
				(ctx, origin, args, solver, generator) -> new PGoTypeNonEnumerableSet(new PGoTypeInt(origin), origin),
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
