package pgo.trans.intermediate;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import pgo.model.type.*;
import pgo.scope.UID;

public class TLABuiltins {

	private TLABuiltins() {}

	private static BuiltinModule universalBuiltins = new BuiltinModule();
	static {
		universalBuiltins.addOperator("=", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), args.get(1)));
			return new PGoTypeBool(origin);
		}));
		universalBuiltins.addOperator("#", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), args.get(1)));
			return new PGoTypeBool(origin);
		}));
		universalBuiltins.addOperator("\\in", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoTypeVariable memberType = generator.get();
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), memberType));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), new PGoTypeSet(memberType)));
			return new PGoTypeBool(origin);
		}));
		universalBuiltins.addOperator("\\", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoTypeVariable memberType = generator.get();
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), new PGoTypeSet(memberType)));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), new PGoTypeSet(memberType)));
			return new PGoTypeSet(memberType, origin);
		}));
		universalBuiltins.addOperator("~", new BuiltinOperator(1, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeBool(origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			return fresh;
		}));
		universalBuiltins.addOperator("\\/", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeBool(origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return fresh;
		}));
		universalBuiltins.addOperator("/\\", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeBool(origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return fresh;
		}));
		universalBuiltins.addOperator("\\union", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoTypeVariable memberType = generator.get();
			PGoType fresh = new PGoTypeSet(memberType, origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return fresh;
		}));
	}

	private static Map<String, BuiltinModule> builtinModules = new HashMap<>();
	static {
		BuiltinModule TLC = new BuiltinModule();
		builtinModules.put("TLC", TLC);


		BuiltinModule Sequences = new BuiltinModule();
		builtinModules.put("Sequences", Sequences);
		Sequences.addOperator("Len", new PolymorphicBuiltinOperator(1, Arrays.asList(
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
				})));
		Sequences.addOperator("Append", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoTypeVariable elementType = generator.get();
			PGoType fresh = new PGoTypeSlice(elementType, origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), elementType));
			return fresh;
		}));
		Sequences.addOperator("Head", new BuiltinOperator(1, (ctx, origin, args, solver, generator) -> {
			PGoTypeVariable elementType = generator.get();
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), new PGoTypeSlice(elementType, origin)));
			return elementType;
		}));
		Sequences.addOperator("Tail", new BuiltinOperator(1, (ctx, origin, args, solver, generator) -> {
			PGoTypeVariable elementType = generator.get();
			PGoType fresh = new PGoTypeSlice(elementType, origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			return fresh;
		}));

		BuiltinModule Naturals = new BuiltinModule();
		builtinModules.put("Naturals", Naturals);
		Naturals.addOperator("-", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return fresh;
		}));
		Naturals.addOperator("+", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return fresh;
		}));
		Naturals.addOperator("%", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = PGoTypeUnrealizedNumber.integralType(new PGoTypeNatural(origin), origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return fresh;
		}));
		Naturals.addOperator("*", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return fresh;
		}));
		Naturals.addOperator("<", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return new PGoTypeBool(origin);
		}));
		Naturals.addOperator(">", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return new PGoTypeBool(origin);
		}));
		// TODO: \leq =<
		Naturals.addOperator("<=", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return new PGoTypeBool(origin);
		}));
		// TODO: \geq
		Naturals.addOperator(">=", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origin), origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return new PGoTypeBool(origin);
		}));
		Naturals.addOperator("Nat", new BuiltinOperator(0, (ctx, origin, args, solver, generator) ->
				new PGoTypeSet(new PGoTypeNatural(origin), origin)));
		Naturals.addOperator("..", new BuiltinOperator(2, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = PGoTypeUnrealizedNumber.integralType(origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(1), fresh));
			return new PGoTypeSet(fresh);
		}));

		BuiltinModule Integers = new BuiltinModule(Naturals);
		builtinModules.put("Integers", Integers);
		Integers.addOperator("-", new BuiltinOperator(1, (ctx, origin, args, solver, generator) -> {
			PGoType fresh = new PGoTypeUnrealizedNumber(new PGoTypeInt(origin), origin);
			solver.addConstraint(ctx, new PGoTypeConstraint(origin, args.get(0), fresh));
			return fresh;
		}));
		Integers.addOperator("Int", new BuiltinOperator(0, (ctx, origin, args, solver, generator) ->
				new PGoTypeSet(new PGoTypeInt(origin), origin)));

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
		for(Map.Entry<String, BuiltinOperator> op : universalBuiltins.getOperators().entrySet()) {
			defs.put(new QualifiedName(op.getKey()), op.getValue().getUID());
		}
		return defs;
	}

}
