package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.Map;

import pgo.model.type.PGoTypeBool;
import pgo.model.type.PGoTypeConstraint;
import pgo.model.type.PGoTypeInt;
import pgo.model.type.PGoTypeNatural;
import pgo.model.type.PGoTypeSet;
import pgo.model.type.PGoTypeSlice;
import pgo.model.type.PGoTypeUnrealizedTuple;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;

public class TLABuiltins {

	private TLABuiltins() {}

	private static BuiltinModule universalBuiltins = new BuiltinModule();
	static {
		universalBuiltins.addOperator("=", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), args.get(1)));
			return PGoTypeBool.getInstance();
		}));
		universalBuiltins.addOperator("#", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), args.get(1)));
			return PGoTypeBool.getInstance();
		}));
		universalBuiltins.addOperator("\\in", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			PGoTypeVariable memberType = generator.get();
			solver.accept(new PGoTypeConstraint(origin, args.get(0), memberType));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), new PGoTypeSet(memberType)));
			return PGoTypeBool.getInstance();
		}));
		universalBuiltins.addOperator("\\", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			PGoTypeVariable memberType = generator.get();
			solver.accept(new PGoTypeConstraint(origin, args.get(0), new PGoTypeSet(memberType)));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), new PGoTypeSet(memberType)));
			return new PGoTypeSet(memberType);
		}));
		universalBuiltins.addOperator("~", new BuiltinOperator(1, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeBool.getInstance()));
			return PGoTypeBool.getInstance();
		}));
		universalBuiltins.addOperator("\\/", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeBool.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeBool.getInstance()));
			return PGoTypeBool.getInstance();
		}));
		universalBuiltins.addOperator("/\\", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeBool.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeBool.getInstance()));
			return PGoTypeBool.getInstance();
		}));
		universalBuiltins.addOperator("\\union", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			PGoTypeVariable memberType = generator.get();
			solver.accept(new PGoTypeConstraint(origin, args.get(0), new PGoTypeSet(memberType)));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), new PGoTypeSet(memberType)));
			return new PGoTypeSet(memberType);
		}));
	}

	private static Map<String, BuiltinModule> builtinModules = new HashMap<>();
	static {
		BuiltinModule TLC = new BuiltinModule();
		builtinModules.put("TLC", TLC);


		BuiltinModule Sequences = new BuiltinModule();
		builtinModules.put("Sequences", Sequences);
		Sequences.addOperator("Len", new BuiltinOperator(1, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), new PGoTypeUnrealizedTuple()));
			return PGoTypeNatural.getInstance();
		}));
		Sequences.addOperator("Append", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			PGoTypeVariable elementType = generator.get();
			solver.accept(new PGoTypeConstraint(origin, args.get(0), new PGoTypeSlice(elementType)));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), elementType));
			return new PGoTypeSlice(elementType);
		}));
		Sequences.addOperator("Head", new BuiltinOperator(1, (origin, args, solver, generator) -> {
			PGoTypeVariable elementType = generator.get();
			solver.accept(new PGoTypeConstraint(origin, args.get(0), new PGoTypeSlice(elementType)));
			return elementType;
		}));
		Sequences.addOperator("Tail", new BuiltinOperator(1, (origin, args, solver, generator) -> {
			PGoTypeVariable elementType = generator.get();
			solver.accept(new PGoTypeConstraint(origin, args.get(0), new PGoTypeSlice(elementType)));
			return new PGoTypeSlice(elementType);
		}));

		BuiltinModule Naturals = new BuiltinModule();
		builtinModules.put("Naturals", Naturals);
		Naturals.addOperator("-", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeNatural.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeNatural.getInstance()));
			return PGoTypeNatural.getInstance();
		}));
		Naturals.addOperator("+", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeNatural.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeNatural.getInstance()));
			return PGoTypeNatural.getInstance();
		}));
		Naturals.addOperator("%", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeNatural.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeNatural.getInstance()));
			return PGoTypeNatural.getInstance();
		}));
		Naturals.addOperator("*", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeNatural.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeNatural.getInstance()));
			return PGoTypeNatural.getInstance();
		}));
		Naturals.addOperator("<", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeNatural.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeNatural.getInstance()));
			return PGoTypeBool.getInstance();
		}));
		Naturals.addOperator(">", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeNatural.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeNatural.getInstance()));
			return PGoTypeBool.getInstance();
		}));
		// TODO: \leq =<
		Naturals.addOperator("<=", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeNatural.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeNatural.getInstance()));
			return PGoTypeBool.getInstance();
		}));
		// TODO: \geq
		Naturals.addOperator(">=", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeNatural.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeNatural.getInstance()));
			return PGoTypeBool.getInstance();
		}));
		Naturals.addOperator("Nat", new BuiltinOperator(0, (origin, args, solver, generator) ->
				new PGoTypeSet(PGoTypeNatural.getInstance())));
		Naturals.addOperator("..", new BuiltinOperator(2, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeNatural.getInstance()));
			solver.accept(new PGoTypeConstraint(origin, args.get(1), PGoTypeNatural.getInstance()));
			return new PGoTypeSet(PGoTypeNatural.getInstance());
		}));

		BuiltinModule Integers = new BuiltinModule(Naturals);
		builtinModules.put("Integers", Integers);
		Integers.addOperator("-", new BuiltinOperator(1, (origin, args, solver, generator) -> {
			solver.accept(new PGoTypeConstraint(origin, args.get(0), PGoTypeNatural.getInstance()));
			return PGoTypeInt.getInstance();
		}));
		Integers.addOperator("Int", new BuiltinOperator(0, (origin, args, solver, generator) ->
				new PGoTypeSet(PGoTypeInt.getInstance())));

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
