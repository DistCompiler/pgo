package pgo.trans.passes.codegen;

import pgo.model.golang.*;

import java.util.*;
import java.util.stream.Collectors;

// TODO add support for Go's flag package
public class GoCommandLineArgumentParser {
	private Map<String, String> positionalArguments = new LinkedHashMap<>();

	public void addPositionalArgument(String name, String display) {
		positionalArguments.put(name, display);
	}

	public List<VariableName> generateArgumentParsingCode(BlockBuilder builder) {
		if (positionalArguments.size() == 0) {
			// nothing to do
			return Collections.emptyList();
		}
		builder.addImport("os");
		builder.addImport("fmt");
		// if len(os.Args) < positionalArguments.size() + 1 {
		// 	fmt.Printf("Usage: %s positionalArgs...", os.Args[0])
		// 	os.Exit(1)
		// }
		try (IfBuilder ifBuilder = builder.ifStmt(new Binop(
				Binop.Operation.NEQ,
				new Call(
						new VariableName("len"),
						Collections.singletonList(new Selector(new VariableName("os"), "Args"))),
				new IntLiteral(positionalArguments.size() + 1)))) {
			try (BlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addStatement(new Call(
						new Selector(new VariableName("fmt"), "Printf"),
						Arrays.asList(
								new StringLiteral("Usage: %s " +
										positionalArguments.values().stream()
												.collect(Collectors.joining(" ")) +
										"\\n"),
								new Index(
										new Selector(new VariableName("os"), "Args"),
										new IntLiteral(0)))));
				yes.addStatement(new Call(
						new Selector(new VariableName("os"), "Exit"),
						Collections.singletonList(new IntLiteral(1))));
			}
		}
		List<VariableName> ret = new ArrayList<>();
		int currentIndex = 1;
		for (String name: positionalArguments.keySet()) {
			ret.add(builder.varDecl(
					name,
					new Index(
							new Selector(new VariableName("os"), "Args"),
							new IntLiteral(currentIndex))));
			currentIndex += 1;
		}
		return ret;
	}
}
