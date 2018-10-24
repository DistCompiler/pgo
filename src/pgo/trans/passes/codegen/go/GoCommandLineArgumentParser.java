package pgo.trans.passes.codegen.go;

import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;

import java.util.*;
import java.util.stream.Collectors;

// TODO add support for GoRoutineStatement's flag package
public class GoCommandLineArgumentParser {
	private Map<String, String> positionalArguments = new LinkedHashMap<>();

	public void addPositionalArgument(String name, String display) {
		positionalArguments.put(name, display);
	}

	public List<GoVariableName> generateArgumentParsingCode(GoBlockBuilder builder) {
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
		try (GoIfBuilder ifBuilder = builder.ifStmt(new GoBinop(
				GoBinop.Operation.NEQ,
				new GoCall(
						new GoVariableName("len"),
						Collections.singletonList(new GoSelectorExpression(new GoVariableName("os"), "Args"))),
				new GoIntLiteral(positionalArguments.size() + 1)))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addStatement(new GoCall(
						new GoSelectorExpression(new GoVariableName("fmt"), "Printf"),
						Arrays.asList(
								new GoStringLiteral("Usage: %s " +
										positionalArguments.values().stream()
												.collect(Collectors.joining(" ")) +
										"\\n"),
								new GoIndexExpression(
										new GoSelectorExpression(new GoVariableName("os"), "Args"),
										new GoIntLiteral(0)))));
				yes.addStatement(new GoCall(
						new GoSelectorExpression(new GoVariableName("os"), "Exit"),
						Collections.singletonList(new GoIntLiteral(1))));
			}
		}
		List<GoVariableName> ret = new ArrayList<>();
		int currentIndex = 1;
		for (String name: positionalArguments.keySet()) {
			ret.add(builder.varDecl(
					name,
					new GoIndexExpression(
							new GoSelectorExpression(new GoVariableName("os"), "Args"),
							new GoIntLiteral(currentIndex))));
			currentIndex += 1;
		}
		return ret;
	}
}
