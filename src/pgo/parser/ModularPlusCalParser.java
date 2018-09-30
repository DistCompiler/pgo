package pgo.parser;

import pgo.model.mpcal.*;
import pgo.model.pcal.PlusCalMultiProcess;
import pgo.model.pcal.PlusCalSingleProcess;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.*;

import java.util.Collections;
import java.util.regex.Pattern;

import static pgo.parser.PlusCalParser.*;
import static pgo.parser.TLAParser.EXPRESSION_NO_OPERATORS;
import static pgo.parser.TLAParser.parseTLAToken;
import static pgo.parser.ParseTools.*;

public class ModularPlusCalParser {
	private ModularPlusCalParser() {}

	private static final Pattern FIND_MPCAL = Pattern.compile(".*?\\(\\*.*?(?=--mpcal)", Pattern.DOTALL);
	private static final Pattern AFTER_MPCAL = Pattern.compile(".*?\\*\\).*$", Pattern.DOTALL);

	private static final Grammar<PlusCalVariableDeclaration> MPCAL_VAR_DECL = emptySequence()
			.part(parseOneOf(
					parsePlusCalToken("ref").map(seq -> new Located<>(seq.getLocation(), true)),
					nop().map(seq -> new Located<>(seq.getLocation(), false))))
			.part(IDENTIFIER)
			.map(seq -> new PlusCalVariableDeclaration(
					seq.getLocation(),
					seq.getValue().getFirst(),
					seq.getValue().getRest().getFirst().getValue(),
					false,
					new PlusCalDefaultInitValue(seq.getLocation())));

	private static final Grammar<ModularPlusCalArchetype> C_SYNTAX_ARCHETYPE = emptySequence()
			.drop(parsePlusCalToken("archetype"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(MPCAL_VAR_DECL, parsePlusCalToken(",")),
					nop().map(seq ->
							new LocatedList<PlusCalVariableDeclaration>(
									seq.getLocation(),
									Collections.emptyList()))))
			.drop(parsePlusCalToken(")"))
			.part(parseOneOf(
					VAR_DECLS,
					nop().map(seq -> new LocatedList<PlusCalVariableDeclaration>(
							seq.getLocation(),
							Collections.emptyList()))))
			.part(C_SYNTAX_COMPOUND_STMT)
			.map(seq -> new ModularPlusCalArchetype(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<ModularPlusCalMapping> MAPPING = emptySequence()
			.drop(parsePlusCalToken("mapping"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("via"))
			.part(IDENTIFIER)
			.map(seq -> new ModularPlusCalMapping(
					seq.getLocation(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst().getValue()));

	private static final Grammar<ModularPlusCalInstance> C_SYNTAX_INSTANCE = emptySequence()
			.drop(parsePlusCalToken("process"))
			.drop(parsePlusCalToken("("))
			.part(VARIABLE_DECLARATION)
			.drop(parsePlusCalToken(")"))
			.drop(parsePlusCalToken("="))
			.drop(parsePlusCalToken("instance"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(MODULAR_PLUSCAL_PARAMETER, parsePlusCalToken(",")),
					nop().map(seq -> new LocatedList<TLAExpression>(seq.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken(")"))
			.part(parseOneOf(
					parseListOf(MAPPING, nop()),
					nop().map(seq ->
							new LocatedList<ModularPlusCalMapping>(seq.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken(";"))
			.map(seq -> new ModularPlusCalInstance(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final ReferenceGrammar<ModularPlusCalYield> YIELD = new ReferenceGrammar<>();

	private static final Grammar<ModularPlusCalMappingMacro> C_SYNTAX_MAPPING_MACRO = emptySequence()
			.drop(parsePlusCalToken("mapping"))
			.drop(parsePlusCalToken("macro"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("{"))
			.drop(parsePlusCalToken("read"))
			.drop(parsePlusCalToken("{"))
			.part(parseListOf(C_SYNTAX_UNLABELED_STMT, parsePlusCalToken(";")))
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.drop(parsePlusCalToken("}"))
			.drop(parsePlusCalToken("write"))
			.drop(parsePlusCalToken("{"))
			.part(parseListOf(C_SYNTAX_UNLABELED_STMT, parsePlusCalToken(";")))
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.drop(parsePlusCalToken("}"))
			.drop(parsePlusCalToken("}"))
			.map(seq -> new ModularPlusCalMappingMacro(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<ModularPlusCalBlock> C_SYNTAX_MPCAL = emptySequence()
			.drop(parsePlusCalToken("--mpcal"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("{"))
			.part(parseOneOf(
					VAR_DECLS,
					nop().map(seq -> new LocatedList<PlusCalVariableDeclaration>(
							seq.getLocation(),
							Collections.emptyList()))))
			.part(parseOneOf(
					C_SYNTAX_DEFINITIONS,
					nop().map(seq -> new LocatedList<TLAUnit>(seq.getLocation(), Collections.emptyList()))))
			.part(parseOneOf(
					parseListOf(C_SYNTAX_MAPPING_MACRO, nop()),
					nop().map(seq -> new LocatedList<ModularPlusCalMappingMacro>(
							seq.getLocation(),
							Collections.emptyList()))))
			.part(parseOneOf(
					parseListOf(C_SYNTAX_ARCHETYPE, nop()),
					nop().map(seq -> new LocatedList<ModularPlusCalArchetype>(
							seq.getLocation(),
							Collections.emptyList()))))
			.part(repeat(C_SYNTAX_MACRO))
			.part(repeat(C_SYNTAX_PROCEDURE))
			.part(repeat(C_SYNTAX_INSTANCE))
			.part(parseOneOf(
					C_SYNTAX_COMPOUND_STMT.map(stmts -> new PlusCalSingleProcess(stmts.getLocation(), stmts)),
					repeatOneOrMore(C_SYNTAX_PROCESS).map(procs -> new PlusCalMultiProcess(procs.getLocation(), procs)),
					nop().map(seq -> new PlusCalMultiProcess(seq.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken("}"))
			.map(seq -> new ModularPlusCalBlock(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<ModularPlusCalBlock> MPCAL_BLOCK = emptySequence()
			.drop(matchPattern(FIND_MPCAL))
			.part(parseOneOf(C_SYNTAX_MPCAL))
			.drop(matchPattern(AFTER_MPCAL))
			.map(seq -> seq.getValue().getFirst());


	private interface ReadSpec {
		Object perform() throws ParseFailureException;
	}

	// Modular PlusCal behaves a lot like vanilla PlusCal except in a few key areas:
	//
	// * Unlabeled statements may include the `yield` keyword
	// * TLA+ expressions may include "special variables" (with dollar-sign prefixed names)
	//
	// This method overrides grammar references with the changes mentioned above before
	// parsing a MPCal specification, and then resets the grammars back to their
	// original contents (useful during testing, when PlusCal/MPCal can be parsed in
	// arbitrary orders).
	private static Object overwriteGrammars(ReadSpec op) throws ParseFailureException {
		Grammar<TLAExpression> oldTLAExpressionNoOperators = TLA_EXPRESSION_NO_OPERATORS.getReferencedGrammar();
		Grammar<TLAExpression> oldTLAExpression = TLA_EXPRESSION.getReferencedGrammar();
		Grammar<PlusCalStatement> oldUnlabeledStatement = C_SYNTAX_UNLABELED_STMT.getReferencedGrammar();

		try {
			// add special variables to TLA+ expressions
			assert oldTLAExpressionNoOperators != null;

			TLA_EXPRESSION_NO_OPERATORS.setReferencedGrammar(
					parseOneOf(
							parseTLAToken("$variable").map(seq -> new TLASpecialVariableVariable(seq.getLocation())),
							parseTLAToken("$value").map(seq -> new TLASpecialVariableValue(seq.getLocation())),

							EXPRESSION_NO_OPERATORS
					)
			);

			initTLAExpression(TLA_EXPRESSION);

			// make sure the definition of the `yield` rule uses the updated TLA+ expression grammar
			// which includes special variables.
			YIELD.setReferencedGrammar(
					emptySequence()
							.drop(parsePlusCalToken("yield"))
							.part(TLA_EXPRESSION)
							.map(seq -> new ModularPlusCalYield(seq.getLocation(), seq.getValue().getFirst()))
			);

			// updates unlabeled statements to include `yield` statements.
			assert oldUnlabeledStatement != null;
			C_SYNTAX_UNLABELED_STMT.setReferencedGrammar(
					parseOneOf(
							oldUnlabeledStatement,
							YIELD
					)
			);

			return op.perform();
		} finally {
			TLA_EXPRESSION_NO_OPERATORS.setReferencedGrammar(oldTLAExpressionNoOperators);
			TLA_EXPRESSION.setReferencedGrammar(oldTLAExpression);
			C_SYNTAX_UNLABELED_STMT.setReferencedGrammar(oldUnlabeledStatement);
		}
	}

	// public interface

	public static boolean hasModularPlusCalBlock(LexicalContext ctx) {
		return ctx.matchPattern(FIND_MPCAL).isPresent();
	}

	public static ModularPlusCalBlock readBlock(LexicalContext ctx) throws ParseFailureException {
		Object block = overwriteGrammars(
				() -> readOrExcept(ctx, MPCAL_BLOCK)
		);

		return (ModularPlusCalBlock) block;
	}

	// testing interface

	static ModularPlusCalUnit readUnit(LexicalContext ctx) throws ParseFailureException {
		Object unit = overwriteGrammars(
				() -> readOrExcept(ctx, parseOneOf(C_SYNTAX_ARCHETYPE, C_SYNTAX_INSTANCE, C_SYNTAX_MAPPING_MACRO))
		);

		return (ModularPlusCalUnit) unit;
	}
}
