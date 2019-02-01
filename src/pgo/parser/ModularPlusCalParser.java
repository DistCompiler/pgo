package pgo.parser;

import pgo.InternalCompilerError;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.*;
import pgo.util.SourceLocatable;

import java.util.Collections;
import java.util.regex.Pattern;

import static pgo.parser.PlusCalParser.*;
import static pgo.parser.ParseTools.*;
import static pgo.parser.TLAParser.EXPRESSION_NO_OPERATORS;

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

	private static final Grammar<TLAExpression> MODULAR_PLUSCAL_PARAMETER = parseOneOf(
			TLA_EXPRESSION,
			emptySequence()
					.dependentPart(emptySequence()
									.drop(TLAParser.parseTLAToken("ref"))
									.drop(TLAParser.skipWhitespaceAndTLAComments())
									.part(TLAParser.matchTLAIdentifier())
									.map(seq -> new TLARef(seq.getLocation(), seq.getValue().getFirst().getValue())),
							info -> new VariableMap().put(MIN_COLUMN, -1))
					.map(seq -> seq.getValue().getFirst()));

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
			.part(parseOneOf(
					parsePlusCalToken("[_]").map(seq -> new Located<>(seq.getLocation(), true)),
					nop().map(seq -> new Located<>(seq.getLocation(), false))))
			.drop(parsePlusCalToken("via"))
			.part(IDENTIFIER)
			.map(seq -> new ModularPlusCalMapping(
					seq.getLocation(),
					new ModularPlusCalMappingVariable(
							seq.getValue().getRest().getFirst().getLocation(),
							seq.getValue().getRest().getRest().getFirst().getValue(),
							seq.getValue().getRest().getFirst().getValue()),
					new ModularPlusCalMappingTarget(
							seq.getValue().getFirst().getLocation(),
							seq.getValue().getFirst().getValue())));

	private static final Grammar<ModularPlusCalInstance> C_SYNTAX_INSTANCE = emptySequence()
			.part(parseOneOf(
					emptySequence()
							.drop(parsePlusCalToken("fair"))
							.drop(parsePlusCalToken("+"))
							.map(seq -> new Located<>(seq.getLocation(), PlusCalFairness.STRONG_FAIR)),
					parsePlusCalToken("fair").map(s -> new Located<>(s.getLocation(), PlusCalFairness.WEAK_FAIR)),
					nop().map(v -> new Located<>(v.getLocation(), PlusCalFairness.UNFAIR))
			))
			.drop(parsePlusCalToken("process"))
			.drop(parsePlusCalToken("("))
			.part(VARIABLE_DECLARATION)
			.drop(parsePlusCalToken(")"))
			.drop(parsePlusCalToken("=="))
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
					seq.getValue().getRest().getRest().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<ModularPlusCalYield> YIELD = emptySequence()
			.drop(parsePlusCalToken("yield"))
			.part(TLA_EXPRESSION)
			.map(seq -> new ModularPlusCalYield(seq.getLocation(), seq.getValue().getFirst()));

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
					C_SYNTAX_DEFINITIONS,
					nop().map(seq -> new LocatedList<TLAUnit>(seq.getLocation(), Collections.emptyList()))))
			.part(repeat(C_SYNTAX_MACRO))
			.part(repeat(C_SYNTAX_PROCEDURE))
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
			.part(parseOneOf(
					VAR_DECLS,
					nop().map(seq -> new LocatedList<PlusCalVariableDeclaration>(
							seq.getLocation(),
							Collections.emptyList()))))
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

	private static final Pattern MPCAL_SPECIAL_VARIABLE = Pattern.compile("\\$variable|\\$value");

	private static Grammar<Located<String>> matchSpecialVariable() {
		return matchPattern(MPCAL_SPECIAL_VARIABLE)
				.map(result -> new Located<>(result.getLocation(), result.getValue().group()));
	}

	private static Grammar<TLAExpression> parseSpecialVariables() {
		return emptySequence()
				.drop(TLAParser.skipWhitespaceAndTLAComments())
				.part(matchSpecialVariable())
				.map(seq -> seq.getValue().getFirst())
				.map(id -> {
					if (id.getValue().equals("$variable")) {
						return new TLASpecialVariableVariable(id.getLocation());
					}

					return new TLASpecialVariableValue(id.getLocation());
				});
	}

	private interface ReadSpec<Result extends SourceLocatable> {
		Result perform() throws ParseFailureException;
	}

	// Modular PlusCal behaves a lot like vanilla PlusCal except in a few key areas:
	//
	// * Unlabeled statements may include the `yield` keyword
	// * TLA+ expressions may include "special variables" (with dollar-sign prefixed names)
	// * procedures can be declared to take arguments by `ref`, and the caller may specify
	//   parameters using the `ref` keyword.
	//
	// This method overrides grammar references with the changes mentioned above before
	// parsing a MPCal specification, and then resets the grammars back to their
	// original contents (useful during testing, when PlusCal/MPCal can be parsed in
	// arbitrary orders).
	private static <Result extends SourceLocatable> Result overwriteGrammars(ReadSpec<Result> op) throws ParseFailureException {
		Grammar<PlusCalStatement> oldUnlabeledStatement = C_SYNTAX_UNLABELED_STMT.getReferencedGrammar();
		Grammar<PlusCalVariableDeclaration> oldPVarDecl = PVAR_DECL.getReferencedGrammar();
		Grammar<TLAExpression> oldProcedureParam = PROCEDURE_PARAM.getReferencedGrammar();
		Grammar<TLAExpression> oldTLAIdExpr = TLA_IDEXPR.getReferencedGrammar();
		Grammar<TLAExpression> oldTLAExprNoOperators = EXPRESSION_NO_OPERATORS.getReferencedGrammar();

		try {
			// updates unlabeled statements to include `yield` statements.
			if (oldUnlabeledStatement == null) {
				throw new InternalCompilerError();
			}
			C_SYNTAX_UNLABELED_STMT.setReferencedGrammar(
					parseOneOf(
							oldUnlabeledStatement,
							YIELD
					)
			);

			// allow procedures to be declared to take arguments by `ref`
			if (oldPVarDecl == null) {
				throw new InternalCompilerError();
			}
			PVAR_DECL.setReferencedGrammar(
					parseOneOf(
							emptySequence()
									.drop(parsePlusCalToken("ref"))
									.part(IDENTIFIER)
									.map(seq -> new PlusCalVariableDeclaration(
											seq.getLocation(),
											seq.getValue().getFirst(),
											true,
											false,
											new PlusCalDefaultInitValue(seq.getLocation()))),
							oldPVarDecl
					)
			);

			// allow call Proc() to be able to pass variables by `ref`
			if (oldProcedureParam == null) {
				throw new InternalCompilerError();
			}
			PROCEDURE_PARAM.setReferencedGrammar(MODULAR_PLUSCAL_PARAMETER);

			// include special variables (`$variable` and `$value`) as part of identifiers
			// recognized by the parser (so that special variables can be assigned to).
			if (oldTLAIdExpr == null) {
				throw new InternalCompilerError();
			}
			TLA_IDEXPR.setReferencedGrammar(
					parseOneOf(
							oldTLAIdExpr,
							parseSpecialVariables()
					)
			);

			// include special variables to the list of TLA+ expressions without operators
			// recognized by the parser.
			if (oldTLAExprNoOperators == null) {
				throw new InternalCompilerError();
			}
			EXPRESSION_NO_OPERATORS.setReferencedGrammar(
					parseOneOf(
							oldTLAExprNoOperators,
							parseSpecialVariables()
					)
			);

			return op.perform();
		} finally {
			C_SYNTAX_UNLABELED_STMT.setReferencedGrammar(oldUnlabeledStatement);
			PVAR_DECL.setReferencedGrammar(oldPVarDecl);
			PROCEDURE_PARAM.setReferencedGrammar(oldProcedureParam);
			TLA_IDEXPR.setReferencedGrammar(oldTLAIdExpr);
			EXPRESSION_NO_OPERATORS.setReferencedGrammar(oldTLAExprNoOperators);
		}
	}

	// public interface

	public static boolean hasModularPlusCalBlock(LexicalContext ctx) {
		return ctx.matchPattern(FIND_MPCAL).isPresent();
	}

	public static ModularPlusCalBlock readBlock(LexicalContext ctx) throws ParseFailureException {
		return overwriteGrammars(() -> readOrExcept(ctx, MPCAL_BLOCK));
	}

	// testing interface

	static ModularPlusCalUnit readUnit(LexicalContext ctx) throws ParseFailureException {
		return overwriteGrammars(() ->
				readOrExcept(ctx, parseOneOf(C_SYNTAX_ARCHETYPE, C_SYNTAX_INSTANCE, C_SYNTAX_MAPPING_MACRO)));
	}
}
