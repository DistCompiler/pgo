package pgo.parser;

import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.*;

import java.util.*;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static pgo.parser.ParseTools.*;

/**
 * The pluscal parser.
 *
 * This class takes a given pluscal file and parses it into the pluscal AST.
 *
 */
public final class PlusCalParser {
	private PlusCalParser() {}

	private static final Pattern PCAL_FIND_ALGORITHM = Pattern.compile(".*?\\(\\*.*?(?=--algorithm)", Pattern.DOTALL);
	private static final Pattern PCAL_AFTER_ALGORITHM = Pattern.compile(".*?\\*\\).*$", Pattern.DOTALL);

	/**
	 * Creates a parse action that accepts the string t, skipping any preceding comments or whitespace.
	 * @param t the token to accept
	 * @return the parse action
	 */
	private static Grammar<Located<Void>> parsePlusCalToken(String t){
		return emptySequence()
				.drop(TLAParser.skipWhitespaceAndTLAComments())
				.part(matchString(t))
				.map(seq -> seq.getValue().getFirst());
	}

	/**
	 * Creates a parse action that accepts any of the string in options, skipping any preceding comments or whitespace.
	 * @param options a list of token values to accept
	 * @return the parse action, yielding which token was accepted
	 */
	private static Grammar<Located<String>> parsePlusCalTokenOneOf(List<String> options){
		return emptySequence()
				.drop(TLAParser.skipWhitespaceAndTLAComments())
				.part(matchStringOneOf(options))
				.map(seq -> seq.getValue().getFirst());
	}

	// common

	private static final Grammar<TLAExpression> TLA_EXPRESSION = emptySequence()
			.dependentPart(
					TLAParser.parseExpression(
							TLAParser.PREFIX_OPERATORS,
							TLAParser.INFIX_OPERATORS
									.stream()
									.filter(op -> !Arrays.asList("||", ":=").contains(op))
									.collect(Collectors.toList()),
							TLAParser.POSTFIX_OPERATORS),
					info -> new VariableMap().put(MIN_COLUMN, -1))
			.map(seq -> seq.getValue().getFirst());

	private static final Grammar<Located<String>> IDENTIFIER = emptySequence()
			.drop(TLAParser.skipWhitespaceAndTLAComments())
			.part(TLAParser.matchTLAIdentifier())
			.map(seq -> seq.getValue().getFirst());

	private static final Grammar<PlusCalVariableDeclaration> VARIABLE_DECLARATION = emptySequence()
			.part(IDENTIFIER)
			.part(parseOneOf(
					parsePlusCalToken("\\in")
							.map(v -> new Located<>(v.getLocation(), true)),
					parsePlusCalToken("=")
							.map(v -> new Located<>(v.getLocation(), false))
			))
			.part(cut(TLA_EXPRESSION))
			.map(seq -> new PlusCalVariableDeclaration(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst().getValue(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalVariableDeclaration> VAR_DECL = emptySequence()
			.part(parseOneOf(
					VARIABLE_DECLARATION,
					IDENTIFIER.map(id -> new PlusCalVariableDeclaration(
							id.getLocation(), id, false, new PlusCalDefaultInitValue(id.getLocation())))
			))
			.drop(parseOneOf(parsePlusCalToken(";"), parsePlusCalToken(",")))
			.map(seq -> seq.getValue().getFirst());

	private static final Grammar<LocatedList<PlusCalVariableDeclaration>> VAR_DECLS = emptySequence()
			.drop(parseOneOf(parsePlusCalToken("variables"), parsePlusCalToken("variable")))
			.part(cut(repeatOneOrMore(VAR_DECL)))
			.map(seq -> seq.getValue().getFirst());

	private static final Grammar<PlusCalVariableDeclaration> PVAR_DECL = emptySequence()
			.part(IDENTIFIER)
			.part(parseOneOf(
					emptySequence()
							.drop(parsePlusCalToken("="))
							.part(TLA_EXPRESSION)
							.map(seq -> seq.getValue().getFirst()),
					nop().map(v -> new PlusCalDefaultInitValue(v.getLocation()))
			))
			.map(seq -> new PlusCalVariableDeclaration(
					seq.getLocation(),
					seq.getValue().getRest().getFirst(),
					false,
					seq.getValue().getFirst()));

	private static final Grammar<LocatedList<PlusCalVariableDeclaration>> PVAR_DECLS = emptySequence()
			.drop(parseOneOf(parsePlusCalToken("variables"), parsePlusCalToken("variable")))
			.part(repeatOneOrMore(
					emptySequence()
							.part(PVAR_DECL)
							.drop(parseOneOf(parsePlusCalToken(";"), parsePlusCalToken(",")))
							.map(seq -> seq.getValue().getFirst())
			))
			.map(seq -> seq.getValue().getFirst());

	private static final Grammar<ModularPlusCalVariableDeclaration> MPCAL_VAR_DECL = emptySequence()
			.part(parseOneOf(
					parsePlusCalToken("ref").map(seq -> new Located<>(seq.getLocation(), true)),
					nop().map(seq -> new Located<>(seq.getLocation(), false))))
			.part(IDENTIFIER)
			.map(seq -> new ModularPlusCalVariableDeclaration(
					seq.getLocation(),
					seq.getValue().getFirst(),
					seq.getValue().getRest().getFirst().getValue()));

	// shortcut to parse a limited form of TLA+ identifiers (as seen in PlusCal assignments)
	private static final Grammar<TLAGeneralIdentifier> TLA_IDEXPR = IDENTIFIER.map(id -> new TLAGeneralIdentifier(
			id.getLocation(),
			new TLAIdentifier(id.getLocation(), id.getValue()),
			Collections.emptyList()));

	private static final Grammar<TLAExpression> LHS = parseOneOf(
			emptySequence()
					.part(TLA_IDEXPR)
					.drop(parsePlusCalToken("["))
					.part(parseListOf(TLA_EXPRESSION, parsePlusCalToken(",")))
					.drop(parsePlusCalToken("]"))
					.map(seq -> new TLAFunctionCall(
							seq.getLocation(),
							seq.getValue().getRest().getFirst(),
							seq.getValue().getFirst())),
			emptySequence()
					.part(TLA_IDEXPR)
					.part(parsePlusCalToken("."))
					.part(TLA_IDEXPR)
					.map(seq -> new TLABinOp(
							seq.getLocation(),
							new TLASymbol(seq.getValue().getRest().getFirst().getLocation(), "."),
							Collections.emptyList(),
							seq.getValue().getRest().getRest().getFirst(),
							seq.getValue().getFirst())),
			TLA_IDEXPR);

	private static final Grammar<PlusCalAssignment> ASSIGN = parseListOf(
			emptySequence()
					.part(LHS)
					.drop(parsePlusCalToken(":="))
					.part(TLA_EXPRESSION)
					.map(seq -> new PlusCalAssignmentPair(
							seq.getLocation(),
							seq.getValue().getRest().getFirst(),
							seq.getValue().getFirst())),
			parsePlusCalToken("||")
	).map(pairs -> new PlusCalAssignment(pairs.getLocation(), pairs));

	private static final Grammar<PlusCalAwait> AWAIT = emptySequence()
			.drop(parsePlusCalTokenOneOf(Arrays.asList("await", "when")))
			.part(TLA_EXPRESSION)
			.map(seq -> new PlusCalAwait(seq.getLocation(), seq.getValue().getFirst()));

	private static final Grammar<PlusCalPrint> PRINT = emptySequence()
			.drop(parsePlusCalToken("print"))
			.part(TLA_EXPRESSION)
			.map(seq -> new PlusCalPrint(seq.getLocation(), seq.getValue().getFirst()));

	private static final Grammar<PlusCalAssert> ASSERT = emptySequence()
			.drop(parsePlusCalToken("assert"))
			.part(TLA_EXPRESSION)
			.map(seq -> new PlusCalAssert(seq.getLocation(), seq.getValue().getFirst()));

	private static final Grammar<PlusCalSkip> SKIP = parsePlusCalToken("skip").map(v -> new PlusCalSkip(v.getLocation()));

	private static final Grammar<PlusCalReturn> RETURN = parsePlusCalToken("return")
			.map(v -> new PlusCalReturn(v.getLocation()));

	private static final Grammar<PlusCalGoto> GOTO = emptySequence()
			.drop(parsePlusCalToken("goto"))
			.part(IDENTIFIER)
			.map(seq -> new PlusCalGoto(seq.getLocation(), seq.getValue().getFirst().getValue()));

	private static final Grammar<PlusCalCall> CALL = emptySequence()
			.drop(parsePlusCalToken("call"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(TLA_EXPRESSION, parsePlusCalToken(",")),
					nop().map(v -> new LocatedList<TLAExpression>(v.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken(")"))
			.map(seq -> new PlusCalCall(
					seq.getLocation(),
					seq.getValue().getRest().getFirst().getValue(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalMacroCall> MACRO_CALL = emptySequence()
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(TLA_EXPRESSION, parsePlusCalToken(",")),
					nop().map(v -> new LocatedList<TLAExpression>(v.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken(")"))
			.map(seq -> new PlusCalMacroCall(
					seq.getLocation(),
					seq.getValue().getRest().getFirst().getValue(),
					seq.getValue().getFirst()));

	// C-syntax

	private static final ReferenceGrammar<LocatedList<PlusCalStatement>> C_SYNTAX_COMPOUND_STMT = new ReferenceGrammar<>();
	private static final ReferenceGrammar<LocatedList<PlusCalStatement>> C_SYNTAX_STMT = new ReferenceGrammar<>();

	private static final Grammar<PlusCalIf> C_SYNTAX_IF = emptySequence()
			.drop(parsePlusCalToken("if"))
			.drop(parsePlusCalToken("("))
			.part(TLA_EXPRESSION)
			.drop(parsePlusCalToken(")"))
			.part(C_SYNTAX_STMT)
			.drop(parseOneOf(parsePlusCalToken(";"), nop())) // not in the grammar, but apparently an optional semicolon is valid here
			.part(parseOneOf(
					emptySequence()
							.drop(parsePlusCalToken("else"))
							.part(C_SYNTAX_STMT)
							.map(seq -> seq.getValue().getFirst()),
					nop().map(v -> new LocatedList<PlusCalStatement>(v.getLocation(), Collections.emptyList()))
			))
			.map(seq -> new PlusCalIf(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalWhile> C_SYNTAX_WHILE = emptySequence()
			.drop(parsePlusCalToken("while"))
			.drop(parsePlusCalToken("("))
			.part(TLA_EXPRESSION)
			.drop(parsePlusCalToken(")"))
			.part(C_SYNTAX_STMT)
			.map(seq -> new PlusCalWhile(
					seq.getLocation(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalEither> C_SYNTAX_EITHER = emptySequence()
			.drop(parsePlusCalToken("either"))
			.part(C_SYNTAX_STMT)
			.part(repeatOneOrMore(
					emptySequence()
							.drop(parsePlusCalToken("or"))
							.part(C_SYNTAX_STMT)
							.map(seq -> seq.getValue().getFirst())
			))
			.map(seq -> {
				List<List<PlusCalStatement>> branches = new ArrayList<>(seq.getValue().getFirst().size()+1);
				branches.add(seq.getValue().getRest().getFirst());
				branches.addAll(seq.getValue().getFirst());
				return new PlusCalEither(seq.getLocation(), branches);
			});

	private static final Grammar<PlusCalWith> C_SYNTAX_WITH = emptySequence()
			.drop(parsePlusCalToken("with"))
			.drop(parsePlusCalToken("("))
			.part(parseListOf(VARIABLE_DECLARATION, parsePlusCalTokenOneOf(Arrays.asList(";", ","))))
			.drop(parseOneOf(parsePlusCalToken(";"), parsePlusCalToken(","), nop()))
			.drop(parsePlusCalToken(")"))
			.part(C_SYNTAX_STMT)
			.map(seq -> new PlusCalWith(
					seq.getLocation(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalStatement> C_SYNTAX_UNLABELEDSTMT = parseOneOf(
			ASSIGN,
			C_SYNTAX_IF,
			C_SYNTAX_WHILE,
			C_SYNTAX_EITHER,
			C_SYNTAX_WITH,
			AWAIT,
			PRINT,
			ASSERT,
			SKIP,
			RETURN,
			GOTO,
			CALL,
			MACRO_CALL
	);

	static {
		C_SYNTAX_STMT.setReferencedGrammar(
				parseOneOf(
						emptySequence()
								.part(emptySequence().part(IDENTIFIER)
										.drop(parsePlusCalToken(":"))
										.part(parseOneOf(
												parsePlusCalToken("+").map(v -> new Located<>(
														v.getLocation(), PlusCalLabel.Modifier.PLUS)),
												parsePlusCalToken("-").map(v -> new Located<>(
														v.getLocation(), PlusCalLabel.Modifier.MINUS)),
												nop().map(v -> new Located<>(
														v.getLocation(), PlusCalLabel.Modifier.NONE))
										))
										.map(seq -> new PlusCalLabel(
												seq.getLocation(),
												seq.getValue().getRest().getFirst().getValue(),
												seq.getValue().getFirst().getValue()))
								)
								.part(parseOneOf(
										parseListOf(C_SYNTAX_UNLABELEDSTMT, parsePlusCalToken(";")), // catch repeated statements instead of parsing them as sibling nodes
										C_SYNTAX_COMPOUND_STMT))
								.map(seq -> new LocatedList<>(
										seq.getLocation(),
										Collections.singletonList(new PlusCalLabeledStatements(
												seq.getLocation(),
												seq.getValue().getRest().getFirst(),
												seq.getValue().getFirst())))),
						C_SYNTAX_UNLABELEDSTMT.map(stmt -> new LocatedList<>(
								stmt.getLocation(), Collections.singletonList(stmt))),
						C_SYNTAX_COMPOUND_STMT)
		);

		C_SYNTAX_COMPOUND_STMT.setReferencedGrammar(
				emptySequence()
						.drop(parsePlusCalToken("{"))
						.part(parseListOf(C_SYNTAX_STMT, parsePlusCalToken(";")))
						.drop(parseOneOf(parsePlusCalToken(";"), nop()))
						.drop(parsePlusCalToken("}"))
						.map(seq -> new LocatedList<>(
								seq.getLocation(),
								seq.getValue().getFirst()
										.stream()
										.flatMap(Collection::stream)
										.collect(Collectors.toList())))
		);
	}

	private static final Grammar<LocatedList<TLAUnit>> C_SYNTAX_DEFINITIONS = emptySequence()
			.drop(parsePlusCalToken("define"))
			.drop(parsePlusCalToken("{"))
			.part(repeat(TLAParser.UNIT))
			.drop(parsePlusCalToken("}"))
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.map(seq -> seq.getValue().getFirst());

	private static final Grammar<ModularPlusCalArchetype> C_SYNTAX_ARCHETYPE = emptySequence()
			.drop(parsePlusCalToken("archetype"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(MPCAL_VAR_DECL, parsePlusCalToken(",")),
					nop().map(seq ->
							new LocatedList<ModularPlusCalVariableDeclaration>(
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
					parseListOf(MPCAL_VAR_DECL, parsePlusCalToken(",")),
					nop().map(seq -> new LocatedList<ModularPlusCalVariableDeclaration>(
							seq.getLocation(),
							Collections.emptyList()))))
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

	private static final Grammar<PlusCalMacro> C_SYNTAX_MACRO = emptySequence()
			.drop(parsePlusCalToken("macro"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(IDENTIFIER, parsePlusCalToken(",")),
					nop().map(v -> new LocatedList<Located<String>>(v.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken(")"))
			.part(C_SYNTAX_COMPOUND_STMT)
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.map(seq -> new PlusCalMacro(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getFirst().stream().map(Located::getValue).collect(Collectors.toList()),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalProcedure> C_SYNTAX_PROCEDURE = emptySequence()
			.drop(parsePlusCalToken("procedure"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(PVAR_DECL, parsePlusCalToken(",")),
					nop().map(v -> new LocatedList<PlusCalVariableDeclaration>(v.getLocation(), Collections.emptyList()))
			))
			.drop(parsePlusCalToken(")"))
			.part(parseOneOf(
					PVAR_DECLS,
					nop().map(v -> new LocatedList<PlusCalVariableDeclaration>(v.getLocation(), Collections.emptyList()))
			))
			.part(C_SYNTAX_COMPOUND_STMT)
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.map(seq -> new PlusCalProcedure(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst())
			);

	private static final Grammar<PlusCalProcess> C_SYNTAX_PROCESS = emptySequence()
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
			.part(parseOneOf(
					VAR_DECLS,
					nop().map(v -> new LocatedList<PlusCalVariableDeclaration>(
							v.getLocation(), Collections.emptyList()))))
			.part(C_SYNTAX_COMPOUND_STMT)
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.map(seq -> new PlusCalProcess(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalAlgorithm> C_SYNTAX_ALGORITHM = emptySequence()
			.part(parseOneOf(
					parsePlusCalToken("--algorithm").map(v -> new Located<>(
							v.getLocation(), PlusCalFairness.UNFAIR)),
					parsePlusCalToken("--fair algorithm").map(v -> new Located<>(
							v.getLocation(), PlusCalFairness.WEAK_FAIR))
			))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("{"))
			.part(parseOneOf(
					VAR_DECLS,
					nop().map(v -> new LocatedList<PlusCalVariableDeclaration>(
							v.getLocation(), Collections.emptyList()))))
			.part(parseOneOf(
					C_SYNTAX_DEFINITIONS,
					nop().map(v -> new LocatedList<TLAUnit>(
							v.getLocation(), Collections.emptyList()))))
			.part(repeat(C_SYNTAX_MACRO))
			.part(repeat(C_SYNTAX_PROCEDURE))
			.part(parseOneOf(
					C_SYNTAX_COMPOUND_STMT.map(stmts -> new PlusCalSingleProcess(stmts.getLocation(), stmts)),
					repeatOneOrMore(C_SYNTAX_PROCESS).map(procs -> new PlusCalMultiProcess(procs.getLocation(), procs))
			))
			.drop(parsePlusCalToken("}"))
			.map(seq -> new PlusCalAlgorithm(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getFirst(),
					seq.getValue().getFirst()));

	// P-syntax

	private static final ReferenceGrammar<PlusCalStatement> P_SYNTAX_STMT = new ReferenceGrammar<>();

	private static final ReferenceGrammar<LocatedList<PlusCalStatement>> P_SYNTAX_IF_ELSE = new ReferenceGrammar<>();
	static {
		P_SYNTAX_IF_ELSE.setReferencedGrammar(
				parseOneOf(
						emptySequence()
								.drop(parsePlusCalToken("elsif"))
								.part(TLA_EXPRESSION)
								.drop(parsePlusCalToken("then"))
								.part(repeatOneOrMore(P_SYNTAX_STMT))
								.part(P_SYNTAX_IF_ELSE)
								.map(seq -> new LocatedList<>(
										seq.getLocation(),
										Collections.singletonList(new PlusCalIf(
												seq.getLocation(),
												seq.getValue().getRest().getRest().getFirst(),
												seq.getValue().getRest().getFirst(),
												seq.getValue().getFirst())))),
						emptySequence()
								.drop(parsePlusCalToken("else"))
								.part(repeatOneOrMore(P_SYNTAX_STMT))
								.map(seq -> seq.getValue().getFirst()),
						nop().map(v -> new LocatedList<>(v.getLocation(), Collections.emptyList()))
				)
		);
	}

	private static final Grammar<PlusCalIf> P_SYNTAX_IF = emptySequence()
			.drop(parsePlusCalToken("if"))
			.part(TLA_EXPRESSION)
			.drop(parsePlusCalToken("then"))
			.part(repeatOneOrMore(P_SYNTAX_STMT))
			.part(P_SYNTAX_IF_ELSE)
			.drop(parsePlusCalToken("end"))
			.drop(parsePlusCalToken("if"))
			.map(seq -> new PlusCalIf(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalWhile> P_SYNTAX_WHILE = emptySequence()
			.drop(parsePlusCalToken("while"))
			.part(cut(TLA_EXPRESSION))
			.drop(parsePlusCalToken("do"))
			.part(cut(repeatOneOrMore(P_SYNTAX_STMT)))
			.drop(parsePlusCalToken("end"))
			.drop(parsePlusCalToken("while"))
			.map(seq -> new PlusCalWhile(
					seq.getLocation(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalEither> P_SYNTAX_EITHER = emptySequence()
			.drop(parsePlusCalToken("either"))
			.part(repeatOneOrMore(P_SYNTAX_STMT))
			.part(repeatOneOrMore(
					emptySequence()
							.drop(parsePlusCalToken("or"))
							.part(repeatOneOrMore(P_SYNTAX_STMT))
							.map(seq -> seq.getValue().getFirst())
			))
			.drop(parsePlusCalToken("end"))
			.drop(parsePlusCalToken("either"))
			.map(seq -> {
				List<List<PlusCalStatement>> branches = new ArrayList<>(seq.getValue().getFirst().size()+1);
				branches.add(seq.getValue().getRest().getFirst());
				branches.addAll(seq.getValue().getFirst());
				return new PlusCalEither(seq.getLocation(), branches);
			});

	private static final Grammar<PlusCalWith> P_SYNTAX_WITH = emptySequence()
			.drop(parsePlusCalToken("with"))
			.part(cut(parseListOf(VARIABLE_DECLARATION, parsePlusCalTokenOneOf(Arrays.asList(";", ",")))))
			.drop(parseOneOf(parsePlusCalToken(";"), parsePlusCalToken(","), nop())) // this separator is optional, unlike in the official grammar
			.drop(parsePlusCalToken("do"))
			.part(cut(repeatOneOrMore(P_SYNTAX_STMT)))
			.drop(parsePlusCalToken("end"))
			.drop(parsePlusCalToken("with"))
			.map(seq -> new PlusCalWith(
					seq.getLocation(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalStatement> P_SYNTAX_UNLABELEDSTMT = parseOneOf(
			ASSIGN,
			P_SYNTAX_IF,
			P_SYNTAX_WHILE,
			P_SYNTAX_EITHER,
			P_SYNTAX_WITH,
			AWAIT,
			PRINT,
			ASSERT,
			SKIP,
			RETURN,
			GOTO,
			CALL,
			MACRO_CALL
	);

	static {
		P_SYNTAX_STMT.setReferencedGrammar(
				parseOneOf(
						emptySequence()
								.part(emptySequence().part(IDENTIFIER)
										.drop(parsePlusCalToken(":"))
										.part(parseOneOf(
												parsePlusCalToken("+").map(v -> new Located<>(
														v.getLocation(), PlusCalLabel.Modifier.PLUS)),
												parsePlusCalToken("-").map(v -> new Located<>(
														v.getLocation(), PlusCalLabel.Modifier.MINUS)),
												nop().map(v -> new Located<>(
														v.getLocation(), PlusCalLabel.Modifier.NONE))
										))
										.map(seq -> new PlusCalLabel(
												seq.getLocation(),
												seq.getValue().getRest().getFirst().getValue(),
												seq.getValue().getFirst().getValue()))
								)
								.part(cut(parseListOf(P_SYNTAX_UNLABELEDSTMT, parsePlusCalToken(";")))) // catch repeated statements instead of parsing them as sibling node)
								.drop(parsePlusCalToken(";"))
								.map(seq -> new PlusCalLabeledStatements(
												seq.getLocation(),
												seq.getValue().getRest().getFirst(),
												seq.getValue().getFirst())),
						emptySequence()
								.part(P_SYNTAX_UNLABELEDSTMT)
								.drop(parsePlusCalToken(";"))
								.map(seq -> seq.getValue().getFirst()))
		);
	}

	private static final Grammar<LocatedList<TLAUnit>> P_SYNTAX_DEFINITIONS = emptySequence()
			.drop(parsePlusCalToken("define"))
			.part(cut(repeat(TLAParser.UNIT)))
			.drop(parsePlusCalToken("end"))
			.drop(parsePlusCalToken("define"))
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.map(seq -> seq.getValue().getFirst());

	private static final Grammar<PlusCalMacro> P_SYNTAX_MACRO = emptySequence()
			.drop(parsePlusCalToken("macro"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(IDENTIFIER, parsePlusCalToken(",")),
					nop().map(v -> new LocatedList<Located<String>>(v.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken(")"))
			.drop(parsePlusCalToken("begin"))
			.part(repeatOneOrMore(P_SYNTAX_STMT))
			.drop(parsePlusCalToken("end"))
			.drop(parsePlusCalToken("macro"))
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.map(seq -> new PlusCalMacro(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getFirst().stream().map(Located::getValue).collect(Collectors.toList()),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalProcedure> P_SYNTAX_PROCEDURE = emptySequence()
			.drop(parsePlusCalToken("procedure"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(PVAR_DECL, parsePlusCalToken(",")),
					nop().map(v -> new LocatedList<PlusCalVariableDeclaration>(v.getLocation(), Collections.emptyList()))
			))
			.drop(parsePlusCalToken(")"))
			.part(parseOneOf(
					PVAR_DECLS,
					nop().map(v -> new LocatedList<PlusCalVariableDeclaration>(v.getLocation(), Collections.emptyList()))
			))
			.drop(parsePlusCalToken("begin"))
			.part(repeatOneOrMore(P_SYNTAX_STMT))
			.drop(parsePlusCalToken("end"))
			.drop(parsePlusCalToken("procedure"))
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.map(seq -> new PlusCalProcedure(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalProcess> P_SYNTAX_PROCESS = emptySequence()
			.part(parseOneOf(
					emptySequence()
							.drop(parsePlusCalToken("fair"))
							.drop(parsePlusCalToken("+"))
							.map(seq -> new Located<>(seq.getLocation(), PlusCalFairness.STRONG_FAIR)),
					parsePlusCalToken("fair").map(s -> new Located<>(s.getLocation(), PlusCalFairness.WEAK_FAIR)),
					nop().map(v -> new Located<>(v.getLocation(), PlusCalFairness.UNFAIR))
			))
			.drop(parsePlusCalToken("process"))
			.part(VARIABLE_DECLARATION)
			.part(parseOneOf(
					VAR_DECLS,
					nop().map(v -> new LocatedList<PlusCalVariableDeclaration>(
							v.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken("begin"))
			.part(repeatOneOrMore(P_SYNTAX_STMT))
			.drop(parsePlusCalToken("end"))
			.drop(parsePlusCalToken("process"))
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.map(seq -> new PlusCalProcess(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<PlusCalAlgorithm> P_SYNTAX_ALGORITHM = emptySequence()
			.part(parseOneOf(
					parsePlusCalToken("--algorithm").map(v -> new Located<>(
							v.getLocation(), PlusCalFairness.UNFAIR)),
					parsePlusCalToken("--fair algorithm").map(v -> new Located<>(
							v.getLocation(), PlusCalFairness.WEAK_FAIR))
			))
			.part(IDENTIFIER)
			.drop(reject(parsePlusCalToken("{")))
			.part(parseOneOf(
					VAR_DECLS,
					nop().map(v -> new LocatedList<PlusCalVariableDeclaration>(
							v.getLocation(), Collections.emptyList()))))
			.part(parseOneOf(
					P_SYNTAX_DEFINITIONS,
					nop().map(v -> new LocatedList<TLAUnit>(
							v.getLocation(), Collections.emptyList()))))
			.part(repeat(P_SYNTAX_MACRO))
			.part(repeat(P_SYNTAX_PROCEDURE))
			.part(parseOneOf(
					emptySequence()
							.drop(parsePlusCalToken("begin"))
							.part(repeatOneOrMore(P_SYNTAX_STMT))
							.map(seq -> new PlusCalSingleProcess(seq.getLocation(), seq.getValue().getFirst())),
					repeatOneOrMore(P_SYNTAX_PROCESS).map(procs -> new PlusCalMultiProcess(procs.getLocation(), procs))
			))
			.drop(parsePlusCalToken("end"))
			.drop(parsePlusCalToken("algorithm"))
			.map(seq -> new PlusCalAlgorithm(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getFirst(),
					seq.getValue().getFirst()));

	// main

	private static final Grammar<PlusCalAlgorithm> ALGORITHM = emptySequence()
			.drop(matchPattern(PCAL_FIND_ALGORITHM))
			.part(parseOneOf(P_SYNTAX_ALGORITHM, C_SYNTAX_ALGORITHM))
			.drop(matchPattern(PCAL_AFTER_ALGORITHM))
			.map(seq -> seq.getValue().getFirst());

	// public interface

	public static PlusCalAlgorithm readAlgorithm(LexicalContext ctx) throws ParseFailureException {
		return readOrExcept(ctx, ALGORITHM);
	}

	// testing interface

	static ModularPlusCalUnit readModularPlusCalUnit(LexicalContext ctx) throws ParseFailureException {
		return readOrExcept(ctx, parseOneOf(C_SYNTAX_ARCHETYPE, C_SYNTAX_INSTANCE));
	}
}
