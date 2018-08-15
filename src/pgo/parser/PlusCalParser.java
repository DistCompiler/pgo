package pgo.parser;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.*;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.regex.Pattern;

import static pgo.parser.ParseTools.*;
import static pgo.parser.TLAParser.*;

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
	public static Grammar<Located<Void>> parsePlusCalToken(String t){
		return emptySequence()
				.drop(skipWhitespaceAndTLAComments())
				.part(matchString(t))
				.map(seq -> seq.getValue().getFirst());
	}

	/**
	 * Creates a parse action that accepts any of the string in options, skipping any preceding comments or whitespace.
	 * @param options a list of token values to accept
	 * @return the parse action, yielding which token was accepted
	 */
	public static Grammar<Located<String>> parsePlusCalTokenOneOf(List<String> options){
		return emptySequence()
				.drop(skipWhitespaceAndTLAComments())
				.part(matchStringOneOf(options))
				.map(seq -> seq.getValue().getFirst());
	}

	/**
	 * Creates a parse action that accepts a PlusCal identifier (identical to a TLA+ identifier, but with a more
	 * convenient return type).
	 * @return the parse action
	 */
	public static Grammar<Located<String>> parsePlusCalIdentifier(){
		return emptySequence()
				.drop(skipWhitespaceAndTLAComments())
				.part(matchTLAIdentifier())
				.map(seq -> seq.getValue().getFirst());
	}

	private enum SyntaxVariant {
		P_SYNTAX,
		C_SYNTAX,
	}

	public static final ReferenceGrammar<PlusCalStatement> UNLABELED_STATEMENT_C_SYNTAX = new ReferenceGrammar<>();
	public static final ReferenceGrammar<PlusCalStatement> UNLABELED_STATEMENT_P_SYNTAX = new ReferenceGrammar<>();
	/*static {
		UNLABELED_STATEMENT_C_SYNTAX.setReferencedGrammar(
				parseOneOf(
						//parseIfStatement(syntax),
						//parseEitherStatement(syntax),
						//parseWhileStatement(syntax),
						parseCSyntaxWhileStatement(),
						parseAwaitStatement(),
						//parseWithStatement(syntax),
						parseSkipStatement(),
						parsePrintStatement(),
						parseAssertStatement(),
						parseCallStatement(),
						parseReturnStatement(),
						parseGotoStatement(),
						parseAssignmentStatement()
				).compile());
		UNLABELED_STATEMENT_P_SYNTAX.setReferencedGrammar(
				parseOneOf(
						//parseIfStatement(syntax),
						//parseEitherStatement(syntax),
						//parseWhileStatement(syntax),
						parseAwaitStatement(),
						//parseWithStatement(syntax),
						parseSkipStatement(),
						parsePrintStatement(),
						parseAssertStatement(),
						parseCallStatement(),
						parseReturnStatement(),
						parseGotoStatement(),
						parseAssignmentStatement()
				).compile());
	}*/

	/*static Grammar<LocatedList<PlusCalStatement>> parseUnlabeledStatement(SyntaxVariant syntax, Grammar<LocatedList<PlusCalStatement>> tail) {
		Variable<PlusCalStatement> stmt = new Variable<>("stmt");
		Variable<LocatedList<PlusCalStatement>> rest = new Variable<>("rest");
		return sequence(
				part(stmt, syntax == SyntaxVariant.C_SYNTAX ? UNLABELED_STATEMENT_C_SYNTAX : UNLABELED_STATEMENT_P_SYNTAX),
				part(rest, tail)
		).map(seqResult -> {
			LocatedList<PlusCalStatement> lst = new LocatedList<>(seqResult.getLocation(), new ArrayList<>());
			lst.add(seqResult.get(stmt));
			lst.addAll(seqResult.get(rest));
			return lst;
		});
	}

	static <AST extends SourceLocatable> Grammar<LocatedList<AST>> parseCommaList(Grammar<AST> element){
		return parseListOf(element, parsePlusCalToken(","));
	}

	static Grammar<Located<Void>> parseEnd(Grammar<Located<Void>> thing){
		return sequence(
				drop(parsePlusCalToken("end")),
				drop(thing)
		).map(seq -> new Located<>(seq.getLocation(), null));
	}

	static <Result extends SourceLocatable> Grammar<Result> parseBracketed(SyntaxVariant syntax, Grammar<Result> action){
		switch(syntax){
			case P_SYNTAX:
				return action;
			case C_SYNTAX:
				Variable<Result> result = new Variable<>("result");
				return sequence(
						drop(parsePlusCalToken("(")),
						part(result, action),
						drop(parsePlusCalToken(")"))
				).map(seq -> seq.get(result));
		}
		throw new Unreachable();
	}

	static Grammar<PlusCalVariableDeclaration> parseVariableDeclaration(){
		Variable<Located<String>> id = new Variable<>("id");
		Variable<Located<Boolean>> isSet = new Variable<>("isSet");
		Variable<TLAExpression> expression = new Variable<>("expression");
		return sequence(
				part(id, parsePlusCalIdentifier()),
				part(expression, parseOneOf(
						sequence(
								part(isSet, parsePlusCalToken("=").map(v ->
										new Located<>(v.getLocation(), false))),
								part(expression, parseExpression())
						).map(seq -> seq.get(expression)),
						sequence(
								part(isSet, parsePlusCalToken("\\in").map(v ->
										new Located<>(v.getLocation(), true))),
								part(expression, parseExpression())
						).map(seq -> seq.get(expression)),
						nop().map(v -> new PlusCalDefaultInitValue(v.getLocation()))
				))
		).map(seq -> new PlusCalVariableDeclaration(
				seq.getLocation(), seq.get(id), seq.get(isSet).getValue(), seq.get(expression)));
	}

	static Grammar<LocatedList<PlusCalVariableDeclaration>> parseVariablesDeclaration(){
		Variable<LocatedList<PlusCalVariableDeclaration>> variables = new Variable<>("variables");
		return sequence(
				drop(parsePlusCalTokenOneOf(Arrays.asList("variables", "variable"))),
				part(variables, parseListOf(parseVariableDeclaration(), parsePlusCalToken(";"))),
				drop(parsePlusCalToken(";"))
		).map(seq -> new LocatedList<>(seq.getLocation(), seq.get(variables)));
	}

	static Grammar<PlusCalLabel> parseLabel(){
		Variable<Located<String>> labelName = new Variable<>("labelName");
		Variable<Located<PlusCalLabel.Modifier>> fairness = new Variable<>("fairness");
		return sequence(
				part(labelName, parsePlusCalIdentifier()),
				drop(parsePlusCalToken(":")),
				part(fairness, parseOneOf(
						parsePlusCalToken("+").map(v -> new Located<>(v.getLocation(), PlusCalLabel.Modifier.PLUS)),
						parsePlusCalToken("-").map(v -> new Located<>(v.getLocation(), PlusCalLabel.Modifier.MINUS)),
						nop().map(v -> new Located<>(v.getLocation(), PlusCalLabel.Modifier.NONE))
				))
		).map(seq -> new PlusCalLabel(seq.getLocation(), seq.get(labelName).getValue(), seq.get(fairness).getValue()));
	}

	static Grammar<PlusCalStatement> parseUnlabeledPlusCalStatement(SyntaxVariant syntax) {
		return parseOneOf(
				//parseIfStatement(syntax),
				//parseEitherStatement(syntax),
				//parseWhileStatement(syntax),
				parseAwaitStatement(),
				//parseWithStatement(syntax),
				parseSkipStatement(),
				parsePrintStatement(),
				parseAssertStatement(),
				parseCallStatement(),
				parseReturnStatement(),
				parseGotoStatement(),
				parseAssignmentStatement()
		);
	}

	static Grammar<LocatedList<PlusCalStatement>> parseUnlabeledCSyntaxStatementList() {

		ReferenceGrammar<LocatedList<PlusCalStatement>> matchStatement = new ReferenceGrammar<>();
		ReferenceGrammar<LocatedList<PlusCalStatement>> matchBlock = new ReferenceGrammar<>();

		matchStatement.setReferencedGrammar(scope(() -> {
			Variable<PlusCalStatement> stmt = new Variable<>("stmt");
			Variable<LocatedList<PlusCalStatement>> rest = new Variable<>("rest");
			return sequence(
					part(stmt, parseUnlabeledPlusCalStatement(SyntaxVariant.C_SYNTAX)),
					part(rest, parseOneOf(
							sequence(
									parsePlusCalToken(";"),
									part(rest, parseOneOf(
											matchStatement,
											matchBlock,
											nop().map(v ->
													new LocatedList<>(v.getLocation(), Collections.emptyList()))
									))
							).map(seqResult -> seqResult.get(rest)),
							nop().map(v -> new LocatedList<>(v.getLocation(), Collections.emptyList()))
					))
			).map(seqResult -> {
				LocatedList<PlusCalStatement> lst = new LocatedList<>(seqResult.getLocation(), new ArrayList<>());
				lst.add(seqResult.get(stmt));
				lst.addAll(seqResult.get(rest));
				return lst;
			});
		}).compile());

		matchBlock.setReferencedGrammar(scope(() -> {
			Variable<LocatedList<PlusCalStatement>> blockStatements = new Variable<>("blockStatements");
			Variable<LocatedList<PlusCalStatement>> rest = new Variable<>("rest");
			return sequence(
					parsePlusCalToken("{"),
					part(blockStatements, parseOneOf(matchBlock, matchStatement)),
					parsePlusCalToken("}"),
					part(rest, parseOneOf(
							scope(() -> {
								Variable<LocatedList<PlusCalStatement>> rest2 = new Variable<>("rest2");
								return sequence(
										parsePlusCalToken(";"),
										part(rest2, parseOneOf(
												matchBlock,
												matchStatement,
												nop().map(v ->
														new LocatedList<>(v.getLocation(), Collections.emptyList()))
										))
								).map(seqResult -> seqResult.get(rest2));
							}),
							matchBlock,
							nop().map(v -> new LocatedList<>(v.getLocation(), Collections.emptyList()))
					))
			).map(seqResult -> {
				LocatedList<PlusCalStatement> result = new LocatedList<>(seqResult.getLocation(), new ArrayList<>());
				result.addAll(seqResult.get(blockStatements));
				result.addAll(seqResult.get(rest));
				return result;
			});
		}).compile());

		return parseOneOf(
				matchStatement,
				matchBlock
		);
	}

	static Grammar<LocatedList<PlusCalStatement>> parseUnlabeledCSyntaxClause(Grammar<Located<Void>> delimiter) {
		return parseOneOf(
				scope(() -> {
					Variable<LocatedList<PlusCalStatement>> blockStmts = new Variable<>("blockStmts");
					return sequence(
							parsePlusCalToken("{"),
							part(blockStmts, parseUnlabeledCSyntaxStatementList()),
							parsePlusCalToken("}"),
							delimiter
					).map(seqResult -> seqResult.get(blockStmts));
				}),
				scope(() -> {
					Variable<PlusCalStatement> stmt = new Variable<>("stmt");
					return sequence(
							part(stmt, parseUnlabeledPlusCalStatement(SyntaxVariant.C_SYNTAX)),
							delimiter
					).map(seqResult -> {
						PlusCalStatement stmtV = seqResult.get(stmt);
						return new LocatedList<>(stmtV.getLocation(), Collections.singletonList(stmtV));
					});
				})
		);
	}

	static Grammar<LocatedList<PlusCalStatement>> parseUnlabeledPSyntaxStatementList() {
		Variable<LocatedList<PlusCalStatement>> stmts = new Variable<>("stmts");
		return sequence(
				part(stmts, parseListOf(
						parseUnlabeledPlusCalStatement(SyntaxVariant.P_SYNTAX),
						parsePlusCalToken(";"))),
				parseOneOf(parsePlusCalToken(";"), nop())
		).map(seqResult -> seqResult.get(stmts));
	}


	static Grammar<PlusCalLabeledStatements> parseLabeledStatements(SyntaxVariant syntax){
		Variable<PlusCalLabel> label = new Variable<>("label");
		Variable<LocatedList<PlusCalStatement>> statements = new Variable<>("statements");
		return sequence(
				part(label, parseLabel()),
				part(statements, syntax == SyntaxVariant.C_SYNTAX ?
						parseUnlabeledCSyntaxStatementList()
						: parseUnlabeledPSyntaxStatementList())
		).map(seq -> new PlusCalLabeledStatements(seq.getLocation(), seq.get(label), seq.get(statements)));
	}*/

	/*static Grammar<PlusCalIf> parseElsifPart(){
		Variable<TLAExpression> condition = new Variable<>("condition");
		Variable<LocatedList<PlusCalStatement>> thenStatements = new Variable<>("thenStatements");
		Variable<LocatedList<PlusCalStatement>> elseStatements = new Variable<>("elseStatements");
		return sequence(
				drop(parsePlusCalToken("elsif")),
				part(condition, parseExpression()),
				drop(parsePlusCalToken("then")),
				part(thenStatements, parseStatementList(SyntaxVariant.P_SYNTAX)),
				part(elseStatements, parseOneOf(
						sequence(
								drop(parsePlusCalToken("else")),
								part(elseStatements, parseStatementList(SyntaxVariant.P_SYNTAX))
						).map(seq -> seq.get(elseStatements)),
						parseElsifPart().map(f ->
								new LocatedList<>(f.getLocation(), Collections.singletonList(f))),
						nop().map(v ->
								new LocatedList<>(v.getLocation(), Collections.singletonList(new PlusCalSkip(v.getLocation()))))
				))
		).map(seq -> new PlusCalIf(
				seq.getLocation(), seq.get(condition), seq.get(thenStatements), seq.get(elseStatements)));
	}*/

	/*static Grammar<PlusCalIf> parseIfStatement(SyntaxVariant syntax){
		Variable<TLAExpression> condition = new Variable<>("condition");
		Variable<LocatedList<PlusCalStatement>> thenStatements = new Variable<>("thenStatements");
		Variable<LocatedList<PlusCalStatement>> elseStatements = new Variable<>("elseStatements");
		switch(syntax){
			case P_SYNTAX:
				return sequence(
						drop(parsePlusCalToken("if")),
						part(condition, parseExpression()),
						drop(parsePlusCalToken("then")),
						part(thenStatements, parseStatementList(syntax)),
						part(elseStatements, parseOneOf(
								parseElsifPart().map(f -> new LocatedList<>(
										f.getLocation(), Collections.singletonList(f))),
								sequence(
										drop(parsePlusCalToken("else")),
										part(elseStatements, parseStatementList(syntax))
								).map(seq -> seq.get(elseStatements)),
								nop().map(v -> new LocatedList<>(
										v.getLocation(), Collections.singletonList(new PlusCalSkip(v.getLocation()))))
						)),
						drop(sequence(
								drop(parsePlusCalToken("end")),
								drop(parsePlusCalToken("if"))
						))
				).map(seq -> new PlusCalIf(
						seq.getLocation(), seq.get(condition), seq.get(thenStatements),
						seq.get(elseStatements)));
			case C_SYNTAX:
				return sequence(
						drop(parsePlusCalToken("if")),
						drop(parsePlusCalToken("(")),
						part(condition, parseExpression()),
						drop(parsePlusCalToken(")")),
						part(thenStatements, parseStatementList(syntax)),
						part(elseStatements, parseOneOf(
								sequence(
										drop(parsePlusCalToken("else")),
										part(elseStatements, parseStatementList(syntax))
								).map(seq -> seq.get(elseStatements)),
								nop().map(v -> new LocatedList<>(
										v.getLocation(), Collections.singletonList(new PlusCalSkip(v.getLocation()))))
						))
				).map(seq -> new PlusCalIf(
						seq.getLocation(), seq.get(condition), seq.get(thenStatements), seq.get(elseStatements)));
			default:
				throw new Unreachable();
		}
	}*/

	/*static Grammar<PlusCalEither> parseEitherStatement(SyntaxVariant syntax){
		Variable<LocatedList<PlusCalStatement>> firstClause = new Variable<>("firstClause");
		Variable<LocatedList<PlusCalStatement>> tmpClause = new Variable<>("tmpClause");
 		Variable<LocatedList<LocatedList<PlusCalStatement>>> restClauses = new Variable<>("restClauses");
		return sequence(
				drop(parsePlusCalToken("either")),
				part(firstClause, parseStatementList(syntax)),
				part(restClauses, repeat(
						sequence(
							drop(parsePlusCalToken("or")),
							part(tmpClause, parseStatementList(syntax))
						).map(seq -> seq.get(tmpClause)))),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parseEnd(parsePlusCalToken("either")))
		).map(seq -> {
			List<List<PlusCalStatement>> clauses = new ArrayList<>();
			clauses.add(seq.get(firstClause));
			clauses.addAll(seq.get(restClauses));
			return new PlusCalEither(seq.getLocation(), clauses);
		});
	}*/

	/*static Grammar<PlusCalWhile> parseWhileStatement(SyntaxVariant syntax){
		Variable<TLAExpression> condition = new Variable<>("condition");
		Variable<LocatedList<PlusCalStatement>> body = new Variable<>("body");
		return sequence(
				drop(parsePlusCalToken("while")),
				part(condition, parseBracketed(syntax, parseExpression())),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parsePlusCalToken("do")),
				part(body, parseStatementList(syntax)),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parseEnd(parsePlusCalToken("while")))
		).map(seq -> new PlusCalWhile(seq.getLocation(), seq.get(condition), seq.get(body)));
	}*/

	/*static Grammar<PlusCalAwait> parseAwaitStatement(){
		Variable<TLAExpression> condition = new Variable<>("condition");
		return sequence(
				drop(parsePlusCalTokenOneOf(Arrays.asList("await", "when"))),
				part(condition, parseExpression())
		).map(seq -> new PlusCalAwait(seq.getLocation(), seq.get(condition)));
	}*/

	/*static Grammar<PlusCalWith> parseWithStatement(SyntaxVariant syntax){
		Variable<LocatedList<PlusCalVariableDeclaration>> decls = new Variable<>("decls");
		Variable<LocatedList<PlusCalStatement>> body = new Variable<>("body");
		return sequence(
				drop(parsePlusCalToken("with")),
				part(decls, parseBracketed(
						syntax,
						parseListOf(parseVariableDeclaration(), parsePlusCalToken(";")))),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parsePlusCalToken("do")),
				part(body, parseStatementList(syntax)),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parseEnd(parsePlusCalToken("with")))
		).map(seq -> {
			// navigate through the list of bindings in reverse to produce the proper recursive structure
			// of single-binding AST nodes
			LocatedList<PlusCalVariableDeclaration> ds = seq.get(decls);
			PlusCalWith with = new PlusCalWith(
					ds.get(ds.size()-1).getLocation().combine(seq.get(body).getLocation()),
					ds.get(ds.size()-1), seq.get(body));
			for(int i = ds.size() - 2; i >= 0; --i){
				with = new PlusCalWith(ds.get(i).getLocation(), ds.get(i), Collections.singletonList(with));
			}
			return with;
		});
	}*/

	/*static Grammar<PlusCalSkip> parseSkipStatement(){
		return parsePlusCalToken("skip")
				.map(seq -> new PlusCalSkip(seq.getLocation()));
	}

	static Grammar<PlusCalPrint> parsePrintStatement(){
		Variable<TLAExpression> value = new Variable<>("value");
		return sequence(
				drop(parsePlusCalToken("print")),
				part(value, parseExpression())
		).map(seq -> new PlusCalPrint(seq.getLocation(), seq.get(value)));
	}

	static Grammar<PlusCalAssert> parseAssertStatement(){
		Variable<TLAExpression> condition = new Variable<>("condition");
		return sequence(
				drop(parsePlusCalToken("assert")),
				part(condition, parseExpression())
		).map(seq -> new PlusCalAssert(seq.getLocation(), seq.get(condition)));
	}

	static Grammar<PlusCalCall> parseCallStatement(){
		Variable<Located<String>> target = new Variable<>("target");
		Variable<LocatedList<TLAExpression>> arguments = new Variable<>("arguments");
		return sequence(
				drop(parsePlusCalToken("call")),
				part(target, parsePlusCalIdentifier()),
				drop(parsePlusCalToken("(")),
				part(arguments, parseCommaList(parseExpression())),
				drop(parsePlusCalToken(")"))
		).map(seq -> new PlusCalCall(seq.getLocation(), seq.get(target).getValue(), seq.get(arguments)));
	}
	
	static Grammar<PlusCalReturn> parseReturnStatement(){
		return parsePlusCalToken("return")
				.map(seq -> new PlusCalReturn(seq.getLocation()));
	}
	
	static Grammar<PlusCalGoto> parseGotoStatement(){
		Variable<Located<String>> target = new Variable<>("target");
		return sequence(
				drop(parsePlusCalToken("goto")),
				part(target, parsePlusCalIdentifier())
		).map(seq -> new PlusCalGoto(seq.getLocation(), seq.get(target).getValue()));
	}

	static Grammar<PlusCalAssignmentPair> parseAssignmentPair(){
		Variable<TLAExpression> lhs = new Variable<>("lhs");
		Variable<TLAExpression> rhs = new Variable<>("rhs");
		return sequence(
				part(lhs, parseExpression()),
				drop(parsePlusCalToken(":=")),
				part(rhs, parseExpression())
		).map(seq -> new PlusCalAssignmentPair(seq.getLocation(), seq.get(lhs), seq.get(rhs)));
	}

	static Grammar<PlusCalAssignment> parseAssignmentStatement(){
		return parseListOf(parseAssignmentPair(), parsePlusCalToken("||"))
				.map(seq -> new PlusCalAssignment(seq.getLocation(), seq));
	}

	static Grammar<PlusCalStatement> parseStatement(SyntaxVariant syntax){
		return parseOneOf(
				parseLabeledStatements(syntax),
				//parseIfStatement(syntax),
				//parseEitherStatement(syntax),
				//parseWhileStatement(syntax),
				parseAwaitStatement(),
				//parseWithStatement(syntax),
				parseSkipStatement(),
				parsePrintStatement(),
				parseAssertStatement(),
				parseCallStatement(),
				parseReturnStatement(),
				parseGotoStatement(),
				parseAssignmentStatement()
		);
	}*/

	/*static Grammar<PlusCalSingleProcess> parseSingleProcess(SyntaxVariant syntax){
		Variable<LocatedList<PlusCalLabeledStatements>> labeledStatements = new Variable<>("labeledStatements");
		return sequence(
				drop(parseBlockBegin(syntax, parsePlusCalToken("begin"))),
				part(labeledStatements, repeat(parseLabeledStatements(syntax)))
		).map(seq -> new PlusCalSingleProcess(seq.getLocation(), seq.get(labeledStatements)));
	}*/

	/*static Grammar<PlusCalProcess> parseProcess(SyntaxVariant syntax){
		Variable<Located<PlusCalFairness>> fairness = new Variable<>("fairness");
		Variable<PlusCalVariableDeclaration> name = new Variable<>("name");
		Variable<LocatedList<PlusCalVariableDeclaration>> variables = new Variable<>("variables");
		Variable<LocatedList<PlusCalLabeledStatements>> labeledStatements = new Variable<>("labeledStatements");
		return sequence(
				part(fairness, parseOneOf(
				)),
				drop(parsePlusCalToken("process")),
				part(name, parseBracketed(syntax, parseVariableDeclaration())),
				part(variables, parseVariablesDeclaration()),
				drop(parseBlockBegin(syntax, parsePlusCalToken("begin"))),
				part(labeledStatements, parseListOf(parseLabeledStatements(syntax), parsePlusCalToken(";"))),
				drop(parseOneOf(parsePlusCalToken(";"), nop())),
				drop(parseBlockEnd(syntax, parseEnd(parsePlusCalToken("process"))))
		).map(seq -> new PlusCalProcess(
				seq.getLocation(), seq.get(name), seq.get(fairness).getValue(), seq.get(variables),
				seq.get(labeledStatements)));
	}*/

	/*static Grammar<PlusCalMultiProcess> parseMultiProcess(SyntaxVariant syntax){
		return repeat(parseProcess(syntax)).map(procs -> new PlusCalMultiProcess(procs.getLocation(), procs));
	}*/

	/*static Grammar<LocatedList<PlusCalStatement>> parseCSyntaxMinStatements() {
		return parseOneOf(
				C_SYNTAX_STATEMENT.map(stmt ->
						new LocatedList<>(stmt.getLocation(), Collections.singletonList(stmt))),
				parseCSyntaxBlock()
		);
	}

	static Grammar<LocatedList<PlusCalStatement>> parseCSyntaxBlock() {
		Variable<LocatedList<PlusCalStatement>> body = new Variable<>("body");
		Variable<LocatedList<PlusCalLabeledStatements>> labeled = new Variable<>("labeled");
		return sequence(
				parsePlusCalToken("{"),
				part(body, C_SYNTAX_STATEMENTS),
				// this allows us to catch labels inside blocks. semantically there is no such thing but this
				// keeps the grammar context-free
				part(labeled, parseOneOf(
						scope(() -> {
							Variable<LocatedList<PlusCalLabeledStatements>> tmp = new Variable<>("tmp");
							return sequence(
									parsePlusCalToken(";"),
									part(tmp, parseListOf(parseCSyntaxLabeledStatements(), parsePlusCalToken(";")))
							).map(seqResult -> seqResult.get(tmp));
						}),
						nop().map(v -> new LocatedList<>(v.getLocation(), Collections.emptyList()))
				)),
				parseOneOf(
						parsePlusCalToken("}"),
						drop(sequence(parsePlusCalToken(";"), parsePlusCalToken("}")))
				)
		).map(seqResult -> {
			LocatedList<PlusCalStatement> result = new LocatedList<>(seqResult.getLocation(), new ArrayList<>());
			result.addAll(seqResult.get(body));
			result.addAll(seqResult.get(labeled));
			return result;
		});
	}

	static Grammar<PlusCalStatement> parseCSyntaxIfStatement() {
		Variable<TLAExpression> cond = new Variable<>("cond");
		Variable<LocatedList<PlusCalStatement>> whenTrue = new Variable<>("whenTrue");
		Variable<LocatedList<PlusCalStatement>> whenFalse = new Variable<>("whenFalse");
		return sequence(
				parsePlusCalToken("if"),
				parsePlusCalToken("("),
				part(cond, parseExpression()),
				parsePlusCalToken(")"),
				part(whenTrue, parseCSyntaxMinStatements()),
				part(whenFalse, parseOneOf(
						sequence(
								parseOneOf(
										drop(sequence(parsePlusCalToken(";"), parsePlusCalToken("else"))),
										parsePlusCalToken("else")
								),
								part(whenFalse, parseCSyntaxMinStatements())
						).map(seqResult -> seqResult.get(whenFalse)),
						nop().map(v -> new LocatedList<>(v.getLocation(), Collections.emptyList()))
				))
		).map(seqResult ->
				new PlusCalIf(
						seqResult.getLocation(), seqResult.get(cond), seqResult.get(whenTrue),
						seqResult.get(whenFalse)));
	}

	static Grammar<PlusCalStatement> parseCSyntaxWhileStatement() {
		Variable<TLAExpression> cond = new Variable<>("cond");
		Variable<LocatedList<PlusCalStatement>> body = new Variable<>("body");

		return sequence(
				parsePlusCalToken("while"),
				parsePlusCalToken("("),
				part(cond, parseExpression()),
				parsePlusCalToken(")"),
				part(body, parseCSyntaxMinStatements())
		).map(seqResult -> new PlusCalWhile(seqResult.getLocation(), seqResult.get(cond), seqResult.get(body)));
	}

	private static final ReferenceGrammar<PlusCalStatement> C_SYNTAX_STATEMENT = new ReferenceGrammar<>();
	static final ReferenceGrammar<LocatedList<PlusCalStatement>> C_SYNTAX_STATEMENTS = new ReferenceGrammar<>();

	static {
		C_SYNTAX_STATEMENT.setReferencedGrammar(
				parseOneOf(
						parseCSyntaxIfStatement(),
						//parseEitherStatement(syntax),
						parseCSyntaxWhileStatement(),
						parseAwaitStatement(),
						//parseWithStatement(syntax),
						parseSkipStatement(),
						parsePrintStatement(),
						parseAssertStatement(),
						parseCallStatement(),
						parseReturnStatement(),
						parseGotoStatement(),
						parseAssignmentStatement()
				).map(stmt -> {
					System.out.println("statement "+stmt);
					return stmt;
				}).compile()
		);
	}

	static {
		ReferenceGrammar<LocatedList<PlusCalStatement>> restGrammar = new ReferenceGrammar<>();

		restGrammar.setReferencedGrammar(
				scope(() -> {
					Variable<LocatedList<PlusCalStatement>> currentPart = new Variable<>("currentPart");
					Variable<LocatedList<PlusCalStatement>> restPart = new Variable<>("restPart");
					Function<ParseInfo<Located<Void>>, LocatedList<PlusCalStatement>> aggregator = seqResult -> {
						LocatedList<PlusCalStatement> result = new LocatedList<>(
								seqResult.getLocation(), new ArrayList<>());
						result.addAll(seqResult.get(currentPart));
						result.addAll(seqResult.get(restPart));
						return result;
					};

					return ParseTools.<LocatedList<PlusCalStatement>>parseOneOf(
							sequence(
									part(currentPart, parseCSyntaxBlock()),
									part(restPart, restGrammar)
							).map(aggregator),
							sequence(
									parsePlusCalToken(";"),
									part(currentPart, C_SYNTAX_STATEMENT
											.map(stmt -> new LocatedList<>(
													stmt.getLocation(), Collections.singletonList(stmt)))),
									part(restPart, restGrammar)
							).map(aggregator),
							nop().map(v -> new LocatedList<>(v.getLocation(), Collections.emptyList()))
					);
				}).compile()
		);

		Variable<LocatedList<PlusCalStatement>> first = new Variable<>("first");
		Variable<LocatedList<PlusCalStatement>> rest = new Variable<>("rest");
		C_SYNTAX_STATEMENTS.setReferencedGrammar(
				sequence(
						part(first, parseOneOf(
								C_SYNTAX_STATEMENT
										.map(stmt -> new LocatedList<>(stmt.getLocation(), Collections.singletonList(stmt))),
								parseCSyntaxBlock()
						)),
						part(rest, restGrammar)
				).map(seqResult -> {
					LocatedList<PlusCalStatement> result = new LocatedList<>(seqResult.getLocation(), new ArrayList<>());
					result.addAll(seqResult.get(first));
					result.addAll(seqResult.get(rest));
					return result;
				}).compile()
		);
	}

	static Grammar<PlusCalLabeledStatements> parseCSyntaxLabeledStatements() {
		Variable<PlusCalLabel> label = new Variable<>("label");
		Variable<LocatedList<PlusCalStatement>> statements = new Variable<>("statements");
		return sequence(
				part(label, parseLabel()),
				part(statements, C_SYNTAX_STATEMENTS)
		).map(seqResult -> new PlusCalLabeledStatements(
				seqResult.getLocation(), seqResult.get(label), seqResult.get(statements)));
	}

	static Grammar<LocatedList<PlusCalLabeledStatements>> parseCSyntaxProcessBody() {
		Variable<LocatedList<PlusCalLabeledStatements>> labeledStmts = new Variable<>("labeledStmts");
		return sequence(
				parsePlusCalToken("{"),
				part(labeledStmts, parseListOf(parseCSyntaxLabeledStatements(), parsePlusCalToken(";"))),
				parseOneOf(
						parsePlusCalToken("}"),
						drop(sequence(parsePlusCalToken(";"), parsePlusCalToken("}")))
				)
		).map(seqResult -> seqResult.get(labeledStmts));
	}

	static Grammar<PlusCalSingleProcess> parseCSyntaxSingleProcess(){
		return parseCSyntaxProcessBody()
				.map(stmts -> new PlusCalSingleProcess(stmts.getLocation(), stmts));
	}

	static Grammar<PlusCalProcesses> parseCSyntaxProcesses(){
		return parseOneOf(
				parseCSyntaxSingleProcess()
		);
	}

	static Grammar<PlusCalAlgorithm> parseCSyntaxAlgorithm(){
		Variable<Located<String>> name = new Variable<>("name");
		Variable<LocatedList<PlusCalVariableDeclaration>> variables = new Variable<>("variables");
		Variable<PlusCalProcesses> processes = new Variable<>("processes");
		return sequence(
				drop(parsePlusCalToken("--algorithm")),
				part(name, parsePlusCalIdentifier()),
				parsePlusCalToken("{"),
				part(variables, parseVariablesDeclaration()),
				part(processes, parseCSyntaxProcesses()),
				parsePlusCalToken("}")
		).map(seq -> new PlusCalAlgorithm(seq.getLocation().combine(seq.getLocation()), seq.get(name),
				seq.get(variables), Collections.emptyList(), Collections.emptyList(), Collections.emptyList(),
				seq.get(processes)));
	}*/

	// ## P-Syntax ##

	/*private static Grammar<PlusCalProcesses> parsePSyntaxProcesses() {
		return parseOneOf(
				parsePSyntaxSingleProcess()
				//parsePSyntaxMultiProcess()
		);
	}*/

	//private static Grammar<PlusCalMultiProcess> parsePSyntaxMultiProcess() {
	//	return null;/*nop().map(v -> );*/
	//}

	/*private static Grammar<PlusCalSingleProcess> parsePSyntaxSingleProcess() {
		return repeatOneOrMore(parseLabeledStatements(SyntaxVariant.P_SYNTAX)).map(stmts ->
				new PlusCalSingleProcess(stmts.getLocation(), stmts));
	}*/

	//static Grammar<PlusCalAlgorithm> parsePSyntaxAlgorithm(){
	//	return nop().map(v -> null);
		/*Variable<Located<String>> name = new Variable<>("name");
		Variable<LocatedList<PlusCalVariableDeclaration>> variables = new Variable<>("variables");
		Variable<PlusCalProcesses> processes = new Variable<>("processes");
		return sequence(
				drop(matchPattern(PCAL_FIND_ALGORITHM).map(v -> new Located<>(SourceLocation.unknown(), null))),
				drop(parsePlusCalToken("--algorithm")),
				part(name, parsePlusCalIdentifier()),
				reject(parsePlusCalToken("{")), // at this point we know which syntax it is
				part(variables, parseVariablesDeclaration()),
				part(processes, parsePSyntaxProcesses()),
				parsePlusCalToken("end"), parsePlusCalToken("algorithm")
		).map(seq -> new PlusCalAlgorithm(seq.getLocation().combine(seq.getLocation()), seq.get(name),
				seq.get(variables), Collections.emptyList(), Collections.emptyList(), Collections.emptyList(),
				seq.get(processes)));*/
	//}

	/*private static Grammar<PlusCalAlgorithm> parseAlgorithm() {
		Variable<PlusCalAlgorithm> theAlgorithm = new Variable<>("theAlgorithm");
		return sequence(
				drop(matchPattern(PCAL_FIND_ALGORITHM)),
				part(theAlgorithm,  parseOneOf(parsePSyntaxAlgorithm(), parseCSyntaxAlgorithm())),
				drop(matchPattern(PCAL_AFTER_ALGORITHM))
		).map(seqResult -> seqResult.get(theAlgorithm));
	}*/

	// public interface

	public static PlusCalAlgorithm readAlgorithm(LexicalContext ctx) throws ParseFailureException {
		throw new TODO();
		//return readOrExcept(ctx, parseAlgorithm());
	}

}
