package pgo.parser;

import pgo.Unreachable;
import pgo.model.pcal.*;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.*;
import java.util.regex.Pattern;

import static pgo.parser.ParseTools.*;
import static pgo.parser.TLAParser.*;

/**
 * The pluscal parser.
 *
 * This class takes a given pluscal file and parses it into the pluscal AST.
 *
 */
public final class PcalParser {
	private PcalParser() {}

	private static final Pattern PCAL_FIND_ALGORITHM = Pattern.compile(".*?\\(\\*.*?(?=--algorithm)", Pattern.DOTALL);

	private enum SyntaxVariant {
		P_SYNTAX,
		C_SYNTAX,
	}

	static Grammar<Located<Void>> parseBlockBegin(SyntaxVariant syntax, Grammar<Located<Void>> altMarker) {
		switch(syntax){
			case P_SYNTAX:
				return altMarker;
			case C_SYNTAX:
				return parsePlusCalToken("{");
		}
		throw new Unreachable();
	}

	static Grammar<Located<Void>> parseBlockEnd(SyntaxVariant syntax, Grammar<Located<Void>> altMarker) {
		switch(syntax){
			case P_SYNTAX:
				return altMarker;
			case C_SYNTAX:
				return parsePlusCalToken("}");
		}
		throw new Unreachable();
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

	static Grammar<VariableDeclaration> parseVariableDeclaration(){
		Variable<Located<String>> id = new Variable<>("id");
		Variable<Located<Boolean>> isSet = new Variable<>("isSet");
		Variable<PGoTLAExpression> expression = new Variable<>("expression");
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
		).map(seq -> new VariableDeclaration(
				seq.getLocation(), seq.get(id), seq.get(isSet).getValue(), seq.get(expression)));
	}

	static Grammar<LocatedList<VariableDeclaration>> parseVariablesDeclaration(){
		Variable<LocatedList<VariableDeclaration>> variables = new Variable<>("variables");
		return sequence(
				drop(parsePlusCalTokenOneOf(Arrays.asList("variables", "variable"))),
				part(variables, parseCommaList(parseVariableDeclaration())),
				drop(parsePlusCalToken(";"))
		).map(seq -> new LocatedList<>(seq.getLocation(), seq.get(variables)));
	}

	static Grammar<Label> parseLabel(){
		Variable<Located<String>> labelName = new Variable<>("labelName");
		Variable<Located<Label.Modifier>> fairness = new Variable<>("fairness");
		return sequence(
				part(labelName, parsePlusCalIdentifier()),
				drop(parsePlusCalToken(":")),
				part(fairness, parseOneOf(
						parsePlusCalToken("+").map(v -> new Located<>(v.getLocation(), Label.Modifier.PLUS)),
						parsePlusCalToken("-").map(v -> new Located<>(v.getLocation(), Label.Modifier.MINUS)),
						nop().map(v -> new Located<>(v.getLocation(), Label.Modifier.NONE))
				))
		).map(seq -> new Label(seq.getLocation(), seq.get(labelName).getValue(), seq.get(fairness).getValue()));
	}

	static Grammar<LocatedList<Statement>> parseStatementList(SyntaxVariant syntax){
		switch(syntax){
			case P_SYNTAX:
				return parseListOf(parseStatement(syntax), parsePlusCalToken(";"));
			case C_SYNTAX:
				// used in C-style syntax for either { stmts... } or exactly one statement
				Variable<LocatedList<Statement>> statements = new Variable<>("statements");
				return parseOneOf(
						sequence(
								drop(parsePlusCalToken("{")),
								part(statements, scope(() ->
										repeatOneOrMore(parseStatementList(syntax)).map(seq -> {
											LocatedList<Statement> flattened = new LocatedList<>(
													SourceLocation.unknown(), new ArrayList<>());
											for(LocatedList<Statement> list : seq){
												flattened.addLocation(list.getLocation());
												flattened.addAll(list);
											}
											return flattened;
										}))),
								drop(parsePlusCalToken("}"))
						).map(seq -> seq.get(statements)),
						parseStatement(SyntaxVariant.C_SYNTAX).map(s ->
								new LocatedList<>(s.getLocation(), Collections.singletonList(s)))
				);
		}
		throw new Unreachable();
	}

	static Grammar<LabeledStatements> parseLabeledStatements(SyntaxVariant syntax){
		Variable<Label> label = new Variable<>("label");
		Variable<LocatedList<Statement>> statements = new Variable<>("statements");
		return sequence(
				part(label, parseLabel()),
				part(statements, scope(() ->
						sequence(
								part(statements, parseListOf(parseStatement(syntax), parsePlusCalToken(";"))),
								drop(parseOneOf(parsePlusCalToken(";"), nop()))
						).map(seq -> seq.get(statements))))
		).map(seq -> new LabeledStatements(seq.getLocation(), seq.get(label), seq.get(statements)));
	}

	static Grammar<If> parseElsifPart(){
		Variable<PGoTLAExpression> condition = new Variable<>("condition");
		Variable<LocatedList<Statement>> thenStatements = new Variable<>("thenStatements");
		Variable<LocatedList<Statement>> elseStatements = new Variable<>("elseStatements");
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
								new LocatedList<>(v.getLocation(), Collections.singletonList(new Skip(v.getLocation()))))
				))
		).map(seq -> new If(
				seq.getLocation(), seq.get(condition), seq.get(thenStatements), seq.get(elseStatements)));
	}

	static Grammar<If> parseIfStatement(SyntaxVariant syntax){
		Variable<PGoTLAExpression> condition = new Variable<>("condition");
		Variable<LocatedList<Statement>> thenStatements = new Variable<>("thenStatements");
		Variable<LocatedList<Statement>> elseStatements = new Variable<>("elseStatements");
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
										v.getLocation(), Collections.singletonList(new Skip(v.getLocation()))))
						)),
						drop(sequence(
								drop(parsePlusCalToken("end")),
								drop(parsePlusCalToken("if"))
						))
				).map(seq -> new If(
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
										v.getLocation(), Collections.singletonList(new Skip(v.getLocation()))))
						))
				).map(seq -> new If(
						seq.getLocation(), seq.get(condition), seq.get(thenStatements), seq.get(elseStatements)));
			default:
				throw new Unreachable();
		}
	}

	static Grammar<Either> parseEitherStatement(SyntaxVariant syntax){
		Variable<LocatedList<Statement>> firstClause = new Variable<>("firstClause");
		Variable<LocatedList<Statement>> tmpClause = new Variable<>("tmpClause");
 		Variable<LocatedList<LocatedList<Statement>>> restClauses = new Variable<>("restClauses");
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
			List<List<Statement>> clauses = new ArrayList<>();
			clauses.add(seq.get(firstClause));
			clauses.addAll(seq.get(restClauses));
			return new Either(seq.getLocation(), clauses);
		});
	}

	static Grammar<While> parseWhileStatement(SyntaxVariant syntax){
		Variable<PGoTLAExpression> condition = new Variable<>("condition");
		Variable<LocatedList<Statement>> body = new Variable<>("body");
		return sequence(
				drop(parsePlusCalToken("while")),
				part(condition, parseBracketed(syntax, parseExpression())),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parsePlusCalToken("do")),
				part(body, parseStatementList(syntax)),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parseEnd(parsePlusCalToken("while")))
		).map(seq -> new While(seq.getLocation(), seq.get(condition), seq.get(body)));
	}

	static Grammar<Await> parseAwaitStatement(){
		Variable<PGoTLAExpression> condition = new Variable<>("condition");
		return sequence(
				drop(parsePlusCalTokenOneOf(Arrays.asList("await", "when"))),
				part(condition, parseExpression())
		).map(seq -> new Await(seq.getLocation(), seq.get(condition)));
	}

	static Grammar<With> parseWithStatement(SyntaxVariant syntax){
		Variable<LocatedList<VariableDeclaration>> decls = new Variable<>("decls");
		Variable<LocatedList<Statement>> body = new Variable<>("body");
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
			LocatedList<VariableDeclaration> ds = seq.get(decls);
			With with = new With(
					ds.get(ds.size()-1).getLocation().combine(seq.get(body).getLocation()),
					ds.get(ds.size()-1), seq.get(body));
			for(int i = ds.size() - 2; i >= 0; --i){
				with = new With(ds.get(i).getLocation(), ds.get(i), Collections.singletonList(with));
			}
			return with;
		});
	}

	static Grammar<Skip> parseSkipStatement(){
		return parsePlusCalToken("skip")
				.map(seq -> new Skip(seq.getLocation()));
	}

	static Grammar<Print> parsePrintStatement(){
		Variable<PGoTLAExpression> value = new Variable<>("value");
		return sequence(
				drop(parsePlusCalToken("print")),
				part(value, parseExpression())
		).map(seq -> new Print(seq.getLocation(), seq.get(value)));
	}

	static Grammar<Assert> parseAssertStatement(){
		Variable<PGoTLAExpression> condition = new Variable<>("condition");
		return sequence(
				drop(parsePlusCalToken("assert")),
				part(condition, parseExpression())
		).map(seq -> new Assert(seq.getLocation(), seq.get(condition)));
	}

	static Grammar<Call> parseCallStatement(){
		Variable<Located<String>> target = new Variable<>("target");
		Variable<LocatedList<PGoTLAExpression>> arguments = new Variable<>("arguments");
		return sequence(
				drop(parsePlusCalToken("call")),
				part(target, parsePlusCalIdentifier()),
				drop(parsePlusCalToken("(")),
				part(arguments, parseCommaList(parseExpression())),
				drop(parsePlusCalToken(")"))
		).map(seq -> new Call(seq.getLocation(), seq.get(target).getValue(), seq.get(arguments)));
	}
	
	static Grammar<Return> parseReturnStatement(){
		return parsePlusCalToken("return")
				.map(seq -> new Return(seq.getLocation()));
	}
	
	static Grammar<Goto> parseGotoStatement(){
		Variable<Located<String>> target = new Variable<>("target");
		return sequence(
				drop(parsePlusCalToken("goto")),
				part(target, parsePlusCalIdentifier())
		).map(seq -> new Goto(seq.getLocation(), seq.get(target).getValue()));
	}

	static Grammar<AssignmentPair> parseAssignmentPair(){
		Variable<PGoTLAExpression> lhs = new Variable<>("lhs");
		Variable<PGoTLAExpression> rhs = new Variable<>("rhs");
		return sequence(
				part(lhs, parseExpression()),
				drop(parsePlusCalToken(":=")),
				part(rhs, parseExpression())
		).map(seq -> new AssignmentPair(seq.getLocation(), seq.get(lhs), seq.get(rhs)));
	}

	static Grammar<Assignment> parseAssignmentStatement(){
		return parseListOf(parseAssignmentPair(), parsePlusCalToken("||"))
				.map(seq -> new Assignment(seq.getLocation(), seq));
	}

	static Grammar<Statement> parseStatement(SyntaxVariant syntax){
		return parseOneOf(
				parseLabeledStatements(syntax),
				parseIfStatement(syntax),
				parseEitherStatement(syntax),
				parseWhileStatement(syntax),
				parseAwaitStatement(),
				parseWithStatement(syntax),
				parseSkipStatement(),
				parsePrintStatement(),
				parseAssertStatement(),
				parseCallStatement(),
				parseReturnStatement(),
				parseGotoStatement(),
				parseAssignmentStatement()
		);
	}

	static Grammar<SingleProcess> parseSingleProcess(SyntaxVariant syntax){
		Variable<LocatedList<LabeledStatements>> labeledStatements = new Variable<>("labeledStatements");
		return sequence(
				drop(parseBlockBegin(syntax, parsePlusCalToken("begin"))),
				part(labeledStatements, repeat(parseLabeledStatements(syntax)))
		).map(seq -> new SingleProcess(seq.getLocation(), seq.get(labeledStatements)));
	}

	static Grammar<PcalProcess> parseProcess(SyntaxVariant syntax){
		Variable<Located<Fairness>> fairness = new Variable<>("fairness");
		Variable<VariableDeclaration> name = new Variable<>("name");
		Variable<LocatedList<VariableDeclaration>> variables = new Variable<>("variables");
		Variable<LocatedList<LabeledStatements>> labeledStatements = new Variable<>("labeledStatements");
		return sequence(
				part(fairness, parseOneOf(
						/*parsePlusCalToken("fair").chain(v -> parseOneOf(
								parsePlusCalToken("+").map(vv ->
										new Located<>(v.getLocation().combine(vv.getLocation()), Fairness.STRONG_FAIR)),
								nop().map(vv -> new Located<>(v.getLocation(), Fairness.WEAK_FAIR))
						)),
						nop().map(v -> new Located<>(SourceLocation.unknown(), Fairness.UNFAIR))*/
				)),
				drop(parsePlusCalToken("process")),
				part(name, parseBracketed(syntax, parseVariableDeclaration())),
				part(variables, parseVariablesDeclaration()),
				drop(parseBlockBegin(syntax, parsePlusCalToken("begin"))),
				part(labeledStatements, parseListOf(parseLabeledStatements(syntax), parsePlusCalToken(";"))),
				drop(parseOneOf(parsePlusCalToken(";"), nop())),
				drop(parseBlockEnd(syntax, parseEnd(parsePlusCalToken("process"))))
		).map(seq -> new PcalProcess(
				seq.getLocation(), seq.get(name), seq.get(fairness).getValue(), seq.get(variables),
				seq.get(labeledStatements)));
	}

	static Grammar<MultiProcess> parseMultiProcess(SyntaxVariant syntax){
		return repeat(parseProcess(syntax)).map(procs -> new MultiProcess(procs.getLocation(), procs));
	}

	static Grammar<Processes> parseProcesses(SyntaxVariant syntax){
		return parseOneOf(
				parseSingleProcess(syntax),
				parseMultiProcess(syntax)
		);
	}

	static Grammar<Algorithm> parseAlgorithm(){
		Variable<Located<String>> name = new Variable<>("name");
		Variable<Located<SyntaxVariant>> syntax = new Variable<>("syntax");
		Variable<LocatedList<VariableDeclaration>> variables = new Variable<>("variables");
		Variable<Processes> processes = new Variable<>("processes");
		return sequence(
				drop(matchPattern(PCAL_FIND_ALGORITHM).map(v -> new Located<>(SourceLocation.unknown(), null))),
				drop(parsePlusCalToken("--algorithm")),
				part(name, parsePlusCalIdentifier()),
				part(syntax, parseOneOf(
						parsePlusCalToken("{").map(v ->
								new Located<>(v.getLocation(), SyntaxVariant.C_SYNTAX)),
						nop().map(v -> new Located<>(SourceLocation.unknown(), SyntaxVariant.P_SYNTAX))
				)),
				part(variables, parseVariablesDeclaration()),
				part(processes, parseProcesses(/* TODO */ null)),
				drop(parseBlockEnd(
						/* TODO */ null,
						parseEnd(parsePlusCalToken("algorithm"))))
		).map(seq -> new Algorithm(seq.getLocation().combine(seq.getLocation()), seq.get(name),
				seq.get(variables), Collections.emptyList(), Collections.emptyList(), Collections.emptyList(),
				seq.get(processes)));
	}

	// public interface

	public static Algorithm readAlgorithm(LexicalContext ctx) throws TLAParseException {
		return readOrExcept(ctx, parseAlgorithm());
	}

}
