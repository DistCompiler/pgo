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
				Mutator<Result> result = new Mutator<>();
				return sequence(
						drop(parsePlusCalToken("(")),
						part(result, action),
						drop(parsePlusCalToken(")"))
				).map(seq -> result.getValue());
		}
		throw new Unreachable();
	}

	static Grammar<VariableDeclaration> parseVariableDeclaration(){
		Mutator<Located<String>> id = new Mutator<>();
		Mutator<Located<Boolean>> isSet = new Mutator<>();
		Mutator<PGoTLAExpression> expression = new Mutator<>();
		Mutator<VariableDeclaration> result = new Mutator<>();
		return sequence(
				part(id, parsePlusCalIdentifier()),
				part(expression, parseOneOf(
						sequence(
								part(isSet, parsePlusCalToken("=").map(v ->
										new Located<>(v.getLocation(), false))),
								part(expression, parseExpression(-1))
						).map(seq -> expression.getValue()),
						sequence(
								part(isSet, parsePlusCalToken("\\in").map(v ->
										new Located<>(v.getLocation(), true))),
								part(expression, parseExpression(-1))
						).map(seq -> expression.getValue()),
						nop().map(v -> new PlusCalDefaultInitValue(id.getValue().getLocation()))
				))
		).map(seq -> new VariableDeclaration(
				seq.getLocation(), id.getValue(), isSet.getValue().getValue(), expression.getValue()));
	}

	static Grammar<LocatedList<VariableDeclaration>> parseVariablesDeclaration(){
		Mutator<LocatedList<VariableDeclaration>> variables = new Mutator<>();
		return sequence(
				drop(parsePlusCalTokenOneOf(Arrays.asList("variables", "variable"))),
				part(variables, parseCommaList(parseVariableDeclaration())),
				drop(parsePlusCalToken(";"))
		).map(seq -> new LocatedList<>(seq.getLocation(), variables.getValue()));
	}

	static Grammar<Label> parseLabel(){
		Mutator<Located<String>> labelName = new Mutator<>();
		Mutator<Located<Label.Modifier>> fairness = new Mutator<>();
		return sequence(
				part(labelName, parsePlusCalIdentifier()),
				drop(parsePlusCalToken(":")),
				part(fairness, parseOneOf(
						parsePlusCalToken("+").map(v -> new Located<>(v.getLocation(), Label.Modifier.PLUS)),
						parsePlusCalToken("-").map(v -> new Located<>(v.getLocation(), Label.Modifier.MINUS)),
						nop().map(v -> new Located<>(v.getLocation(), Label.Modifier.NONE))
				))
		).map(seq -> new Label(seq.getLocation(), labelName.getValue().getValue(), fairness.getValue().getValue()));
	}

	static Grammar<LocatedList<Statement>> parseStatementList(SyntaxVariant syntax){
		switch(syntax){
			case P_SYNTAX:
				return parseListOf(parseStatement(syntax), parsePlusCalToken(";"));
			case C_SYNTAX:
				// used in C-style syntax for either { stmts... } or exactly one statement
				Mutator<LocatedList<Statement>> statements = new Mutator<>();
				return parseOneOf(
						sequence(
								drop(parsePlusCalToken("{")),
								part(statements, nop().chain(v ->
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
						).map(seq -> statements.getValue()),
						parseStatement(SyntaxVariant.C_SYNTAX).map(s ->
								new LocatedList<>(s.getLocation(), Collections.singletonList(s)))
				);
		}
		throw new Unreachable();
	}

	static Grammar<LabeledStatements> parseLabeledStatements(SyntaxVariant syntax){
		Mutator<Label> label = new Mutator<>();
		Mutator<LocatedList<Statement>> statements = new Mutator<>();
		return sequence(
				part(label, parseLabel()),
				part(statements, nop().chain(v ->
						sequence(
								part(statements, parseListOf(parseStatement(syntax), parsePlusCalToken(";"))),
								drop(parseOneOf(parsePlusCalToken(";"), nop()))
						).map(seq -> statements.getValue())))
		).map(seq -> new LabeledStatements(seq.getLocation(), label.getValue(), statements.getValue()));
	}

	static Grammar<If> parseElsifPart(){
		Mutator<PGoTLAExpression> condition = new Mutator<>();
		Mutator<LocatedList<Statement>> thenStatements = new Mutator<>();
		Mutator<LocatedList<Statement>> elseStatements = new Mutator<>();
		return sequence(
				drop(parsePlusCalToken("elsif")),
				part(condition, parseExpression(-1)),
				drop(parsePlusCalToken("then")),
				part(thenStatements, nop().chain(v -> parseStatementList(SyntaxVariant.P_SYNTAX))),
				part(elseStatements, parseOneOf(
						sequence(
								drop(parsePlusCalToken("else")),
								part(elseStatements, nop().chain(v -> parseStatementList(SyntaxVariant.P_SYNTAX)))
						).map(seq -> elseStatements.getValue()),
						nop().chain(v -> parseElsifPart().map(f ->
								new LocatedList<>(f.getLocation(), Collections.singletonList(f)))),
						nop().map(v ->
								new LocatedList<>(v.getLocation(), Collections.singletonList(new Skip(v.getLocation()))))
				))
		).map(seq -> new If(
				seq.getLocation(), condition.getValue(), thenStatements.getValue(), elseStatements.getValue()));
	}

	static Grammar<If> parseIfStatement(SyntaxVariant syntax){
		Mutator<PGoTLAExpression> condition = new Mutator<>();
		Mutator<LocatedList<Statement>> thenStatements = new Mutator<>();
		Mutator<LocatedList<Statement>> elseStatements = new Mutator<>();
		switch(syntax){
			case P_SYNTAX:
				return sequence(
						drop(parsePlusCalToken("if")),
						part(condition, parseExpression(-1)),
						drop(parsePlusCalToken("then")),
						part(thenStatements, nop().chain(v -> parseStatementList(syntax))),
						part(elseStatements, parseOneOf(
								parseElsifPart().map(f -> new LocatedList<>(
										f.getLocation(), Collections.singletonList(f))),
								sequence(
										drop(parsePlusCalToken("else")),
										part(elseStatements, nop().chain(v -> parseStatementList(syntax)))
								).map(seq -> elseStatements.getValue()),
								nop().map(v -> new LocatedList<>(
										v.getLocation(), Collections.singletonList(new Skip(v.getLocation()))))
						)),
						drop(sequence(
								drop(parsePlusCalToken("end")),
								drop(parsePlusCalToken("if"))
						))
				).map(seq -> new If(
						seq.getLocation(), condition.getValue(), thenStatements.getValue(),
						elseStatements.getValue()));
			case C_SYNTAX:
				return sequence(
						drop(parsePlusCalToken("if")),
						drop(parsePlusCalToken("(")),
						part(condition, parseExpression(-1)),
						drop(parsePlusCalToken(")")),
						part(thenStatements, nop().chain(v -> nop().chain(vv -> parseStatementList(syntax)))),
						part(elseStatements, parseOneOf(
								sequence(
										drop(parsePlusCalToken("else")),
										part(elseStatements, nop().chain(v -> parseStatementList(syntax)))
								).map(seq -> elseStatements.getValue()),
								nop().map(v -> new LocatedList<>(
										v.getLocation(), Collections.singletonList(new Skip(v.getLocation()))))
						))
				).map(seq -> new If(
						seq.getLocation(), condition.getValue(), thenStatements.getValue(), elseStatements.getValue()));
			default:
				throw new Unreachable();
		}
	}

	static Grammar<Either> parseEitherStatement(SyntaxVariant syntax){
		Mutator<LocatedList<Statement>> firstClause = new Mutator<>();
		Mutator<LocatedList<Statement>> tmpClause = new Mutator<>();
 		Mutator<LocatedList<LocatedList<Statement>>> restClauses = new Mutator<>();
		return sequence(
				drop(parsePlusCalToken("either")),
				part(firstClause, nop().chain(v -> parseStatementList(syntax))),
				part(restClauses, repeat(
						sequence(
							drop(parsePlusCalToken("or")),
							part(tmpClause, nop().chain(v -> parseStatementList(syntax)))
						).map(seq -> tmpClause.getValue()))),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parseEnd(parsePlusCalToken("either")))
		).map(seq -> {
			List<List<Statement>> clauses = new ArrayList<>();
			clauses.add(firstClause.getValue());
			clauses.addAll(restClauses.getValue());
			return new Either(seq.getLocation(), clauses);
		});
	}

	static Grammar<While> parseWhileStatement(SyntaxVariant syntax){
		Mutator<PGoTLAExpression> condition = new Mutator<>();
		Mutator<LocatedList<Statement>> body = new Mutator<>();
		return sequence(
				drop(parsePlusCalToken("while")),
				part(condition, parseBracketed(syntax, parseExpression(-1))),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parsePlusCalToken("do")),
				part(body, nop().chain(v -> parseStatementList(syntax))),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parseEnd(parsePlusCalToken("while")))
		).map(seq -> new While(seq.getLocation(), condition.getValue(), body.getValue()));
	}

	static Grammar<Await> parseAwaitStatement(){
		Mutator<PGoTLAExpression> condition = new Mutator<>();
		return sequence(
				drop(parsePlusCalTokenOneOf(Arrays.asList("await", "when"))),
				part(condition, parseExpression(-1))
		).map(seq -> new Await(seq.getLocation(), condition.getValue()));
	}

	static Grammar<With> parseWithStatement(SyntaxVariant syntax){
		Mutator<LocatedList<VariableDeclaration>> decls = new Mutator<>();
		Mutator<LocatedList<Statement>> body = new Mutator<>();
		return sequence(
				drop(parsePlusCalToken("with")),
				part(decls, parseBracketed(
						syntax,
						parseListOf(parseVariableDeclaration(), parsePlusCalToken(";")))),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parsePlusCalToken("do")),
				part(body, nop().chain(v -> parseStatementList(syntax))),
				drop(syntax == SyntaxVariant.C_SYNTAX ? nop() : parseEnd(parsePlusCalToken("with")))
		).map(seq -> {
			// navigate through the list of bindings in reverse to produce the proper recursive structure
			// of single-binding AST nodes
			LocatedList<VariableDeclaration> ds = decls.getValue();
			With with = new With(
					ds.get(ds.size()-1).getLocation().combine(body.getValue().getLocation()),
					ds.get(ds.size()-1), body.getValue());
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
		Mutator<PGoTLAExpression> value = new Mutator<>();
		return sequence(
				drop(parsePlusCalToken("print")),
				part(value, parseExpression(-1))
		).map(seq -> new Print(seq.getLocation(), value.getValue()));
	}

	static Grammar<Assert> parseAssertStatement(){
		Mutator<PGoTLAExpression> condition = new Mutator<>();
		return sequence(
				drop(parsePlusCalToken("assert")),
				part(condition, parseExpression(-1))
		).map(seq -> new Assert(seq.getLocation(), condition.getValue()));
	}

	static Grammar<Call> parseCallStatement(){
		Mutator<Located<String>> target = new Mutator<>();
		Mutator<LocatedList<PGoTLAExpression>> arguments = new Mutator<>();
		return sequence(
				drop(parsePlusCalToken("call")),
				part(target, parsePlusCalIdentifier()),
				drop(parsePlusCalToken("(")),
				part(arguments, parseCommaList(parseExpression(-1))),
				drop(parsePlusCalToken(")"))
		).map(seq -> new Call(seq.getLocation(), target.getValue().getValue(), arguments.getValue()));
	}
	
	static Grammar<Return> parseReturnStatement(){
		return parsePlusCalToken("return")
				.map(seq -> new Return(seq.getLocation()));
	}
	
	static Grammar<Goto> parseGotoStatement(){
		Mutator<Located<String>> target = new Mutator<>();
		return sequence(
				drop(parsePlusCalToken("goto")),
				part(target, parsePlusCalIdentifier())
		).map(seq -> new Goto(seq.getLocation(), target.getValue().getValue()));
	}

	static Grammar<AssignmentPair> parseAssignmentPair(){
		Mutator<PGoTLAExpression> lhs = new Mutator<>();
		Mutator<PGoTLAExpression> rhs = new Mutator<>();
		return sequence(
				part(lhs, parseExpression(-1)),
				drop(parsePlusCalToken(":=")),
				part(rhs, parseExpression(-1))
		).map(seq -> new AssignmentPair(seq.getLocation(), lhs.getValue(), rhs.getValue()));
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
		Mutator<LocatedList<LabeledStatements>> labeledStatements = new Mutator<>();
		return sequence(
				drop(parseBlockBegin(syntax, parsePlusCalToken("begin"))),
				part(labeledStatements, repeat(parseLabeledStatements(syntax)))
		).map(seq -> new SingleProcess(seq.getLocation(), labeledStatements.getValue()));
	}

	static Grammar<PcalProcess> parseProcess(SyntaxVariant syntax){
		Mutator<Located<Fairness>> fairness = new Mutator<>();
		Mutator<VariableDeclaration> name = new Mutator<>();
		Mutator<LocatedList<VariableDeclaration>> variables = new Mutator<>();
		Mutator<LocatedList<LabeledStatements>> labeledStatements = new Mutator<>();
		return sequence(
				part(fairness, parseOneOf(
						parsePlusCalToken("fair").chain(v -> parseOneOf(
								parsePlusCalToken("+").map(vv ->
										new Located<>(v.getLocation().combine(vv.getLocation()), Fairness.STRONG_FAIR)),
								nop().map(vv -> new Located<>(v.getLocation(), Fairness.WEAK_FAIR))
						)),
						nop().map(v -> new Located<>(SourceLocation.unknown(), Fairness.UNFAIR))
				)),
				drop(parsePlusCalToken("process")),
				part(name, parseBracketed(syntax, parseVariableDeclaration())),
				part(variables, parseVariablesDeclaration()),
				drop(parseBlockBegin(syntax, parsePlusCalToken("begin"))),
				part(labeledStatements, parseListOf(parseLabeledStatements(syntax), parsePlusCalToken(";"))),
				drop(parseOneOf(parsePlusCalToken(";"), nop())),
				drop(parseBlockEnd(syntax, parseEnd(parsePlusCalToken("process"))))
		).map(seq -> new PcalProcess(
				seq.getLocation(), name.getValue(), fairness.getValue().getValue(), variables.getValue(),
				labeledStatements.getValue()));
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
		Mutator<Located<String>> name = new Mutator<>();
		Mutator<Located<SyntaxVariant>> syntax = new Mutator<>();
		Mutator<LocatedList<VariableDeclaration>> variables = new Mutator<>();
		Mutator<Processes> processes = new Mutator<>();
		return sequence(
				drop(matchPattern(PCAL_FIND_ALGORITHM).map(v -> new Located<>(SourceLocation.unknown(), null))),
				drop(parsePlusCalToken("--algorithm")),
				part(name, parsePlusCalIdentifier()),
				part(syntax, parseOneOf(
						parsePlusCalToken("{").map(v ->
								new Located<>(v.getLocation(), SyntaxVariant.C_SYNTAX)),
						nop().map(v -> new Located<>(SourceLocation.unknown(), SyntaxVariant.P_SYNTAX))
				))
		).chain(seq1 -> sequence( // defer the rest until we know the syntax version from the above parse rule
				part(variables, parseVariablesDeclaration()),
				part(processes, parseProcesses(syntax.getValue().getValue())),
				drop(parseBlockEnd(
						syntax.getValue().getValue(),
						parseEnd(parsePlusCalToken("algorithm"))))
		).map(seq -> new Algorithm(seq1.getLocation().combine(seq.getLocation()), name.getValue(),
				variables.getValue(), Collections.emptyList(), Collections.emptyList(), Collections.emptyList(),
				processes.getValue())));
	}

	// public interface

	public static Algorithm readAlgorithm(LexicalContext ctx) throws TLAParseException {
		return readOrExcept(ctx, parseAlgorithm());
	}

}
