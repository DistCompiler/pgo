package pgo.util;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Vector;

import pcal.AST;
import pcal.TLAExpr;
import pgo.PGoException;
import pgo.errors.IssueContext;
import pgo.lexer.TLAToken;
import pgo.lexer.TLATokenType;
import pgo.model.pcal.*;
import pgo.model.pcal.VariableDeclaration;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAUnit;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.parser.TLAParseException;
import pgo.parser.TLAParser;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.TLAParserIssue;
import tla2sany.st.Location;

public class TLCToPGoPCalASTConversionVisitor extends PcalASTUtil.Visitor<List<Statement>> {

	private IssueContext ctx;
	private Algorithm result;
	private Vector<String> plusLabels;
	private Vector<String> minusLabels;

	public TLCToPGoPCalASTConversionVisitor(IssueContext ctx) {
		this.ctx = ctx;
	}

	private static SourceLocation sourceLocationFromRegion(AST a) {
		Location loc = a.getOrigin().toLocation();
		return new SourceLocation(Paths.get("PLUSCAL"), loc.beginLine(), loc.endLine(), loc.beginColumn(), loc.endColumn());
	}

	private List<LabeledStatements> parseProcessBody(Vector<AST> body) throws PGoException {
		List<LabeledStatements> result = new ArrayList<>();

		for(AST a : body) {
			List<Statement> statements = PcalASTUtil.accept(a, this);
			for(Statement s : statements) {
				result.add((LabeledStatements)s);
			}
		}

		return result;
	}

	private List<Statement> parseStatementSequence(Vector<AST> body) throws PGoException{
		List<Statement> result = new ArrayList<>();

		for(AST a : body) {
			List<Statement> statements = PcalASTUtil.accept(a, this);
			result.addAll(statements);
		}

		return result;
	}

	private static TLAToken convertToken(pcal.TLAToken tok){
		SourceLocation loc;
		if(tok.source == null) {
			loc = SourceLocation.unknown();
		}else {
			Location l = tok.source.toLocation();
			loc = new SourceLocation(Paths.get("TLA"), l.beginLine(), l.endLine(), l.beginColumn(), l.endColumn());
		}
		TLATokenType type;
		switch(tok.type) {
		case pcal.TLAToken.BUILTIN:
			type = TLATokenType.BUILTIN;
			break;
		case pcal.TLAToken.IDENT:
			type = TLATokenType.IDENT;
			break;
		case pcal.TLAToken.NUMBER:
			type = TLATokenType.NUMBER;
			break;
		case pcal.TLAToken.STRING:
			type = TLATokenType.STRING;
			break;
		default:
			throw new RuntimeException("unreachable");
		}
		return new TLAToken(tok.string, type, loc);
	}

	@SuppressWarnings("unchecked")
	private PGoTLAExpression parseTLAExpression(TLAExpr e) {
		if(e.isOneToken() && e.firstToken().string.equals("defaultInitValue")) {
			return new PlusCalDefaultInitValue(SourceLocation.unknown());
		}

		List<TLAToken> tokens = new ArrayList<>();
		for(Object tokList : e.tokens) {
			for(pcal.TLAToken tok : (Vector<pcal.TLAToken>)tokList) {
				tokens.add(convertToken(tok));
			}
		}
		try {
			return TLAParser.readExpression(tokens.listIterator());
		} catch (TLAParseException e1) {
			ctx.error(new TLAParserIssue(e1.getReason()));
			return null;
		}
	}

	private VariableDeclaration convertVarDecl(AST.VarDecl v) {
		return new VariableDeclaration(sourceLocationFromRegion(v), v.var, !v.isEq, parseTLAExpression(v.val));
	}

	@SuppressWarnings("unchecked")
	private Macro convertMacro(pcal.AST.Macro m) throws PGoException {
		return new Macro(sourceLocationFromRegion(m), m.name, m.params, parseStatementSequence(m.body));
	}

	private List<VariableDeclaration> convertVarDecls(Vector<AST.VarDecl> decls) {
		List<VariableDeclaration> result = new ArrayList<>();
		for(AST.VarDecl d : decls) {
			result.add(convertVarDecl(d));
		}
		return result;
	}

	private List<VariableDeclaration> convertPVarDecls(Vector<AST.PVarDecl> decls) {
		List<VariableDeclaration> result = new ArrayList<>();
		for(AST.PVarDecl d : decls) {
			result.add(convertVarDecl(d.toVarDecl()));
		}
		return result;
	}

	@SuppressWarnings("unchecked")
	private Procedure convertProcedure(pcal.AST.Procedure p) throws PGoException {
		plusLabels = p.plusLabels;
		minusLabels = p.minusLabels;
		List<LabeledStatements> stmts = parseProcessBody(p.body);
		return new Procedure(sourceLocationFromRegion(p), p.name, convertPVarDecls(p.params), convertPVarDecls(p.decls), stmts);
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	private Algorithm convertAlgorithm(SourceLocation loc, String name, Vector decls, Vector macros, Vector procs, Vector defns, Processes processes) throws PGoException {
		List<VariableDeclaration> variables = convertVarDecls(decls);

		List<Macro> resultMacros = new ArrayList<>();
		for(Object m : macros) {
			resultMacros.add(convertMacro((AST.Macro)m));
		}

		List<Procedure> procedures = new ArrayList<>();
		for(Object p : procs) {
			procedures.add(convertProcedure((AST.Procedure)p));
		}

		List<TLAToken> tokens = new ArrayList<>();
		for(Object tokList : defns) {
			for(pcal.TLAToken tok : (Vector<pcal.TLAToken>)tokList) {
				tokens.add(convertToken(tok));
			}
		}
		List<PGoTLAUnit> units;
		try {
			units = TLAParser.readUnits(tokens.listIterator());
		} catch (TLAParseException e) {
			ctx.error(new TLAParserIssue(e.getReason()));
			units = Collections.emptyList();
		}

		return new Algorithm(loc, name, variables, macros, procedures, units, processes);
	}

	public Algorithm getResult() {
		return result;
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.Uniprocess ua) throws PGoException {
		SingleProcess proc = new SingleProcess(sourceLocationFromRegion(ua), parseProcessBody(ua.body));
		result = convertAlgorithm(sourceLocationFromRegion(ua), ua.name, ua.decls, ua.macros, ua.prcds, ua.defs.tokens, proc);
		return null;
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.Multiprocess ma) throws PGoException {
		List<PcalProcess> procs = new ArrayList<>();

		for(AST.Process p : (Vector<AST.Process>)ma.procs) {
			Fairness f;
			switch(p.fairness) {
			case AST.UNFAIR_PROC:
				f = Fairness.UNFAIR;
				break;
			case AST.WF_PROC:
				f = Fairness.WEAK_FAIR;
				break;
			case AST.SF_PROC:
				f = Fairness.STRONG_FAIR;
				break;
			default:
				throw new RuntimeException("unreachable");
			}
			minusLabels = p.minusLabels;
			plusLabels = p.plusLabels;
			List<LabeledStatements> stmts = parseProcessBody(p.body);
			procs.add(new PcalProcess(sourceLocationFromRegion(p), new VariableDeclaration(
					sourceLocationFromRegion(p), p.name, !p.isEq, parseTLAExpression(p.id)),
					f, convertVarDecls(p.decls), stmts));
		}

		MultiProcess proc = new MultiProcess(sourceLocationFromRegion(ma), procs);

		result = convertAlgorithm(sourceLocationFromRegion(ma), ma.name, ma.decls, ma.macros, ma.prcds, ma.defs.tokens, proc);

		return null;
	}

	@Override
	public List<Statement> visit(AST.Procedure p) throws PGoTransException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public List<Statement> visit(AST.Process p) throws PGoTransException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public List<Statement> visit(AST.PVarDecl a) throws PGoTransException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public List<Statement> visit(AST.VarDecl a) throws PGoTransException {
		throw new RuntimeException("unreachable");
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.LabeledStmt ls) throws PGoException {
		List<Statement> statements = new ArrayList<>();
		for(AST a : (Vector<AST>)ls.stmts) {
			statements.addAll(PcalASTUtil.accept(a, this));
		}
		Label.Modifier modifier = Label.Modifier.NONE;
		if(minusLabels != null && minusLabels.contains(ls.label)) {
			modifier = Label.Modifier.MINUS;
		}else if(plusLabels != null && plusLabels.contains(ls.label)) {
			modifier = Label.Modifier.PLUS;
		}

		return Collections.singletonList(new LabeledStatements(sourceLocationFromRegion(ls),
				new Label(sourceLocationFromRegion(ls), ls.label, modifier), statements));
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.While w) throws PGoException {
		List<Statement> statements = new ArrayList<>();
		for(AST a : (Vector<AST>)w.unlabDo) {
			statements.addAll(PcalASTUtil.accept(a, this));
		}
		for(AST a : (Vector<AST>)w.labDo) {
			statements.addAll(PcalASTUtil.accept(a, this));
		}
		return Collections.singletonList(new While(sourceLocationFromRegion(w),
				parseTLAExpression(w.test), statements));
	}

	@SuppressWarnings("unchecked")
	private PGoTLAExpression parseLHS(AST.Lhs lhs) {
		List<TLAToken> lhsTok = new ArrayList<>();
		lhsTok.add(new TLAToken(lhs.var, TLATokenType.IDENT, SourceLocation.unknown()));
		for(Vector<pcal.TLAToken> tokList : (Vector<Vector<pcal.TLAToken>>)lhs.sub.tokens){
			for(pcal.TLAToken tok : tokList) {
				lhsTok.add(convertToken(tok));
			}
		}
		try {
			return TLAParser.readExpression(lhsTok.listIterator());
		} catch (TLAParseException e) {
			ctx.error(new TLAParserIssue(e.getReason()));
			return null;
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.Assign as) throws PGoException {
		List<AssignmentPair> assignments = new ArrayList<>();
		for(AST.SingleAssign a : (Vector<AST.SingleAssign>)as.ass) {
			assignments.add(new AssignmentPair(
					sourceLocationFromRegion(a), parseLHS(a.lhs), parseTLAExpression(a.rhs)));
		}
		return Collections.singletonList(new Assignment(sourceLocationFromRegion(as), assignments));
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.SingleAssign sa) throws PGoException {
		return Collections.singletonList(new Assignment(
				sourceLocationFromRegion(sa),
				Collections.singletonList(
						new AssignmentPair(
								sourceLocationFromRegion(sa),
								parseLHS(sa.lhs),
								parseTLAExpression(sa.rhs)))));
	}

	@Override
	public List<Statement> visit(AST.Lhs lhs) throws PGoTransException {
		throw new RuntimeException("unreachable");
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.If ifast) throws PGoException{
		return Collections.singletonList(new If(sourceLocationFromRegion(ifast), parseTLAExpression(ifast.test),
				parseStatementSequence(ifast.Then), parseStatementSequence(ifast.Else)));
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.Either ei) throws PGoException {
		List<List<Statement>> cases = new ArrayList<>();
		for(Vector<AST> statements : (Vector<Vector<AST>>)ei.ors) {
			cases.add(parseStatementSequence(statements));
		}
		return Collections.singletonList(new Either(sourceLocationFromRegion(ei), cases));
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.With with) throws PGoException {
		return Collections.singletonList(new With(sourceLocationFromRegion(with),
				new VariableDeclaration(sourceLocationFromRegion(with), with.var, !with.isEq, parseTLAExpression(with.exp)), parseStatementSequence(with.Do)));
	}

	@Override
	public List<Statement> visit(AST.When when) throws PGoException {
		return Collections.singletonList(new Await(sourceLocationFromRegion(when), parseTLAExpression(when.exp)));
	}

	@Override
	public List<Statement> visit(AST.PrintS ps) throws PGoException {
		return Collections.singletonList(new Print(sourceLocationFromRegion(ps), parseTLAExpression(ps.exp)));
	}

	@Override
	public List<Statement> visit(AST.Assert as) throws PGoException {
		return Collections.singletonList(new Assert(sourceLocationFromRegion(as), parseTLAExpression(as.exp)));
	}

	@Override
	public List<Statement> visit(AST.Skip s) throws PGoTransException {
		return Collections.singletonList(new Skip(sourceLocationFromRegion(s)));
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.LabelIf lif) throws PGoException {
		List<Statement> yes = new ArrayList<>();
		for(AST a : (Vector<AST>)lif.unlabThen) {
			yes.addAll(PcalASTUtil.accept(a, this));
		}
		for(AST a : (Vector<AST>)lif.labThen) {
			yes.addAll(PcalASTUtil.accept(a, this));
		}
		List<Statement> no = new ArrayList<>();
		for(AST a : (Vector<AST>)lif.unlabElse) {
			no.addAll(PcalASTUtil.accept(a, this));
		}
		for(AST a : (Vector<AST>)lif.labElse) {
			no.addAll(PcalASTUtil.accept(a, this));
		}
		return Collections.singletonList(new If(sourceLocationFromRegion(lif),
				parseTLAExpression(lif.test), yes, no));
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.LabelEither le) throws PGoException {
		List<List<Statement>> cases = new ArrayList<>();
		for(AST.Clause c : (Vector<AST.Clause>)le.clauses) {
			List<Statement> statements = new ArrayList<>();
			for(AST a : (Vector<AST>)c.unlabOr) {
				statements.addAll(PcalASTUtil.accept(a, this));
			}
			for(AST a : (Vector<AST>)c.labOr) {
				statements.addAll(PcalASTUtil.accept(a, this));
			}
		}
		return Collections.singletonList(new Either(sourceLocationFromRegion(le), cases));
	}

	@Override
	public List<Statement> visit(AST.Clause c) throws PGoTransException {
		throw new RuntimeException("unreachable");
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.Call c) throws PGoException {
		List<PGoTLAExpression> args = new ArrayList<>();
		for(TLAExpr e : (Vector<TLAExpr>)c.args) {
			args.add(parseTLAExpression(e));
		}
		return Collections.singletonList(new Call(sourceLocationFromRegion(c), c.to, args));
	}

	@Override
	public List<Statement> visit(AST.Return r) throws PGoTransException {
		return Collections.singletonList(new Return(sourceLocationFromRegion(r)));
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.CallReturn cr) throws PGoException {
		List<Statement> statements = new ArrayList<>();
		List<PGoTLAExpression> args = new ArrayList<>();
		for(TLAExpr e : (Vector<TLAExpr>)cr.args) {
			args.add(parseTLAExpression(e));
		}
		statements.add(new Call(sourceLocationFromRegion(cr), cr.to, args));
		statements.add(new Return(sourceLocationFromRegion(cr)));
		return statements;
	}

	@Override
	public List<Statement> visit(AST.Goto g) throws PGoTransException {
		return Collections.singletonList(new Goto(sourceLocationFromRegion(g), g.to));
	}

	@Override
	public List<Statement> visit(AST.Macro m) throws PGoTransException {
		throw new RuntimeException("unreachable");
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.MacroCall m) throws PGoException {
		List<PGoTLAExpression> args = new ArrayList<>();
		for(TLAExpr e : (Vector<TLAExpr>)m.args) {
			args.add(parseTLAExpression(e));
		}
		return Collections.singletonList(new MacroCall(sourceLocationFromRegion(m), m.name, args));
	}

}
