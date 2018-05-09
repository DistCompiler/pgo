package pgo.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import pcal.AST;
import pcal.TLAExpr;
import pcal.TLAToken;
import pgo.PGoException;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.Assert;
import pgo.model.pcal.Assignment;
import pgo.model.pcal.Await;
import pgo.model.pcal.Call;
import pgo.model.pcal.Either;
import pgo.model.pcal.Fairness;
import pgo.model.pcal.Goto;
import pgo.model.pcal.If;
import pgo.model.pcal.Label;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.Macro;
import pgo.model.pcal.MacroCall;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.PcalProcess;
import pgo.model.pcal.Print;
import pgo.model.pcal.Procedure;
import pgo.model.pcal.Processes;
import pgo.model.pcal.Return;
import pgo.model.pcal.SingleProcess;
import pgo.model.pcal.Skip;
import pgo.model.pcal.Statement;
import pgo.model.pcal.VariableDecl;
import pgo.model.pcal.While;
import pgo.model.pcal.With;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAInstance;
import pgo.model.tla.PGoTLAOperator;
import pgo.parser.PGoTLAParseException;
import pgo.parser.TLAParser;
import pgo.trans.PGoTransException;

public class TLCToPGoPCalASTConversionVisitor extends PcalASTUtil.Visitor<List<Statement>> {
	
	Algorithm result;
	Vector<String> plusLabels;
	Vector<String> minusLabels;
	
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
	
	@SuppressWarnings("unchecked")
	private static PGoTLAExpression parseTLAExpression(TLAExpr e) throws PGoTLAParseException {
		List<TLAToken> tokens = new ArrayList<>();
		for(Object tokList : e.tokens) {
			tokens.addAll((Vector<TLAToken>)tokList);
		}
		return TLAParser.readExpression(tokens.listIterator());
	}
	
	private VariableDecl convertVarDecl(AST.VarDecl v) throws PGoTLAParseException {
		return new VariableDecl(v.var, !v.isEq, parseTLAExpression(v.val));
	}

	@SuppressWarnings("unchecked")
	private Macro convertMacro(pcal.AST.Macro m) throws PGoException {
		return new Macro(m.name, m.params, parseStatementSequence(m.body));
	}
	
	private List<VariableDecl> convertVarDecls(Vector<AST.VarDecl> decls) throws PGoTLAParseException{
		List<VariableDecl> result = new ArrayList<>();
		for(AST.VarDecl d : decls) {
			result.add(convertVarDecl(d));
		}
		return result;
	}
	
	private List<VariableDecl> convertPVarDecls(Vector<AST.PVarDecl> decls) throws PGoTLAParseException{
		List<VariableDecl> result = new ArrayList<>();
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
		return new Procedure(p.name, convertPVarDecls(p.params), convertPVarDecls(p.decls), stmts);
	}
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	private Algorithm convertAlgorithm(String name, Vector decls, Vector macros, Vector procs, Vector defns, Processes processes) throws PGoException {
		List<VariableDecl> variables = convertVarDecls(decls);
		
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
			tokens.addAll((Vector<TLAToken>)tokList);
		}
		Map<String, PGoTLAOperator> operatorDefinitions = new HashMap<>();
		Map<String, PGoTLAFunction> functionDefinitions = new HashMap<>();
		List<PGoTLAInstance> instanceDefinitions = new ArrayList<>(); // you should never actually encounter these
		
		TLAParser.lookaheadOperatorFunctionOrModuleDefinition(tokens.listIterator(), operatorDefinitions, functionDefinitions, instanceDefinitions, -1);
		
		return new Algorithm(name, variables, macros, procedures, operatorDefinitions,
				functionDefinitions, processes);
	}
	
	public Algorithm getResult() {
		return result;
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.Uniprocess ua) throws PGoException {
		SingleProcess proc = new SingleProcess(parseProcessBody(ua.body));
		result = convertAlgorithm(ua.name, ua.decls, ua.macros, ua.prcds, ua.defs.tokens, proc);
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
			procs.add(new PcalProcess(new VariableDecl(p.name, !p.isEq, parseTLAExpression(p.id)), f, convertVarDecls(p.decls), stmts));
		}
		
		MultiProcess proc = new MultiProcess(procs);

		result = convertAlgorithm(ma.name, ma.decls, ma.macros, ma.prcds, ma.defs.tokens, proc);
		
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
		if(minusLabels.contains(ls.label)) {
			modifier = Label.Modifier.MINUS;
		}else if(plusLabels.contains(ls.label)) {
			modifier = Label.Modifier.PLUS;
		}
		
		return Collections.singletonList(new LabeledStatements(new Label(ls.label, modifier), statements));
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
		return Collections.singletonList(new While(parseTLAExpression(w.test), statements));
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.Assign as) throws PGoException {
		List<Statement> statements = new ArrayList<>();
		for(AST.SingleAssign a : (Vector<AST.SingleAssign>)as.ass) {
			statements.addAll(PcalASTUtil.accept(a, this));
		}
		return statements;
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.SingleAssign sa) throws PGoException {
		List<TLAToken> lhsTok = new ArrayList<>();
		lhsTok.add(new TLAToken(sa.lhs.var, sa.lhs.col, TLAToken.IDENT, sa.lhs.line));
		for(Vector<TLAToken> tokList : (Vector<Vector<TLAToken>>)sa.lhs.sub.tokens){
			lhsTok.addAll(tokList);
		}
		PGoTLAExpression lhs = TLAParser.readExpression(lhsTok.listIterator());
		return Collections.singletonList(new Assignment(lhs, parseTLAExpression(sa.rhs)));
	}

	@Override
	public List<Statement> visit(AST.Lhs lhs) throws PGoTransException {
		throw new RuntimeException("unreachable");
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.If ifast) throws PGoException{
		return Collections.singletonList(new If(parseTLAExpression(ifast.test),
				parseStatementSequence(ifast.Then), parseStatementSequence(ifast.Else)));
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.Either ei) throws PGoException {
		List<List<Statement>> cases = new ArrayList<>();
		for(Vector<AST> statements : (Vector<Vector<AST>>)ei.ors) {
			cases.add(parseStatementSequence(statements));
		}
		return Collections.singletonList(new Either(cases));
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.With with) throws PGoException {
		return Collections.singletonList(new With(new VariableDecl(with.var, !with.isEq, parseTLAExpression(with.exp)),
				parseStatementSequence(with.Do)));
	}

	@Override
	public List<Statement> visit(AST.When when) throws PGoException {
		return Collections.singletonList(new Await(parseTLAExpression(when.exp)));
	}

	@Override
	public List<Statement> visit(AST.PrintS ps) throws PGoException {
		return Collections.singletonList(new Print(parseTLAExpression(ps.exp)));
	}

	@Override
	public List<Statement> visit(AST.Assert as) throws PGoException {
		return Collections.singletonList(new Assert(parseTLAExpression(as.exp)));
	}

	@Override
	public List<Statement> visit(AST.Skip s) throws PGoTransException {
		return Collections.singletonList(new Skip());
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
		return Collections.singletonList(new If(parseTLAExpression(lif.test), yes, no));
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
		return Collections.singletonList(new Either(cases));
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
		return Collections.singletonList(new Call(c.to, args));
	}

	@Override
	public List<Statement> visit(AST.Return r) throws PGoTransException {
		return Collections.singletonList(new Return());
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<Statement> visit(AST.CallReturn cr) throws PGoException {
		List<Statement> statements = new ArrayList<>();
		List<PGoTLAExpression> args = new ArrayList<>();
		for(TLAExpr e : (Vector<TLAExpr>)cr.args) {
			args.add(parseTLAExpression(e));
		}
		statements.add(new Call(cr.to, args));
		statements.add(new Return());
		return statements;
	}

	@Override
	public List<Statement> visit(AST.Goto g) throws PGoTransException {
		return Collections.singletonList(new Goto(g.to));
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
		return Collections.singletonList(new MacroCall(m.name, args));
	}

}
