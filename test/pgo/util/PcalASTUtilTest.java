package pgo.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Vector;

import org.junit.Before;
import org.junit.Test;

import pcal.AST;
import pcal.AST.Assign;
import pcal.AST.Call;
import pcal.AST.LabeledStmt;
import pcal.AST.Lhs;
import pcal.AST.Macro;
import pcal.AST.MacroCall;
import pcal.AST.Multiprocess;
import pcal.AST.PVarDecl;
import pcal.AST.PrintS;
import pcal.AST.Procedure;
import pcal.AST.Process;
import pcal.AST.SingleAssign;
import pcal.AST.VarDecl;
import pcal.AST.While;

public class PcalASTUtilTest {

	private AST ast;

	@Before
	public void makeAST() {

		Multiprocess a = new Multiprocess();
		a.decls = new Vector();
		VarDecl v = new VarDecl();
		v.var = "var";
		a.decls.add(v);
		v = new VarDecl();
		v.var = "ret";
		a.decls.add(v);

		a.prcds = new Vector();
		a.macros = new Vector();
		a.procs = new Vector();

		// Add a procedure with while loop of print and assignment to "ret" and
		// an assignment to "var" outside loop
		Procedure prc = new Procedure();
		prc.name = "foo";
		prc.params = new Vector();
		PVarDecl pvar = new PVarDecl();
		pvar.var = "param1";
		prc.params.add(pvar);
		pvar = new PVarDecl();
		pvar.var = "param2";
		prc.params.add(pvar);

		pvar = new PVarDecl();
		pvar.var = "prcVar";
		prc.decls = new Vector();
		prc.decls.add(pvar);
		prc.body = new Vector();

		LabeledStmt ls = new LabeledStmt();
		ls.stmts = new Vector();
		While w = new While();
		w.unlabDo = new Vector();
		w.unlabDo.add(new PrintS());
		Assign ass = new Assign();
		ass.ass = new Vector();
		SingleAssign sa = new SingleAssign();
		sa.lhs = new Lhs();
		sa.lhs.var = "ret";
		ass.ass.add(sa);
		w.unlabDo.add(ass);
		ls.stmts.add(w);

		prc.body.add(ls);

		ls = new LabeledStmt();
		ls.stmts = new Vector();
		ass = new Assign();
		ass.ass = new Vector();
		sa = new SingleAssign();
		sa.lhs = new Lhs();
		sa.lhs.var = "var";
		prc.body.add(ls);

		a.prcds.add(prc);

		// Add a macro with assignment to var

		Macro m = new Macro();
		m.name = "bar";
		m.params = new Vector();
		m.params.add("mp1");
		m.body = new Vector();
		ass = new Assign();
		ass.ass = new Vector();
		sa = new SingleAssign();
		sa.lhs = new Lhs();
		sa.lhs.var = "var";
		ass.ass.add(sa);
		m.body.add(ass);

		a.macros.add(m);

		// Create a process that assigns to ret and calls on foo
		Process ps = new Process();
		ps.name = "proc1";
		ps.body = new Vector();

		ass = new Assign();
		sa = new SingleAssign();
		sa.lhs = new Lhs();
		sa.lhs.var = "ret";
		ass.ass = new Vector();
		ass.ass.add(sa);
		ps.body.add(ass);

		Call call = new Call();
		call.args = new Vector();
		call.to = "foo";
		ps.body.add(call);

		a.procs.add(ps);

		// Create a process that calls macro bar
		ps = new Process();
		ps.name = "proc2";
		ps.body = new Vector();

		MacroCall mc = new MacroCall();
		mc.name = "bar";
		ps.body.add(mc);

		a.procs.add(ps);

		ast = a;
	}

	@Test
	public void testContainsReference() {
		Vector<AST> body = new Vector<AST>();
		body.add(ast);

		assertTrue(PcalASTUtil.containsAssignmentToVar(body, "ret"));
		assertTrue(PcalASTUtil.containsAssignmentToVar(body, "var"));
		assertFalse(PcalASTUtil.containsAssignmentToVar(body, "foo"));
		assertFalse(PcalASTUtil.containsAssignmentToVar(body, "bar"));
		assertFalse(PcalASTUtil.containsAssignmentToVar(body, "proc1"));
		assertFalse(PcalASTUtil.containsAssignmentToVar(body, "none"));
	}

	@Test
	public void testEarlyTermWalker() {
		// testing that the early termination works
		assertEquals(3, (int) new PcalASTUtil.Walker<Integer>() {

			@Override
			protected void init() {
				result = 0;
			}

			@Override
			protected void walk(AST a) {
				result++;
				if (result == 3) {
					earlyTerm = true;
				}
				super.walk(a);
			}
		}.getResult(ast));

		// If we can reach 3, see that 2 works as well
		assertEquals(2, (int) new PcalASTUtil.Walker<Integer>() {

			@Override
			protected void init() {
				result = 0;
			}

			@Override
			protected void walk(AST a) {
				result++;
				if (result == 2) {
					earlyTerm = true;
				}
				super.walk(a);
			}
		}.getResult(ast));
	}

	@Test
	public void testFindFunctionCalls() {
		Vector<String> expected = new Vector<String>();
		Vector<AST> body = new Vector<AST>();
		body.add((AST) ((Multiprocess) ast).prcds.get(0));

		assertEquals(expected, PcalASTUtil.collectFunctionCalls(body));

		body.clear();
		expected.add("foo");
		body.add((AST) ((Multiprocess) ast).procs.get(0));
		assertEquals(expected, PcalASTUtil.collectFunctionCalls(body));

		body.clear();
		expected.clear();
		expected.add("bar");
		body.add((AST) ((Multiprocess) ast).procs.get(1));
		assertEquals(expected, PcalASTUtil.collectFunctionCalls(body));

		body.clear();
		expected.clear();
		expected.add("foo");
		expected.add("bar");
		body.add(ast);
		Vector<String> vs = PcalASTUtil.collectFunctionCalls(body);
		assertEquals(expected.size(), vs.size());
		assertTrue(expected.containsAll(vs));
	}
}
