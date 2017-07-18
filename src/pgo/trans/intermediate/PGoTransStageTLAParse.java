package pgo.trans.intermediate;

import java.util.Vector;

import pcal.AST.*;
import pcal.AST.Process;
import pcal.TLAExpr;
import pgo.model.tla.PGoTLA;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;
import pgo.util.PcalASTUtil;

/**
 * Parses all TLAExprs in the PlusCal ast into PGoTLA ast representations, and
 * stores them in the tlaToAST map in the intermediate data.
 *
 */
public class PGoTransStageTLAParse {

	// contains the tlaToAST map which we populate
	PGoTransIntermediateData data;

	public PGoTransStageTLAParse(PGoTransStageInitParse s) throws PGoTransException {
		this.data = s.data;
		parseTLA();
	}

	public void parseTLA() throws PGoTransException {
		new PcalASTUtil.Walker<Void>() {

			@Override
			public void init() {
			}

			@Override
			protected void visit(Uniprocess ua) throws PGoTransException {
				convert(ua.defs, ua.line);
				super.visit(ua);
			}

			@Override
			protected void visit(Multiprocess ma) throws PGoTransException {
				convert(ma.defs, ma.line);
				super.visit(ma);
			}

			@Override
			protected void visit(Process p) throws PGoTransException {
				convert(p.id, p.line);
				super.visit(p);
			}

			@Override
			protected void visit(VarDecl v) throws PGoTransException {
				convert(v.val, v.line);
				super.visit(v);
			}

			@Override
			protected void visit(PVarDecl v) throws PGoTransException {
				visit(v.toVarDecl());
			}

			@Override
			protected void visit(While w) throws PGoTransException {
				convert(w.test, w.line);
				super.visit(w);
			}

			@Override
			protected void visit(SingleAssign sa) throws PGoTransException {
				convert(sa.rhs, sa.line);
				super.visit(sa);
			}

			@Override
			protected void visit(If i) throws PGoTransException {
				convert(i.test, i.line);
				super.visit(i);
			}

			@Override
			protected void visit(With w) throws PGoTransException {
				convert(w.exp, w.line);
				super.visit(w);
			}

			@Override
			protected void visit(When w) throws PGoTransException {
				convert(w.exp, w.line);
				super.visit(w);
			}

			@Override
			protected void visit(PrintS ps) throws PGoTransException {
				convert(ps.exp, ps.line);
				super.visit(ps);
			}

			@Override
			protected void visit(Assert a) throws PGoTransException {
				convert(a.exp, a.line);
				super.visit(a);
			}

			@Override
			protected void visit(LabelIf lif) throws PGoTransException {
				convert(lif.test, lif.line);
				super.visit(lif);
			}

			@Override
			protected void visit(Call c) throws PGoTransException {
				for (TLAExpr e : (Vector<TLAExpr>) c.args) {
					convert(e, c.line);
				}
				super.visit(c);
			}

			@Override
			protected void visit(CallReturn cr) throws PGoTransException {
				for (TLAExpr e : (Vector<TLAExpr>) cr.args) {
					convert(e, cr.line);
				}
				super.visit(cr);
			}

			@Override
			protected void visit(MacroCall mc) throws PGoTransException {
				for (TLAExpr e : (Vector<TLAExpr>) mc.args) {
					convert(e, mc.line);
				}
				super.visit(mc);
			}

		}.getResult(data.ast);
	}

	// Converts the TLAExpr to PGoTLA using the TLAExprParser
	private void convert(TLAExpr e, int line) throws PGoTransException {
		if (e != null) {
			Vector<PGoTLA> v = new TLAExprParser(e, line).getResult();
			assert (v.size() <= 1);
			if (!v.isEmpty()) {
				data.putPGoTLA(e, v.get(0));
			}
		}
	}
}
