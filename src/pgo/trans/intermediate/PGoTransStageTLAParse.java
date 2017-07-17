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
				convert(ua.defs);
				super.visit(ua);
			}

			@Override
			protected void visit(Multiprocess ma) throws PGoTransException {
				convert(ma.defs);
				super.visit(ma);
			}

			@Override
			protected void visit(Process p) throws PGoTransException {
				convert(p.id);
				super.visit(p);
			}

			@Override
			protected void visit(VarDecl v) throws PGoTransException {
				convert(v.val);
				super.visit(v);
			}

			@Override
			protected void visit(PVarDecl v) throws PGoTransException {
				visit(v.toVarDecl());
			}

			@Override
			protected void visit(While w) throws PGoTransException {
				convert(w.test);
				super.visit(w);
			}

			@Override
			protected void visit(SingleAssign sa) throws PGoTransException {
				convert(sa.rhs);
				super.visit(sa);
			}

			@Override
			protected void visit(If i) throws PGoTransException {
				convert(i.test);
				super.visit(i);
			}

			@Override
			protected void visit(With w) throws PGoTransException {
				convert(w.exp);
				super.visit(w);
			}

			@Override
			protected void visit(When w) throws PGoTransException {
				convert(w.exp);
				super.visit(w);
			}

			@Override
			protected void visit(PrintS ps) throws PGoTransException {
				convert(ps.exp);
				super.visit(ps);
			}

			@Override
			protected void visit(Assert a) throws PGoTransException {
				convert(a.exp);
				super.visit(a);
			}

			@Override
			protected void visit(LabelIf lif) throws PGoTransException {
				convert(lif.test);
				super.visit(lif);
			}

			@Override
			protected void visit(Call c) throws PGoTransException {
				for (TLAExpr e : (Vector<TLAExpr>) c.args) {
					convert(e);
				}
				super.visit(c);
			}

			@Override
			protected void visit(CallReturn cr) throws PGoTransException {
				for (TLAExpr e : (Vector<TLAExpr>) cr.args) {
					convert(e);
				}
				super.visit(cr);
			}

			@Override
			protected void visit(MacroCall mc) throws PGoTransException {
				for (TLAExpr e : (Vector<TLAExpr>) mc.args) {
					convert(e);
				}
				super.visit(mc);
			}

		}.getResult(data.ast);
	}

	// Converts the TLAExpr to PGoTLA using the TLAExprParser
	private void convert(TLAExpr e) throws PGoTransException {
		if (e != null) {
			Vector<PGoTLA> v;
			if (e.getOrigin() != null) {
				v = new TLAExprParser(e, e.getOrigin().getBegin().getLine()).getResult();
			} else {
				v = new TLAExprParser(e, -1).getResult();
			}
			assert (v.size() <= 1);
			if (!v.isEmpty()) {
				data.tlaToAST.put(e, v.get(0));
			}
		}
	}
}
