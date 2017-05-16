package pgo.model.tla;

import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

import pgo.model.golang.SimpleExpression;
import pgo.model.golang.Statement;

/**
 * Converts the TLA ast generated by the TLAExprParser into GoAST
 *
 */
public class TLAExprToGo {
	
	private Vector<Statement> stmts;
	private Set<String> imports;

	public TLAExprToGo(Vector<PGoTLA> tla) {
		stmts = new Vector<>();
		imports = new HashSet<>();
		convert(tla);
	}
	
	public TLAExprToGo(PGoTLA tla) {
		convert(tla);
	}

	public SimpleExpression toSimpleExpression() {
		// TODO Auto-generated method stub
		return null;
	}

	public Vector<Statement> getStatements() {
		return stmts;
	}
	
	public Set<String> getImports() {
		return imports;
	}
	
	/**
	 * Takes PGoTLA ast tree and converts it to Go statement
	 * 
	 * TODO probably want to take the tokens into a class TLAExprToGo. Then support things like getEquivStatement() to get the
	 * equivalent go expr to refer to the equivalent data in the pluscal, and getInit() to get any initialization code to
	 * generate that data. Constructor of this class may need to know what local variable names are available
	 * 
	 * @param ptla
	 * @return
	 */
	private void convert(Vector<PGoTLA> ptla) {
		for (PGoTLA tla : ptla) {
			stmts.addAll(tla.toStatements());
			imports.addAll(tla.getImports());
		}
	}
	
	private void convert(PGoTLA tla) {
		stmts = tla.toStatements();
		imports = tla.getImports();
	}
}
