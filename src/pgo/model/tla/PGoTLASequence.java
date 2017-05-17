package pgo.model.tla;

import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.golang.FunctionCall;
import pgo.model.golang.Statement;

/**
 * Represents a sequence "a .. b" in TLA
 *
 */
public class PGoTLASequence extends PGoTLA {

	private PGoTLA start;

	private PGoTLA end;

	public PGoTLASequence(PGoTLA prev, PGoTLA next, int line) {
		super(line);
		start = prev;
		end = next;
	}

	public PGoTLA getStart() {
		return start;
	}

	public PGoTLA getEnd() {
		return end;
	}

	protected Vector<Statement> toStatements() {
		Vector<Statement> ret = new Vector<>();

		Vector<Statement> startRes = this.getStart().toStatements();
		Vector<Statement> endRes = this.getEnd().toStatements();

		// comparators operations should just be a single Expression
		assert (startRes.size() == 1);
		assert (endRes.size() == 1);
		assert (startRes.get(0) instanceof Expression);
		assert (endRes.get(0) instanceof Expression);

		Vector<Expression> args = new Vector<Expression>();
		args.add((Expression) startRes.get(0));
		args.add((Expression) endRes.get(0));

		FunctionCall fc = new FunctionCall("pgoutil.Sequence", args);
		ret.add(fc);

		return ret;
	}
	
	protected Set<String> getImports() {
		Set<String> ret = new HashSet<>();
		ret.add("pgoutil");
		ret.addAll(this.getStart().getImports());
		ret.addAll(this.getEnd().getImports());
		return ret;
	}

	public String toString() {
		return "PGoTLASequence (" + this.getLine() + "): (" + start.toString() + ") .. ("
				+ end.toString() + ")";
	}
}
