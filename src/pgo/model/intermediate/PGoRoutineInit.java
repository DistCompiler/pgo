package pgo.model.intermediate;

import pcal.AST.Process;
import pcal.TLAExpr;

/**
 * Intermediate representation of the initialization code for a process that
 * will be spawned as a goroutine.
 *
 */
public class PGoRoutineInit {

	// The name of the goroutine
	private String name;
	// Whether the process id was a simple assignment
	private boolean isSimpleInit;
	// The process id assignment code
	private TLAExpr init;

	public String getName() {
		return name;
	}

	public boolean getIsSimpleInit() {
		return isSimpleInit;
	}

	public TLAExpr getInitTLA() {
		return init;
	}

	public static PGoRoutineInit convert(Process p) {
		PGoRoutineInit r = new PGoRoutineInit();
		r.name = p.name;
		r.isSimpleInit = p.isEq;
		r.init = p.id;

		return r;
	}

}
