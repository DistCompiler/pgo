package pgo.trans.passes.expansion;

import pgo.errors.IssueContext;
import pgo.model.pcal.*;

import java.util.*;

public class PlusCalProcessesMacroExpansionVisitor extends PlusCalProcessesVisitor<PlusCalProcesses, RuntimeException> {

	private IssueContext ctx;
	private Map<String, PlusCalMacro> macros;

	public PlusCalProcessesMacroExpansionVisitor(IssueContext ctx, Map<String, PlusCalMacro> macros) {
		this.ctx = ctx;
		this.macros = macros;
	}

	@Override
	public PlusCalProcesses visit(PlusCalSingleProcess singleProcess) throws RuntimeException {
		PlusCalMacroExpansionVisitor v = new PlusCalMacroExpansionVisitor(ctx, macros, new HashSet<>(), new HashMap<>());
		List<PlusCalStatement> stmts = new ArrayList<>();
		for(PlusCalStatement stmt : singleProcess.getBody()) {
			for(PlusCalStatement s : stmt.accept(v)) {
				stmts.add(s);
			}
		}
		return new PlusCalSingleProcess(singleProcess.getLocation(), stmts);
	}

	@Override
	public PlusCalProcesses visit(PlusCalMultiProcess multiProcess) throws RuntimeException {
		PlusCalMacroExpansionVisitor v = new PlusCalMacroExpansionVisitor(ctx, macros, new HashSet<>(), new HashMap<>());
		List<PlusCalProcess> procs = new ArrayList<>();
		for(PlusCalProcess proc : multiProcess.getProcesses()) {
			List<PlusCalStatement> stmts = new ArrayList<>();
			for(PlusCalStatement stmt : proc.getBody()) {
				for(PlusCalStatement s : stmt.accept(v)) {
					stmts.add(s);
				}
			}
			procs.add(new PlusCalProcess(
					proc.getLocation(), proc.getName(), proc.getFairness(), proc.getVariables(), stmts));
		}
		return new PlusCalMultiProcess(multiProcess.getLocation(), procs);
	}

}
