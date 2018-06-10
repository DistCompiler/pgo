package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.Macro;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.PcalProcess;
import pgo.model.pcal.Processes;
import pgo.model.pcal.ProcessesVisitor;
import pgo.model.pcal.SingleProcess;
import pgo.model.pcal.Statement;

public class PlusCalProcessesMacroExpansionVisitor extends ProcessesVisitor<Processes, RuntimeException> {

	private IssueContext ctx;
	private Map<String, Macro> macros;

	public PlusCalProcessesMacroExpansionVisitor(IssueContext ctx, Map<String, Macro> macros) {
		this.ctx = ctx;
		this.macros = macros;
	}

	@Override
	public Processes visit(SingleProcess singleProcess) throws RuntimeException {
		PlusCalMacroExpansionVisitor v = new PlusCalMacroExpansionVisitor(ctx, macros, new HashSet<>(), new HashMap<>());
		List<LabeledStatements> stmts = new ArrayList<>();
		for(LabeledStatements stmt : singleProcess.getLabeledStatements()) {
			for(Statement s : stmt.accept(v)) {
				stmts.add((LabeledStatements)s);
			}
		}
		return new SingleProcess(singleProcess.getLocation(), stmts);
	}

	@Override
	public Processes visit(MultiProcess multiProcess) throws RuntimeException {
		PlusCalMacroExpansionVisitor v = new PlusCalMacroExpansionVisitor(ctx, macros, new HashSet<>(), new HashMap<>());
		List<PcalProcess> procs = new ArrayList<>();
		for(PcalProcess proc : multiProcess.getProcesses()) {
			List<LabeledStatements> stmts = new ArrayList<>();
			for(LabeledStatements stmt : proc.getLabeledStatements()) {
				for(Statement s : stmt.accept(v)) {
					stmts.add((LabeledStatements)s);
				}
			}
			procs.add(new PcalProcess(proc.getLocation(), proc.getName(), proc.getFairness(), proc.getVariables(), stmts));
		}
		return new MultiProcess(multiProcess.getLocation(), procs);
	}

}
