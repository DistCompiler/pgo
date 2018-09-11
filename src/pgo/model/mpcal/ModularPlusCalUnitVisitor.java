package pgo.model.mpcal;

import pgo.model.pcal.PlusCalMacro;
import pgo.model.pcal.PlusCalMultiProcess;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalSingleProcess;
import pgo.model.tla.TLAUnit;

public abstract class ModularPlusCalUnitVisitor<T, E extends Throwable> {
	public abstract T visit(TLAUnit tlaUnit) throws E;
	public abstract T visit(ModularPlusCalMappingMacro modularPlusCalMappingMacro) throws E;
	public abstract T visit(ModularPlusCalArchetype modularPlusCalArchetype) throws E;
	public abstract T visit(PlusCalMacro plusCalMacro) throws E;
	public abstract T visit(PlusCalProcedure plusCalProcedure) throws E;
	public abstract T visit(ModularPlusCalInstance modularPlusCalInstance) throws E;
	public abstract T visit(PlusCalSingleProcess plusCalSingleProcess) throws E;
	public abstract T visit(PlusCalMultiProcess plusCalMultiProcess) throws E;
}
