package pgo.model.mpcal;

import pgo.model.pcal.*;
import pgo.model.tla.TLAUnit;

public abstract class ModularPlusCalBlockVisitor<T, E extends Throwable> {
	public abstract T visit(ModularPlusCalBlock modularPlusCalBlock) throws E;
	public abstract T visit(TLAUnit tlaUnit) throws E;
	public abstract T visit(ModularPlusCalMappingMacro modularPlusCalMappingMacro) throws E;
	public abstract T visit(ModularPlusCalArchetype modularPlusCalArchetype) throws E;
	public abstract T visit(PlusCalMacro plusCalMacro) throws E;
	public abstract T visit(PlusCalProcedure plusCalProcedure) throws E;
	public abstract T visit(ModularPlusCalInstance modularPlusCalInstance) throws E;
	public abstract T visit(PlusCalSingleProcess plusCalSingleProcess) throws E;
	public abstract T visit(PlusCalMultiProcess plusCalMultiProcess) throws E;
}
