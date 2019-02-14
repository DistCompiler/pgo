package pgo.model.type;

import java.util.Set;

public class PGoTypeVariableCollectionVisitor extends PGoTypeVisitor<Void, RuntimeException> {
	private final Set<PGoTypeVariable> output;

	public PGoTypeVariableCollectionVisitor(Set<PGoTypeVariable> output) {
		this.output = output;
	}

	@Override
	public Void visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		output.add(pGoTypeVariable);
		return null;
	}

	@Override
	public Void visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		for (PGoType elementType : pGoTypeTuple.getElementTypes()) {
			elementType.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PGoTypeString pGoTypeString) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
		pGoTypeSet.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTypeNonEnumerableSet pGoTypeNonEnumerableSet) throws RuntimeException {
		pGoTypeNonEnumerableSet.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTypeBool pGoTypeBool) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PGoTypeReal pGoTypeReal) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PGoTypeFunction pGoTypeFunction) throws RuntimeException {
		for (PGoType paramType : pGoTypeFunction.getParamTypes()) {
			paramType.accept(this);
		}
		pGoTypeFunction.getReturnType().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		pGoTypeChan.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTypeInt pGoTypeInt) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PGoTypeInterface pGoTypeInterface) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PGoTypeMap pGoTypeMap) throws RuntimeException {
		pGoTypeMap.getKeyType().accept(this);
		pGoTypeMap.getValueType().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTypeSlice pGoTypeSlice) throws RuntimeException {
		pGoTypeSlice.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTypeProcedure pGoTypeProcedure) throws RuntimeException {
		for (PGoType paramType : pGoTypeProcedure.getParamTypes()) {
			paramType.accept(this);
		}
		return null;
	}
}
