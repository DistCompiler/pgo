package pgo.model.type;

public class PGoTypeHasVariableVisitor extends PGoTypeVisitor<Boolean, RuntimeException> {
	private final PGoTypeVariable typeVariable;

	public PGoTypeHasVariableVisitor(PGoTypeVariable typeVariable) {
		this.typeVariable = typeVariable;
	}

	@Override
	public Boolean visit(PGoTypeAbstractRecord pGoTypeAbstractRecord) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
			return pGoTypeVariable.equals(typeVariable);
	}

	@Override
	public Boolean visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		return pGoTypeTuple.getElementTypes().stream().anyMatch(t -> t.accept(this));
	}

	@Override
	public Boolean visit(PGoTypeString pGoTypeString) throws RuntimeException {
        return false;
	}

	@Override
	public Boolean visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
        return pGoTypeSet.getElementType().accept(this);
	}

	@Override
	public Boolean visit(PGoTypeNonEnumerableSet pGoTypeNonEnumerableSet) throws RuntimeException {
		return pGoTypeNonEnumerableSet.getElementType().accept(this);
	}

	@Override
	public Boolean visit(PGoTypeBool pGoTypeBool) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PGoTypeReal pGoTypeReal) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PGoTypeFunction pGoTypeFunction) throws RuntimeException {
		return pGoTypeFunction.getParamTypes().stream().anyMatch(p -> p.accept(this)) ||
				pGoTypeFunction.getReturnType().accept(this);
	}

	@Override
	public Boolean visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		return pGoTypeChan.getElementType().accept(this);
	}

	@Override
	public Boolean visit(PGoTypeInt pGoTypeInt) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PGoTypeInterface pGoTypeInterface) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PGoTypeMap pGoTypeMap) throws RuntimeException {
		return pGoTypeMap.getKeyType().accept(this) || pGoTypeMap.getValueType().accept(this);
	}

	@Override
	public Boolean visit(PGoTypeSlice pGoTypeSlice) throws RuntimeException {
		return pGoTypeSlice.getElementType().accept(this);
	}

	@Override
	public Boolean visit(PGoTypeProcedure pGoTypeProcedure) throws RuntimeException {
		return pGoTypeProcedure.getParamTypes().stream().anyMatch(p -> p.accept(this));
	}

	@Override
	public Boolean visit(PGoTypeConcreteRecord pGoTypeConcreteRecord) throws RuntimeException {
		return pGoTypeConcreteRecord.getFields().stream().anyMatch(f -> f.getType().accept(this));
	}
}
