package pgo.model.type;

import java.util.stream.Collectors;

public class PGoTypeVariableSubstitutionVisitor extends PGoTypeVisitor<PGoType, RuntimeException> {
	protected final PGoTypeSubstitution substitution;

	public PGoTypeVariableSubstitutionVisitor(PGoTypeSubstitution substitution) {
		this.substitution = substitution;
	}

	@Override
	public PGoType visit(PGoTypeAbstractRecord pGoTypeAbstractRecord) throws RuntimeException {
		return pGoTypeAbstractRecord;
	}

	@Override
	public PGoType visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		PGoType old = pGoTypeVariable;
		PGoType sub = substitution.getOrDefault(pGoTypeVariable, pGoTypeVariable);
		while (!sub.equals(old)) {
			old = sub;
			sub = sub.accept(this);
		}
		return sub;
	}

	@Override
	public PGoType visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		pGoTypeTuple.setElementTypes(
				pGoTypeTuple.getElementTypes().stream().map(t -> t.accept(this)).collect(Collectors.toList()));
		return pGoTypeTuple;
	}

	@Override
	public PGoType visit(PGoTypeString pGoTypeString) throws RuntimeException {
		return pGoTypeString;
	}

	@Override
	public PGoType visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
		pGoTypeSet.setElementType(pGoTypeSet.getElementType().accept(this));
		return pGoTypeSet;
	}

	@Override
	public PGoType visit(PGoTypeNonEnumerableSet pGoTypeNonEnumerableSet) throws RuntimeException {
		pGoTypeNonEnumerableSet.setElementType(pGoTypeNonEnumerableSet.getElementType().accept(this));
		return pGoTypeNonEnumerableSet;
	}

	@Override
	public PGoType visit(PGoTypeBool pGoTypeBool) throws RuntimeException {
		return pGoTypeBool;
	}

	@Override
	public PGoType visit(PGoTypeReal pGoTypeReal) throws RuntimeException {
		return pGoTypeReal;
	}

	@Override
	public PGoType visit(PGoTypeFunction pGoTypeFunction) throws RuntimeException {
		pGoTypeFunction.setParamTypes(
				pGoTypeFunction.getParamTypes().stream().map(t -> t.accept(this)).collect(Collectors.toList()));
		pGoTypeFunction.setReturnType(pGoTypeFunction.getReturnType().accept(this));
		return pGoTypeFunction;
	}

	@Override
	public PGoType visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		pGoTypeChan.setElementType(pGoTypeChan.getElementType().accept(this));
		return pGoTypeChan;
	}

	@Override
	public PGoType visit(PGoTypeInt pGoTypeInt) throws RuntimeException {
		return pGoTypeInt;
	}

	@Override
	public PGoType visit(PGoTypeInterface pGoTypeInterface) throws RuntimeException {
		return pGoTypeInterface;
	}

	@Override
	public PGoType visit(PGoTypeMap pGoTypeMap) throws RuntimeException {
		pGoTypeMap.setKeyType(pGoTypeMap.getKeyType().accept(this));
		pGoTypeMap.setValueType(pGoTypeMap.getValueType().accept(this));
		return pGoTypeMap;
	}

	@Override
	public PGoType visit(PGoTypeSlice pGoTypeSlice) throws RuntimeException {
		pGoTypeSlice.setElementType(pGoTypeSlice.getElementType().accept(this));
		return pGoTypeSlice;
	}

	@Override
	public PGoType visit(PGoTypeProcedure pGoTypeProcedure) throws RuntimeException {
		pGoTypeProcedure.setParamTypes(
				pGoTypeProcedure.getParamTypes().stream().map(t -> t.accept(this)).collect(Collectors.toList()));
		return pGoTypeProcedure;
	}

	@Override
	public PGoType visit(PGoTypeRecord pGoTypeRecord) throws RuntimeException {
		pGoTypeRecord.setFields(
				pGoTypeRecord.getFields()
						.stream()
						.map(f -> new PGoTypeRecord.Field(f.getName(), f.getType().accept(this)))
						.collect(Collectors.toList()));
		return pGoTypeRecord;
	}
}
