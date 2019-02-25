package pgo.model.type;

import java.util.stream.Collectors;

public class PGoTypeCopyVisitor extends PGoTypeVisitor<PGoType, RuntimeException> {
	@Override
	public PGoType visit(PGoTypeAbstractRecord pGoTypeAbstractRecord) throws RuntimeException {
		return pGoTypeAbstractRecord;
	}

	@Override
	public PGoType visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		return pGoTypeVariable;
	}

	@Override
	public PGoType visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		return new PGoTypeTuple(
				pGoTypeTuple.getElementTypes().stream().map(t -> t.accept(this)).collect(Collectors.toList()),
				pGoTypeTuple.getOrigins());
	}

	@Override
	public PGoType visit(PGoTypeString pGoTypeString) throws RuntimeException {
		return pGoTypeString;
	}

	@Override
	public PGoType visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
		return new PGoTypeSet(pGoTypeSet.getElementType().accept(this), pGoTypeSet.getOrigins());
	}

	@Override
	public PGoType visit(PGoTypeNonEnumerableSet pGoTypeNonEnumerableSet) throws RuntimeException {
		return new PGoTypeNonEnumerableSet(
				pGoTypeNonEnumerableSet.getElementType().accept(this), pGoTypeNonEnumerableSet.getOrigins());
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
		return new PGoTypeFunction(
				pGoTypeFunction.getParamTypes().stream().map(p -> p.accept(this)).collect(Collectors.toList()),
				pGoTypeFunction.getReturnType().accept(this),
				pGoTypeFunction.getOrigins());
	}

	@Override
	public PGoType visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		return new PGoTypeChan(pGoTypeChan.getElementType().accept(this), pGoTypeChan.getOrigins());
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
		return new PGoTypeMap(
				pGoTypeMap.getKeyType().accept(this),
				pGoTypeMap.getValueType().accept(this),
				pGoTypeMap.getOrigins());
	}

	@Override
	public PGoType visit(PGoTypeSlice pGoTypeSlice) throws RuntimeException {
		return new PGoTypeSlice(pGoTypeSlice.getElementType().accept(this), pGoTypeSlice.getOrigins());
	}

	@Override
	public PGoType visit(PGoTypeProcedure pGoTypeProcedure) throws RuntimeException {
		return new PGoTypeProcedure(
				pGoTypeProcedure.getParamTypes().stream().map(p -> p.accept(this)).collect(Collectors.toList()),
				pGoTypeProcedure.getOrigins());
	}

	@Override
	public PGoType visit(PGoTypeRecord pGoTypeRecord) throws RuntimeException {
		return new PGoTypeRecord(
				pGoTypeRecord.getFields()
						.stream()
						.map(f -> new PGoTypeRecord.Field(f.getName(), f.getType()))
						.collect(Collectors.toList()),
				pGoTypeRecord.getOrigins());
	}
}
