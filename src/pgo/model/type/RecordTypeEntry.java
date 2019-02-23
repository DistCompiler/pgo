package pgo.model.type;

import pgo.InternalCompilerError;

import java.util.*;
import java.util.stream.Collectors;

abstract class RecordTypeEntry {
	abstract boolean hasVariable(PGoTypeVariable variable);

	RecordTypeEntry unify(PGoTypeSolver solver, RecordTypeEntry entry) throws UnificationException {
		if (entry instanceof Abstract) {
			return unify(solver, (Abstract) entry);
		}
		if (entry instanceof Concrete) {
			return unify(solver, (Concrete) entry);
		}
		throw new InternalCompilerError();
	}

	abstract RecordTypeEntry unify(PGoTypeSolver solver, Abstract entry) throws UnificationException;
	abstract Concrete unify(PGoTypeSolver solver, Concrete entry) throws UnificationException;

	static class Abstract extends RecordTypeEntry {
		private final Map<String, PGoType> fields;

		Abstract() {
			this(new HashMap<>());
		}

		Abstract(Map<String, PGoType> fields) {
			this.fields = fields;
		}

		@Override
		boolean hasVariable(PGoTypeVariable variable) {
			PGoTypeHasVariableVisitor visitor = new PGoTypeHasVariableVisitor(variable);
			return fields.values().stream().anyMatch(t -> t.accept(visitor));
		}

		@Override
		RecordTypeEntry unify(PGoTypeSolver solver, Abstract entry) throws UnificationException {
			Map<String, PGoType> fields = new HashMap<>(this.fields);
			entry.fields.forEach((k, v) -> {
				if (fields.containsKey(k)) {
					solver.addFirst(new PGoTypeMonomorphicConstraint(v, v, fields.get(k)));
				} else {
					fields.put(k, v);
				}
			});
			return new Abstract(fields);
		}

		@Override
		Concrete unify(PGoTypeSolver solver, Concrete entry) throws UnificationException {
			if (entry.record.getFields().size() < fields.size() ||
					entry.record.getFields().stream().anyMatch(f -> !fields.containsKey(f.getName()))) {
				List<PGoTypeConcreteRecord.Field> fs = new ArrayList<>();
				fields.forEach((k, v) -> fs.add(new PGoTypeConcreteRecord.Field(k, v)));
				throw new UnificationException(new UnsatisfiableConstraintIssue(
						entry.record,
						new PGoTypeConcreteRecord(
								fs,
								fs.stream()
										.flatMap(f -> f.getType().getOrigins().stream())
										.collect(Collectors.toList()))));
			}
			for (PGoTypeConcreteRecord.Field field : entry.record.getFields()) {
				solver.addFirst(
						new PGoTypeMonomorphicConstraint(entry.record, field.getType(), fields.get(field.getName())));
			}
			return entry;
		}
	}

	static class Concrete extends RecordTypeEntry {
		private final PGoTypeConcreteRecord record;

		Concrete(PGoTypeConcreteRecord record) {
			this.record = record;
		}

		PGoTypeConcreteRecord getRecord() {
			return record;
		}

		@Override
		boolean hasVariable(PGoTypeVariable variable) {
			return record.accept(new PGoTypeHasVariableVisitor(variable));
		}

		@Override
		RecordTypeEntry unify(PGoTypeSolver solver, Abstract entry) throws UnificationException {
			return entry.unify(solver, this);
		}

		@Override
		Concrete unify(PGoTypeSolver solver, Concrete entry) throws UnificationException {
			if (entry.record.getFields().size() != record.getFields().size()) {
				throw new UnificationException(new UnsatisfiableConstraintIssue(entry.record, record));
			}
			List<PGoTypeConcreteRecord.Field> fields = record.getFields();
			List<PGoTypeConcreteRecord.Field> otherFields = entry.record.getFields();
			for (int i = 0; i < otherFields.size(); i++) {
				PGoTypeConcreteRecord.Field field = fields.get(i);
				PGoTypeConcreteRecord.Field ofield = otherFields.get(i);
				if (!field.getName().equals(ofield.getName())) {
					throw new UnificationException(new UnsatisfiableConstraintIssue(entry.record, record));
				}
				solver.addFirst(new PGoTypeMonomorphicConstraint(
						Collections.emptyList(), new PGoTypeEqualityConstraint(field.getType(), ofield.getType())));
			}
			return this;
		}
	}
}
