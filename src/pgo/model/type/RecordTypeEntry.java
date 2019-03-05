package pgo.model.type;

import pgo.InternalCompilerError;
import pgo.model.type.constraint.EqualityConstraint;
import pgo.model.type.constraint.MonomorphicConstraint;

import java.util.*;
import java.util.stream.Collectors;

abstract class RecordTypeEntry {
	abstract boolean hasVariable(TypeVariable variable);

	RecordTypeEntry unify(TypeSolver solver, RecordTypeEntry entry) throws UnificationException {
		if (entry instanceof Abstract) {
			return unify(solver, (Abstract) entry);
		}
		if (entry instanceof Concrete) {
			return unify(solver, (Concrete) entry);
		}
		throw new InternalCompilerError();
	}

	abstract RecordTypeEntry unify(TypeSolver solver, Abstract entry) throws UnificationException;
	abstract Concrete unify(TypeSolver solver, Concrete entry) throws UnificationException;

	abstract RecordType toConcreteRecord();

	static class Abstract extends RecordTypeEntry {
		static final Abstract EMPTY_ABSTRACT_RECORD = new Abstract();

		private final Map<String, Type> fields;

		Abstract() {
			this(new HashMap<>());
		}

		Abstract(Map<String, Type> fields) {
			this.fields = fields;
		}

		@Override
		boolean hasVariable(TypeVariable variable) {
			TypeHasVariableVisitor visitor = new TypeHasVariableVisitor(variable);
			return fields.values().stream().anyMatch(t -> t.accept(visitor));
		}

		@Override
		RecordTypeEntry unify(TypeSolver solver, Abstract entry) throws UnificationException {
			Map<String, Type> fields = new HashMap<>(this.fields);
			entry.fields.forEach((k, v) -> {
				if (fields.containsKey(k)) {
					solver.addFirst(new MonomorphicConstraint(v, v, fields.get(k)));
				} else {
					fields.put(k, v);
				}
			});
			return new Abstract(fields);
		}

		private void throwException(Concrete entry) throws UnificationException {
			List<RecordType.Field> fs = new ArrayList<>();
			fields.forEach((k, v) -> fs.add(new RecordType.Field(k, v)));
			throw new UnificationException(new UnsatisfiableConstraintIssue(
					entry.record,
					new RecordType(
							fs,
							fs.stream()
									.flatMap(f -> f.getType().getOrigins().stream())
									.collect(Collectors.toList()))));
		}

		@Override
		Concrete unify(TypeSolver solver, Concrete entry) throws UnificationException {
			if (entry.record.getFields().size() < fields.size()) {
				throwException(entry);
			}
			Set<String> keysInAbstractNotConcrete = new HashSet<>(fields.keySet());
			keysInAbstractNotConcrete.removeAll(entry.record.getFields().stream()
					.map(RecordType.Field::getName)
					.collect(Collectors.toSet()));
			if (keysInAbstractNotConcrete.size() > 0) {
				throwException(entry);
			}
			for (RecordType.Field field : entry.record.getFields()) {
				if (fields.containsKey(field.getName())) {
					solver.addFirst(new MonomorphicConstraint(
							entry.record, field.getType(), fields.get(field.getName())));
				}
			}
			return entry;
		}

		@Override
		RecordType toConcreteRecord() {
			return new RecordType(
					fields.entrySet().stream()
							.sorted(Comparator.comparing(Map.Entry::getKey))
							.map(e -> new RecordType.Field(e.getKey(), e.getValue()))
							.collect(Collectors.toList()),
					fields.values().stream().flatMap(t -> t.getOrigins().stream()).collect(Collectors.toList()));
		}
	}

	static class Concrete extends RecordTypeEntry {
		private final RecordType record;

		Concrete(RecordType record) {
			this.record = record;
		}

		RecordType getRecord() {
			return record;
		}

		@Override
		boolean hasVariable(TypeVariable variable) {
			return record.accept(new TypeHasVariableVisitor(variable));
		}

		@Override
		RecordTypeEntry unify(TypeSolver solver, Abstract entry) throws UnificationException {
			return entry.unify(solver, this);
		}

		@Override
		Concrete unify(TypeSolver solver, Concrete entry) throws UnificationException {
			if (entry.record.getFields().size() != record.getFields().size()) {
				throw new UnificationException(new UnsatisfiableConstraintIssue(entry.record, record));
			}
			List<RecordType.Field> fields = record.getFields();
			List<RecordType.Field> otherFields = entry.record.getFields();
			for (int i = 0; i < otherFields.size(); i++) {
				RecordType.Field field = fields.get(i);
				RecordType.Field ofield = otherFields.get(i);
				if (!field.getName().equals(ofield.getName())) {
					throw new UnificationException(new UnsatisfiableConstraintIssue(entry.record, record));
				}
				solver.addFirst(new MonomorphicConstraint(
						Collections.emptyList(), new EqualityConstraint(field.getType(), ofield.getType())));
			}
			return this;
		}

		@Override
		RecordType toConcreteRecord() {
			return record;
		}
	}
}
