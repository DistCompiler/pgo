package pgo.trans.passes.codegen;

import pgo.InternalCompilerError;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

public class Recycling<T> {
	public static class Checkpoint<T> {
		private final Recycling<T> from;
		private int currentIndex;

		public Checkpoint(Recycling<T> from, int currentIndex) {
			this.from = from;
			this.currentIndex = currentIndex;
		}
	}

	private final List<T> items;
	private int currentIndex;

	public Recycling() {
		this(new ArrayList<>(), -1);
	}

	public Recycling(T item) {
		this(new ArrayList<>(Collections.singletonList(item)), 0);
	}

	private Recycling(List<T> items, int currentIndex) {
		this.items = items;
		this.currentIndex = currentIndex;
	}

	public Checkpoint<T> checkpoint() {
		return new Checkpoint<>(this, currentIndex);
	}

	public void restore(Checkpoint checkpoint) {
		if (checkpoint.from != this) {
			throw new InternalCompilerError();
		}
		currentIndex = checkpoint.currentIndex;
	}

	public boolean add(T item) {
		boolean result = items.add(item);
		currentIndex = items.size() - 1;
		return result;
	}

	// fetch only returns the top of the stack
	public Optional<T> fetch() {
		if (currentIndex < 0 || currentIndex >= items.size()) {
			return Optional.empty();
		}
		return Optional.of(items.get(currentIndex));
	}

	// use advances the index and then returns the new top of the stack
	public Optional<T> use() {
		if (currentIndex < items.size()) {
			currentIndex += 1;
		}
		return fetch();
	}

	public void reuse() {
		currentIndex = -1;
	}

	@Override
	public String toString() {
		return "{currentIndex=" + currentIndex + ", items=" + items.toString() + "}";
	}
}
