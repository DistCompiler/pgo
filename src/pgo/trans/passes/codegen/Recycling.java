package pgo.trans.passes.codegen;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

public class Recycling<T> {
	private final List<T> items;
	private int currentIndex;

	public Recycling() {
		items = new ArrayList<>();
		currentIndex = -1;
	}

	public Recycling(T items) {
		this(Collections.singletonList(items));
	}

	public Recycling(List<T> items) {
		this.items = new ArrayList<>(items);
		currentIndex = items.size() - 1;
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
}
