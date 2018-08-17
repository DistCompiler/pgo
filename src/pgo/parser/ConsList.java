package pgo.parser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public final class ConsList<T> {

	private static final class Node<T> {
		private final T value;
		private final Node<T> next;

		public Node(T value, Node<T> next) {
			this.value = value;
			this.next = next;
		}

		public T getValue() { return value; }
		public Node<T> getNext() { return next; }
	}

	private final Node<T> root;

	public ConsList() {
		this.root = null;
	}

	private ConsList(Node<T> root) {
		this.root = root;
	}

	public T first() { return root.getValue(); }
	public ConsList<T> rest() { return new ConsList<>(root.getNext()); }

	public ConsList<T> cons(T value) {
		return new ConsList<>(new Node<>(value, root));
	}

	@Override
	public String toString() {
		return toList().toString();
	}

	public List<T> toList() {
		List<T> result = new ArrayList<>();
		Node<T> rootCopy = root;
		while(rootCopy != null) {
			result.add(rootCopy.getValue());
			rootCopy = rootCopy.getNext();
		}
		return result;
	}

}
