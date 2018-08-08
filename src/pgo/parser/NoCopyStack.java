package pgo.parser;

import java.util.Optional;

public final class NoCopyStack<T> {

	private static final class Node<T> {
		public T value;
		public Node<T> next;

		public Node(T value, Node<T> next) {
			this.value = value;
			this.next = next;
		}
	}

	private Node<T> root;

	public NoCopyStack() { this.root = null; }

	public NoCopyStack(T initVal) {
		this.root = new Node<T>(initVal, null);
	}

	private NoCopyStack(Node<T> root){ this.root = root; }

	public T top() { return root != null ? root.value : null; }
	public boolean hasNext() { return root != null && root.next != null; }
	public Optional<T> pop() {
		if(root == null) return Optional.empty();
		T value = root.value;
		root = root.next;
		return Optional.of(value);
	}
	public void push(T value) {
		root = new Node<>(value, root);
	}
	public NoCopyStack<T> duplicate() {
		return new NoCopyStack<>(root);
	}

	public boolean isEmpty() { return root == null; }
}
