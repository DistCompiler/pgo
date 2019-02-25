package pgo.util;

import java.util.HashMap;
import java.util.Map;

public class UnionFind<T> {
	private final Map<T, T> predecessorMap;
	private final Map<T, Integer> rank;

	public UnionFind() {
		this(new HashMap<>(), new HashMap<>());
	}

	private UnionFind(Map<T, T> predecessorMap, Map<T, Integer> rank) {
		this.predecessorMap = predecessorMap;
		this.rank = rank;
	}

	private boolean ensurePresence(T element) {
		if (!predecessorMap.containsKey(element)) {
			predecessorMap.put(element, element);
			rank.put(element, 0);
			return false;
		}
		return true;
	}

	public T find(T element) {
		if (!ensurePresence(element)) {
			return element;
		}
		while (true) {
			T parent = predecessorMap.getOrDefault(element, element);
			if (parent.equals(element)) {
				return element;
			}
			predecessorMap.put(element, predecessorMap.get(parent));
			element = parent;
		}
	}

	public void union(T u, T v) {
		T uRoot = find(u);
		T vRoot = find(v);
		if (uRoot.equals(vRoot)) {
			return;
		}
		if (rank.get(uRoot) < rank.get(vRoot)) {
			predecessorMap.put(uRoot, vRoot);
		} else if (rank.get(uRoot) > rank.get(vRoot)) {
			predecessorMap.put(vRoot, uRoot);
		} else {
			predecessorMap.put(vRoot, uRoot);
			rank.put(uRoot, rank.get(uRoot) + 1);
		}
	}

	public int getRank(T element) {
		ensurePresence(element);
		return rank.get(find(element));
	}

	public UnionFind<T> copy() {
		return new UnionFind<>(new HashMap<>(predecessorMap), new HashMap<>(rank));
	}
}
