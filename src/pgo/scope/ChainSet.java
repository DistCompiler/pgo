package pgo.scope;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class ChainSet<T> implements Set<T> {
	
	private Set<T> union;
	
	public ChainSet(Set<T> parent) {
		this.union = new HashSet<>(parent);
	}
	
	@Override
	public boolean add(T e) {
		return union.add(e);
	}
	@Override
	public boolean addAll(Collection<? extends T> c) {
		return union.addAll(c);
	}
	@Override
	public void clear() {
		union.clear();
	}
	@Override
	public boolean contains(Object o) {
		return union.contains(o);
	}
	@Override
	public boolean containsAll(Collection<?> c) {
		return union.containsAll(c);
	}
	@Override
	public boolean isEmpty() {
		return union.isEmpty();
	}
	@Override
	public Iterator<T> iterator() {
		return union.iterator();
	}
	@Override
	public boolean remove(Object o) {
		return union.remove(o);
	}
	@Override
	public boolean removeAll(Collection<?> c) {
		return union.removeAll(c);
	}
	@Override
	public boolean retainAll(Collection<?> c) {
		return union.retainAll(c);
	}
	@Override
	public int size() {
		return union.size();
	}
	@Override
	public Object[] toArray() {
		return union.toArray();
	}
	@Override
	public <V> V[] toArray(V[] a) {
		return union.toArray(a);
	}

	
}
