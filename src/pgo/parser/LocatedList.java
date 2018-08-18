package pgo.parser;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

public class LocatedList<T> extends SourceLocatable implements List<T> {
	
	SourceLocation location;
	List<T> list;

	public LocatedList(SourceLocation location, List<T> list){
		this.location = location;
		this.list = list;
	}

	@Override
	public boolean equals(Object other){
		return list.equals(other);
	}

	@Override
	public int hashCode(){
		return list.hashCode();
	}

	@Override
	public String toString() {
		return list.toString() + " at " + location;
	}

	@Override
	public SourceLocation getLocation() {
		return location;
	}
	
	public void addLocation(SourceLocation loc) {
		location = location.combine(loc);
	}

	@Override
	public boolean add(T e) {
		return list.add(e);
	}

	@Override
	public void add(int index, T element) {
		list.add(index, element);
	}

	@Override
	public boolean addAll(Collection<? extends T> c) {
		return list.addAll(c);
	}

	@Override
	public boolean addAll(int index, Collection<? extends T> c) {
		return list.addAll(index, c);
	}

	@Override
	public void clear() {
		list.clear();
	}

	@Override
	public boolean contains(Object o) {
		return list.contains(o);
	}

	@Override
	public boolean containsAll(Collection<?> c) {
		return list.containsAll(c);
	}

	@Override
	public T get(int index) {
		return list.get(index);
	}

	@Override
	public int indexOf(Object o) {
		return list.indexOf(o);
	}

	@Override
	public boolean isEmpty() {
		return list.isEmpty();
	}

	@Override
	public Iterator<T> iterator() {
		return list.iterator();
	}

	@Override
	public int lastIndexOf(Object o) {
		return list.lastIndexOf(o);
	}

	@Override
	public ListIterator<T> listIterator() {
		return list.listIterator();
	}

	@Override
	public ListIterator<T> listIterator(int index) {
		return list.listIterator(index);
	}

	@Override
	public boolean remove(Object o) {
		return list.remove(o);
	}

	@Override
	public T remove(int index) {
		return list.remove(index);
	}

	@Override
	public boolean removeAll(Collection<?> c) {
		return list.removeAll(c);
	}

	@Override
	public boolean retainAll(Collection<?> c) {
		return list.retainAll(c);
	}

	@Override
	public T set(int index, T element) {
		return list.set(index, element);
	}

	@Override
	public int size() {
		return list.size();
	}

	@Override
	public List<T> subList(int fromIndex, int toIndex) {
		return list.subList(fromIndex, toIndex);
	}

	@Override
	public Object[] toArray() {
		return list.toArray();
	}

	@Override
	public <TT> TT[] toArray(TT[] a) {
		return list.toArray(a);
	}

}
