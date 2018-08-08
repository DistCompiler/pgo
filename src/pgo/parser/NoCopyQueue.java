package pgo.parser;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;

public final class NoCopyQueue<T> {
	private List<T> objects;
	private int index;
	private Iterator<T> iterator;
	private NoCopyQueue<T> next;

	private NoCopyQueue(List<T> objects, int index, Iterator<T> iterator, NoCopyQueue<T> next) {
		this.objects = objects;
		this.index = index;
		this.iterator = iterator;
		this.next = next;
	}

	public NoCopyQueue(){
		this.objects = Collections.emptyList();
		this.index = 0;
		this.iterator = null;
		this.next = null;
	}

	public NoCopyQueue(List<T> elements){
		this.objects = elements;
		this.index = 0;
		this.iterator = null;
		this.next = null;
	}

	@Override
	public String toString() {
		return objects.subList(index, objects.size()).toString() + "; " + next;
	}

	public NoCopyQueue<T> duplicate() {
		return new NoCopyQueue<>(objects, index, null, next);
	}

	public void prepend(List<T> elements) {
		next = duplicate();
		objects = elements;
		index = 0;
		iterator = null;
	}

	public void clear() {
		next = null;
		objects = Collections.emptyList();
		index = 0;
		iterator = null;
	}

	public Optional<T> dequeue(){
		while(true){
			if (iterator == null && index < objects.size()) {
				iterator = objects.listIterator(index);
			}
			if (iterator != null && iterator.hasNext()) {
				++index;
				return Optional.of(iterator.next());
			}
			if (next != null) {
				objects = next.objects;
				index = next.index;
				next = next.next;
				iterator = null;
			}else{
				return Optional.empty();
			}
		}
	}
}
