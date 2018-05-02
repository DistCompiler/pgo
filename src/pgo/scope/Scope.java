package pgo.scope;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * 
 * A map object that implements nested scoping. Provide any map-like objects
 * as parent scopes and Scope will search through them if a value is not found
 * locally.
 * 
 * Modifications only affect the local map, not the parents.
 *
 * @param <K> The key used to access bound objects
 * @param <V> The the type of objects bound in this scope
 */
public class Scope<K, V> implements Map<K, V> {
	private List<? extends Map<K, V>> parents;
	private Map<K, V> members;
	
	public Scope(List<? extends Map<K, V>> parents) {
		this.parents = parents;
		this.members = new HashMap<>();
	}
	
	public Scope(List<? extends Map<K, V>> parents, Map<K, V> local) {
		this.parents = parents;
		this.members = local;
	}

	@Override
	public void clear() {
		members.clear();
	}

	@Override
	public boolean containsKey(Object k) {
		return members.containsKey(k) || parents.stream().anyMatch(p -> p.containsKey(k));
	}

	@Override
	public boolean containsValue(Object v) {
		return members.containsValue(v) || parents.stream().anyMatch(p -> p.containsValue(v));
	}

	@Override
	public Set<Entry<K, V>> entrySet() {
		Set<Entry<K, V>> result = members.entrySet();
		Set<K> keysUsed = members.keySet();
		for(Map<K, V> p : parents) {
			Set<Entry<K, V>> parentSet = p.entrySet();
			for(Entry<K, V> e : parentSet) {
				// add only if we haven't encountered that key before
				if(!keysUsed.contains(e.getKey())) {
					keysUsed.add(e.getKey());
					result.add(e);
				}
			}
		}
		return result;
	}

	@Override
	public V get(Object k) {
		V result = members.get(k);
		if(result == null) {
			for(Map<K, V> p : parents) {
				result = p.get(k);
				if(result != null) {
					return result;
				}
			}
		}
		return result;
	}

	@Override
	public boolean isEmpty() {
		return members.isEmpty() && parents.stream().allMatch(Map<K, V>::isEmpty);
	}

	@Override
	public Set<K> keySet() {
		Set<K> result = members.keySet();
		
		result.addAll(parents.stream()
				.map(Map<K, V>::keySet)
				.collect(HashSet<K>::new, Set<K>::addAll, Set<K>::addAll));
		return result;
	}

	@Override
	public V put(K k, V v) {
		return members.put(k, v);
	}

	@Override
	public void putAll(Map<? extends K, ? extends V> arg) {
		members.putAll(arg);
	}

	@Override
	public V remove(Object k) {
		return members.remove(k);
	}

	@Override
	public int size() {
		return members.size() + parents.stream().mapToInt(Map<K, V>::size).sum();
	}

	@Override
	public Collection<V> values() {
		return entrySet().stream().map(Entry<K, V>::getValue).collect(Collectors.toList());
	}
	
	
}
