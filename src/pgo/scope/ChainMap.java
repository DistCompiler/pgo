package pgo.scope;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 *
 * A map that extends another map. It is exactly like a normal map, but modifications only affect
 * the local map, not the parent.
 *
 * @param <K> The key used type
 * @param <V> The the value type
 */
public class ChainMap<K, V> implements Map<K, V> {
	private final Map<K, V> parent;
	private final Map<K, V> members;

	public ChainMap(Map<K, V> parent) {
		this.parent = parent;
		this.members = new HashMap<>();
	}

	public Map<K, V> getParent(){
		return parent;
	}

	@Override
	public void clear() {
		members.clear();
	}

	@Override
	public boolean containsKey(Object k) {
		return members.containsKey(k) || parent.containsKey(k);
	}

	@Override
	public boolean containsValue(Object v) {
		return members.containsValue(v) || parent.containsValue(v);
	}

	@Override
	public Set<Entry<K, V>> entrySet() {
		// do not overwrite members
		Map<K, V> result = new HashMap<>(members);
		Set<Entry<K, V>> parentSet = parent.entrySet();
		for(Entry<K, V> e : parentSet) {
			result.putIfAbsent(e.getKey(), e.getValue());
		}
		return result.entrySet();
	}

	@Override
	public V get(Object k) {
		V result = members.get(k);
		if(result == null) {
			return parent.get(k);
		}
		return result;
	}

	@Override
	public boolean isEmpty() {
		return members.isEmpty() && parent.isEmpty();
	}

	@Override
	public Set<K> keySet() {
		Set<K> result = members.keySet();

		result.addAll(parent.keySet());
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
		return keySet().size();
	}

	@Override
	public Collection<V> values() {
		return entrySet().stream().map(Entry::getValue).collect(Collectors.toList());
	}


}
