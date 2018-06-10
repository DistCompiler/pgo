package pgo.scope;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class Context<V> implements Map<UID, V> {
	
	Map<UID, V> map;
	
	public Context() {
		this.map = new HashMap<>();
	}

	@Override
	public void clear() {
		map.clear();
	}

	@Override
	public boolean containsKey(Object key) {
		return map.containsKey(key);
	}

	@Override
	public boolean containsValue(Object value) {
		return map.containsValue(value);
	}

	@Override
	public Set<Entry<UID, V>> entrySet() {
		return map.entrySet();
	}

	@Override
	public V get(Object key) {
		return map.get(key);
	}

	@Override
	public boolean isEmpty() {
		return map.isEmpty();
	}

	@Override
	public Set<UID> keySet() {
		return map.keySet();
	}

	@Override
	public V put(UID key, V value) {
		return map.put(key, value);
	}

	@Override
	public void putAll(Map<? extends UID, ? extends V> m) {
		map.putAll(m);
	}

	@Override
	public V remove(Object key) {
		return map.remove(key);
	}

	@Override
	public int size() {
		return map.size();
	}

	@Override
	public Collection<V> values() {
		return map.values();
	}

}
