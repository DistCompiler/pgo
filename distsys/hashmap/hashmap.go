package hashmap

import (
	"github.com/UBC-NSS/pgo/distsys/tla"
)

type Entry[V any] struct {
	Key   tla.Value
	Value V
}

type HashMap[V any] struct {
	m    map[uint32][]Entry[V]
	keys []tla.Value
}

func New[V any]() *HashMap[V] {
	return &HashMap[V]{m: make(map[uint32][]Entry[V])}
}

func (h *HashMap[V]) Set(k tla.Value, v V) {
	entry := Entry[V]{
		Key:   k,
		Value: v,
	}
	hash := k.Hash()
	if _, ok := h.m[hash]; !ok {
		h.keys = append(h.keys, k)
		h.m[hash] = append(h.m[hash], entry)
	} else {
		for i := range h.m[hash] {
			if h.m[hash][i].Key.Equal(k) {
				h.m[hash][i].Value = v
				return
			}
		}
		h.keys = append(h.keys, k)
		h.m[hash] = append(h.m[hash], entry)
	}
}

func (h *HashMap[V]) Get(k tla.Value) (V, bool) {
	var v V
	entries, ok := h.m[k.Hash()]
	if !ok {
		return v, false
	}

	for _, e := range entries {
		if e.Key.Equal(k) {
			return e.Value, true
		}
	}
	return v, false
}

func (h *HashMap[V]) Keys() []tla.Value {
	return h.keys
}

func (h *HashMap[V]) Clear() {
	for k := range h.m {
		delete(h.m, k)
	}
	h.keys = nil
}
