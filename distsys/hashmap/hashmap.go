package hashmap

import (
	"github.com/UBC-NSS/pgo/distsys/tla"
)

type Entry[V any] struct {
	Key   tla.TLAValue
	Value V
}

type HashMap[V any] struct {
	M    map[uint32][]Entry[V]
	Keys []tla.TLAValue
}

func New[V any]() *HashMap[V] {
	return &HashMap[V]{M: make(map[uint32][]Entry[V])}
}

func (h *HashMap[V]) Set(k tla.TLAValue, v V) {
	entry := Entry[V]{
		Key:   k,
		Value: v,
	}
	hash := k.Hash()
	if _, ok := h.M[hash]; !ok {
		h.Keys = append(h.Keys, k)
		h.M[hash] = append(h.M[hash], entry)
	} else {
		for i := range h.M[hash] {
			if h.M[hash][i].Key.Equal(k) {
				h.M[hash][i].Value = v
				return
			}
		}
		h.Keys = append(h.Keys, k)
		h.M[hash] = append(h.M[hash], entry)
	}
}

func (h *HashMap[V]) Get(k tla.TLAValue) (V, bool) {
	var v V
	entries, ok := h.M[k.Hash()]
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

func (h *HashMap[V]) Clear() {
	for k := range h.M {
		delete(h.M, k)
	}
	h.Keys = nil
}
