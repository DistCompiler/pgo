package hashmap

import (
	"github.com/UBC-NSS/pgo/distsys/tla"
)

type HashMap[V any] struct {
	M map[uint32]V
}

func New[V any]() *HashMap[V] {
	return &HashMap[V]{M: make(map[uint32]V)}
}

func (h *HashMap[V]) Set(k tla.TLAValue, v V) {
	h.M[k.Hash()] = v
}

func (h *HashMap[V]) Get(k tla.TLAValue) (v V, ok bool) {
	v, ok = h.M[k.Hash()]
	return
}

func (h *HashMap[V]) Clear() {
	for k := range h.M {
		delete(h.M, k)
	}
}
