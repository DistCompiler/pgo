package hashmap

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

type HashMap struct {
	M map[uint32]distsys.ArchetypeResource
}

func New() *HashMap {
	return &HashMap{M: make(map[uint32]distsys.ArchetypeResource)}
}

func (h *HashMap) Set(k tla.TLAValue, v distsys.ArchetypeResource) {
	h.M[k.Hash()] = v
}

func (h *HashMap) Get(k tla.TLAValue) (v distsys.ArchetypeResource, ok bool) {
	v, ok = h.M[k.Hash()]
	return
}

func (h *HashMap) Clear() {
	for k := range h.M {
		delete(h.M, k)
	}
}
