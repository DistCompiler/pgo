package distsys

import "github.com/UBC-NSS/pgo/distsys/tla"

type Resource struct {
	Name string
}

func NewResource(name string) *Resource {
	return &Resource{
		Name: name,
	}
}

func (res *Resource) Child(name string) *Resource {
	return &Resource{
		Name: res.Name + "/" + name,
	}
}

type ResourceReadEffect struct {
	Resource *Resource
	Indices  []tla.TLAValue
}

type ResourceWriteEffect struct {
	Resource *Resource
	Indices  []tla.TLAValue
	Value    tla.TLAValue
}
