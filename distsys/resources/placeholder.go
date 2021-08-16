package resources

import (
	"errors"

	"github.com/UBC-NSS/pgo/distsys"
)

var ErrPlaceHolderAccess = errors.New("no access is allowed to PlaceHolderResource")

type PlaceHolderResource struct{}

func PlaceHolderResourceMaker() distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		return &PlaceHolderResource{}
	})
}

var _ distsys.ArchetypeResource = &PlaceHolderResource{}

func (res *PlaceHolderResource) Abort() chan struct{} {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolderResource) PreCommit() chan error {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolderResource) Commit() chan struct{} {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolderResource) ReadValue() (distsys.TLAValue, error) {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolderResource) WriteValue(value distsys.TLAValue) error {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolderResource) Index(index distsys.TLAValue) (distsys.ArchetypeResource, error) {
	panic(ErrPlaceHolderAccess)
}
