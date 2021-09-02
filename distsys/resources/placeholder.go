package resources

import (
	"errors"
	"github.com/UBC-NSS/pgo/distsys/tla"

	"github.com/UBC-NSS/pgo/distsys"
)

var ErrPlaceHolderAccess = errors.New("no access is allowed to PlaceHolderResource")

type PlaceHolderResource struct{}

// PlaceHolderResourceMaker produces a distsys.ArchetypeResourceMaker that does
// nothing. It's just for usage of passing as placeholder for an archetype's
// argument and calling any of its methods causes a panic.
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

func (res *PlaceHolderResource) ReadValue() (tla.TLAValue, error) {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolderResource) WriteValue(value tla.TLAValue) error {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolderResource) Index(index tla.TLAValue) (distsys.ArchetypeResource, error) {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolderResource) Close() error {
	return nil
}
