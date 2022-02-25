package resources

import (
	"errors"

	"github.com/UBC-NSS/pgo/distsys/tla"

	"github.com/UBC-NSS/pgo/distsys"
)

var ErrPlaceHolderAccess = errors.New("no access is allowed to PlaceHolder")

type PlaceHolder struct{}

// PlaceHolderResourceMaker produces a distsys.ArchetypeResourceMaker that does
// nothing. It's just for usage of passing as placeholder for an archetype's
// argument and calling any of its methods causes a panic.
func PlaceHolderResourceMaker() distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		return &PlaceHolder{}
	})
}

var _ distsys.ArchetypeResource = &PlaceHolder{}

func (res *PlaceHolder) Abort() chan struct{} {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolder) PreCommit() chan error {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolder) Commit() chan struct{} {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolder) ReadValue() (tla.TLAValue, error) {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolder) WriteValue(value tla.TLAValue) error {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolder) Index(index tla.TLAValue) (distsys.ArchetypeResource, error) {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolder) Close() error {
	return nil
}

func (res *PlaceHolder) ForkState() (distsys.ArchetypeResource, error) {
	//TODO implement me
	panic("implement me")
}
