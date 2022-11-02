package resources

import (
	"errors"

	"github.com/UBC-NSS/pgo/distsys/trace"

	"github.com/UBC-NSS/pgo/distsys/tla"

	"github.com/UBC-NSS/pgo/distsys"
)

var ErrPlaceHolderAccess = errors.New("no access is allowed to PlaceHolder")

type PlaceHolder struct{}

// NewPlaceHolder produces a distsys.ArchetypeResource that does
// nothing. It's just for usage of passing as placeholder for an archetype's
// argument and calling any of its methods causes a panic.
func NewPlaceHolder() distsys.ArchetypeResource {
	return &PlaceHolder{}
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

func (res *PlaceHolder) ReadValue() (tla.Value, error) {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolder) WriteValue(value tla.Value) error {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolder) Index(index tla.Value) (distsys.ArchetypeResource, error) {
	panic(ErrPlaceHolderAccess)
}

func (res *PlaceHolder) Close() error {
	return nil
}

func (res *PlaceHolder) VClockHint(archClock trace.VClock) trace.VClock {
	return archClock
}
