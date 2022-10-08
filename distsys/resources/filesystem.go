package resources

import (
	"fmt"
	"io/ioutil"
	"path"

	"github.com/UBC-NSS/pgo/distsys/tla"

	"github.com/UBC-NSS/pgo/distsys"
)

type FileSystem struct {
	*IncMap
}

var _ distsys.ArchetypeResource = &FailureDetector{}

// NewFileSystem produces a distsys.ArchetypeResource for a filesystem-backed
// map-like resource. Each element of the map will refer to a file, with keys and values being required
// to be string-typed, and keys being required to refer to valid paths (or create-able paths, if a
// key is written to before it is read).
func NewFileSystem(workingDirectory string) *FileSystem {
	return &FileSystem{
		NewIncMap(func(index tla.TLAValue) distsys.ArchetypeResource {
			return &file{
				workingDirectory: workingDirectory,
				subPath:          index.AsString(),
			}
		}),
	}
}

type file struct {
	distsys.ArchetypeResourceLeafMixin

	workingDirectory string
	subPath          string

	writePending *string
	cachedRead   *string
}

var _ distsys.ArchetypeResource = &file{}

func (res *file) Abort() chan struct{} {
	res.writePending = nil
	res.cachedRead = nil
	return nil
}

func (res *file) PreCommit() chan error {
	return nil
}

func (res *file) Commit() chan struct{} {
	res.cachedRead = nil
	if res.writePending != nil {
		doneCh := make(chan struct{})
		go func() {
			// FIXME: this is not atomic. see: https://github.com/natefinch/atomic and potential need for flush ops
			err := ioutil.WriteFile(path.Join(res.workingDirectory, res.subPath), []byte(*res.writePending), 0777)
			if err != nil {
				panic(fmt.Errorf("could not write file %s: %w", path.Join(res.workingDirectory, res.subPath), err))
			}
			res.writePending = nil
			doneCh <- struct{}{}
		}()
		return doneCh
	}
	return nil
}

func (res *file) ReadValue() (tla.TLAValue, error) {
	if res.writePending != nil {
		return tla.MakeTLAString(*res.writePending), nil
	} else if res.cachedRead != nil {
		return tla.MakeTLAString(*res.cachedRead), nil
	} else {
		contents, err := ioutil.ReadFile(path.Join(res.workingDirectory, res.subPath))
		if err != nil {
			panic(fmt.Errorf("could not read file %s: %w", path.Join(res.workingDirectory, res.subPath), err))
		}
		contentsStr := string(contents)
		res.cachedRead = &contentsStr
		return tla.MakeTLAString(*res.cachedRead), nil
	}
}

func (res *file) WriteValue(value tla.TLAValue) error {
	res.cachedRead = nil
	strToWrite := value.AsString()
	res.writePending = &strToWrite
	return nil
}

func (res *file) Close() error {
	return nil
}
