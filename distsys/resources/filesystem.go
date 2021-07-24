package resources

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"io/ioutil"
	"path"
)

// FilesystemArchetypeResourceMaker produces a distsys.ArchetypeResourceMaker for a filesystem-backed
// map-like resource. Each element of the map will refer to a file, with keys and values being required
// to be string-typed, and keys being required to refer to valid paths (or create-able paths, if a
// key is written to before it is read).
func FilesystemArchetypeResourceMaker(workingDirectory string) distsys.ArchetypeResourceMaker {
	return IncrementalArchetypeMapResourceMaker(func(index distsys.TLAValue) distsys.ArchetypeResourceMaker {
		return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
			return &fileArchetypeResource{
				workingDirectory: workingDirectory,
				subPath:          index.AsString(),
			}
		})
	})
}

type fileArchetypeResource struct {
	distsys.ArchetypeResourceLeafMixin

	workingDirectory string
	subPath          string

	writePending *string
	cachedRead   *string
}

var _ distsys.ArchetypeResource = &fileArchetypeResource{}

func (res *fileArchetypeResource) Abort() chan struct{} {
	res.writePending = nil
	res.cachedRead = nil
	return nil
}

func (res *fileArchetypeResource) PreCommit() chan error {
	return nil
}

func (res *fileArchetypeResource) Commit() chan struct{} {
	if res.writePending != nil {
		doneCh := make(chan struct{})
		go func() {
			err := ioutil.WriteFile(path.Join(res.workingDirectory, res.subPath), []byte(*res.writePending), 0777)
			if err != nil {
				panic(fmt.Errorf("could not write file %s: %w", path.Join(res.workingDirectory, res.subPath), err))
			}
			res.writePending = nil
			doneCh <- struct{}{}
		}()
		return doneCh
	}
	res.cachedRead = nil
	return nil
}

func (res *fileArchetypeResource) ReadValue() (distsys.TLAValue, error) {
	if res.writePending != nil {
		return distsys.NewTLAString(*res.writePending), nil
	} else if res.cachedRead != nil {
		return distsys.NewTLAString(*res.cachedRead), nil
	} else {
		contents, err := ioutil.ReadFile(path.Join(res.workingDirectory, res.subPath))
		if err != nil {
			panic(fmt.Errorf("could not read file %s: %w", path.Join(res.workingDirectory, res.subPath), err))
		}
		contentsStr := string(contents)
		res.cachedRead = &contentsStr
		return distsys.NewTLAString(*res.cachedRead), nil
	}
}

func (res *fileArchetypeResource) WriteValue(value distsys.TLAValue) error {
	res.cachedRead = nil
	strToWrite := value.AsString()
	res.writePending = &strToWrite
	return nil
}
