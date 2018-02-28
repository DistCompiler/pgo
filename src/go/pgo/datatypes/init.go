package datatypes

import (
	"encoding/gob"
)

func init() {
	gob.Register(&mp{})
	gob.Register(&KVPair{})
	gob.Register(&pair{})
	gob.Register(&set{})
	gob.Register(&tuple{})
}
