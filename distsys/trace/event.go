package trace

import (
	"encoding/json"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

type Event struct {
	ArchetypeName string
	Self          tla.Value
	Elements      []Element
	Clock         VClock
}

func (event Event) MarshalJSON() ([]byte, error) {
	serializedElements := []json.RawMessage{}
	for _, element := range event.Elements {
		switch element := element.(type) {
		case ReadElement:
			serializedIndices := []string{}
			for _, index := range element.Indices {
				serializedIndices = append(serializedIndices, index.String())
			}
			buf, err := json.Marshal(map[string]interface{}{
				"tag": "read",
				"name": map[string]interface{}{
					"prefix": element.Prefix,
					"name":   element.Name,
					"self":   event.Self.String(),
				},
				"indices": serializedIndices,
				"value":   element.Value.String(),
			})
			if err != nil {
				return nil, err
			}
			serializedElements = append(serializedElements, buf)
		case WriteElement:
			serializedIndices := []string{}
			for _, index := range element.Indices {
				serializedIndices = append(serializedIndices, index.String())
			}
			buf, err := json.Marshal(map[string]interface{}{
				"tag": "write",
				"name": map[string]interface{}{
					"prefix": element.Prefix,
					"name":   element.Name,
					"self":   event.Self.String(),
				},
				"indices": serializedIndices,
				"value":   element.Value.String(),
			})
			if err != nil {
				return nil, err
			}
			serializedElements = append(serializedElements, buf)
		default:
			panic("should be unreachable")
		}
	}

	return json.Marshal(map[string]interface{}{
		"archetypeName": event.ArchetypeName,
		"self":          event.Self.String(),
		"csElements":    serializedElements,
		"clock":         event.Clock,
	})
}

type Element interface {
	isElement()
}

type ReadElement struct {
	Prefix, Name string
	Indices      []tla.Value
	Value        tla.Value
}

var _ Element = ReadElement{}

func (_ ReadElement) isElement() {}

type WriteElement struct {
	Prefix, Name string
	Indices      []tla.Value
	Value        tla.Value
}

var _ Element = WriteElement{}

func (_ WriteElement) isElement() {}
