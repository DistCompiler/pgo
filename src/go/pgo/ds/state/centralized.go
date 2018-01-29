package centralized

var ACCEPTED_PROPERTIES = []string{"Endpoints", "Timeout"}

type CentralizedGlobalStateBuilder struct {
	properties map[string]interface{}
}

func NewCentralizedStateBuilder() GlobalStateBuilder {
	return CentralizedGlobalStateBuilder{
		properties: map[string]interface{}{},
	}
}

func validProperty(name string) bool {
	for i := 0; i < len(ACCEPTED_PROPERTIES); i++ {
		if ACCEPTED_PROPERTIES[i] == name {
			return true
		}
	}

	return false
}

func (config *CentralizedGlobalStateBuilder) SetProperty(name string, val interface{}) GlobalStateBuilder {
	if !validProperty(name) {
		panic(fmt.Sprintf("Invalid property name %s", name))
	}

	properties[name] = val
	return config
}

func (config *CentralizedGlobalStateBuilder) Build() GlobalState {
	return CentralizedGlobalState{
		EtcdEndpoints: properties["Endpoints"].([]string),
		Timeout:       properties["Timeout"].(int),
	}
}

type CentralizedGlobalState struct {
	EtcdEndpoints []string
	Timeout       int
}

func (state CentralizedGlobalState) Encode(val interface{}) []byte {
	// ...
	return []byte{}
}
