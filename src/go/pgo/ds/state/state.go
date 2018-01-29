package state

// each of the interfaces declared here could have concrete implementations
// for each distribution strategy (state/centralized and state/distributed)
//
// Usage:
//
// 	// centralized
// 	stateBuilder := state.NewCentralizedStateBuilder()
// 	globalState := stateBuilder.SetProperty("Endpoints", []string{"10.0.0.1"}).SetProperty("Timeout", 3).Build()
//
// 	// distributed
// 	stateBuilder := globals.NewDistributedStateBuilder()
// 	globalState := stateBuilder.SetProperty("Processes", PCAL_PROCESSES).SetProperty("Ownership", OWNERSHIP).Build()

type GlobalStateBuilder interface {
	SetProperty(name string, val interface{}) GlobalStateBuilder
	Build() GlobalState
}

type GlobalState interface {
	Encode(val interface{}) []byte
	Decode(blob []byte) (interface{}, error)
}
