package distsys

// Specifies how to connect to our global state management
type Config struct {
	Endpoints []string // list of endpoints in the ip:port format
	Timeout   int      // timeout in seconds
}
