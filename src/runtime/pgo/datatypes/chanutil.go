package datatypes

// Return a channel initialized with elements.
func NewChan(elts ...interface{}) chan interface{} {
	ret := make(chan interface{}, len(elts))
	for _, elt := range elts {
		ret <- elt
	}
	return ret
}
