module example.com/shopcart

go 1.17

replace github.com/UBC-NSS/pgo/distsys => ../../distsys

require github.com/UBC-NSS/pgo/distsys v0.0.0-20211101232000-7978191b68b7

require (
	github.com/benbjohnson/immutable v0.3.0 // indirect
	go.uber.org/atomic v1.9.0 // indirect
	go.uber.org/multierr v1.7.0 // indirect
)