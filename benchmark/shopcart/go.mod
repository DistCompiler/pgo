module example.com/shopcart

go 1.17

replace benchmark => ../common

replace github.com/UBC-NSS/pgo/distsys => ../../distsys

require (
	benchmark v0.0.0-00010101000000-000000000000
	github.com/UBC-NSS/pgo/distsys v0.0.0-20211101232000-7978191b68b7
	github.com/benbjohnson/immutable v0.3.0
)

require (
	github.com/dgraph-io/badger/v3 v3.2103.2 // indirect
	go.uber.org/atomic v1.9.0 // indirect
	go.uber.org/multierr v1.7.0 // indirect
	golang.org/x/sync v0.0.0-20210220032951-036812b2e83c // indirect
)
