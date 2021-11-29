module example.com/lock

go 1.17

replace github.com/UBC-NSS/pgo/distsys => ../../distsys

replace benchmark => ../common

replace counter => ../../test/files/general/shcounter.tla.gotests

require (
	benchmark v0.0.0-00010101000000-000000000000
	counter v0.0.0-00010101000000-000000000000
)

require (
	github.com/UBC-NSS/pgo/distsys v0.0.0-20211126020840-5e7fecd5cd7b // indirect
	github.com/benbjohnson/immutable v0.3.0 // indirect
	go.uber.org/atomic v1.9.0 // indirect
	go.uber.org/multierr v1.7.0 // indirect
)
