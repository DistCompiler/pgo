module example.org/raftkvs

go 1.14

replace github.com/UBC-NSS/pgo/distsys => ../../../../distsys

require (
	github.com/UBC-NSS/pgo/distsys v0.0.0-00010101000000-000000000000
	github.com/benbjohnson/immutable v0.3.0
	github.com/dgraph-io/badger/v3 v3.2103.2
)
