module example.com/shcounter

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
	github.com/cespare/xxhash v1.1.0 // indirect
	github.com/cespare/xxhash/v2 v2.1.1 // indirect
	github.com/dgraph-io/badger/v3 v3.2103.2 // indirect
	github.com/dgraph-io/ristretto v0.1.0 // indirect
	github.com/dustin/go-humanize v1.0.0 // indirect
	github.com/gogo/protobuf v1.3.2 // indirect
	github.com/golang/glog v0.0.0-20160126235308-23def4e6c14b // indirect
	github.com/golang/groupcache v0.0.0-20190702054246-869f871628b6 // indirect
	github.com/golang/protobuf v1.3.1 // indirect
	github.com/golang/snappy v0.0.3 // indirect
	github.com/google/flatbuffers v1.12.1 // indirect
	github.com/klauspost/compress v1.12.3 // indirect
	github.com/pkg/errors v0.9.1 // indirect
	go.opencensus.io v0.22.5 // indirect
	go.uber.org/atomic v1.9.0 // indirect
	go.uber.org/multierr v1.7.0 // indirect
	golang.org/x/net v0.0.0-20201021035429-f5854403a974 // indirect
	golang.org/x/sync v0.0.0-20210220032951-036812b2e83c // indirect
	golang.org/x/sys v0.0.0-20210124154548-22da62e12c0c // indirect
)
