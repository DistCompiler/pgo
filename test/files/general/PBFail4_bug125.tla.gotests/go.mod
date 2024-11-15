module example.org/pbfail

go 1.22.0

toolchain go1.23.2

replace github.com/UBC-NSS/pgo/distsys => ../../../../distsys

require github.com/UBC-NSS/pgo/distsys v0.0.0-20241115155132-ac5da2a2c7c6

require (
	github.com/benbjohnson/immutable v0.4.3 // indirect
	github.com/segmentio/fasthash v1.0.3 // indirect
	github.com/stretchr/testify v1.8.1 // indirect
	go.uber.org/multierr v1.11.0 // indirect
	golang.org/x/exp v0.0.0-20241108190413-2d47ceb2692f // indirect
)
