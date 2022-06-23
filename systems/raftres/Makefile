GO=go

all: build

test:
	$(GO) test -v

racetest:
	$(GO) test -race -v

build:
	$(GO) build -o server cmd/server/*.go
