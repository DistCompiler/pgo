GO=go
JAVA=java
JAVA_OPTS=-XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC
TLA2TOOLS_JAR=../../tools/tla2tools.jar

TLC_CMD=$(JAVA) $(JAVA_OPTS) -cp $(TLA2TOOLS_JAR)

TLC=$(TLC_CMD) tlc2.TLC
PCAL=$(TLC_CMD) pcal.trans
SANY=$(TLC_CMD) tla2sany.SANY

.PHONY: mc tlaplusgen sany

all: build

mc: 
	$(TLC) -config pbkvs.cfg -workers 'auto' -cleanup pbkvs.tla

tlaplusgen:
	$(PCAL) -nocfg pbkvs.tla

sany:
	$(SANY) pbkvs.tla

build:
	$(GO) build -o server cmd/server/*.go
	$(GO) build -o client cmd/client/*.go
