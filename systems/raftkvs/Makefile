GO=go
JAVA=java
JAVA_OPTS=-XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC
TLA2TOOLS_JAR=../../tools/tla2tools.jar

TLC_CMD=$(JAVA) $(JAVA_OPTS) -cp $(TLA2TOOLS_JAR)

TLC=$(TLC_CMD) tlc2.TLC
PCAL=$(TLC_CMD) pcal.trans
SANY=$(TLC_CMD) tla2sany.SANY

.PHONY: sim mc tlaplusgen sany test racetest build

all: build

sim:
	$(TLC) -config models/SIM.cfg -depth '1000' -simulate num=100 -workers 'auto' -cleanup raftkvs.tla

mc: 
	$(TLC) -config models/MC.cfg -workers 'auto' -cleanup raftkvs.tla

tlaplusgen:
	$(PCAL) -nocfg raftkvs.tla

sany:
	$(SANY) raftkvs.tla

test:
	$(GO) test -v

racetest:
	$(GO) test -race -v

build:
	$(GO) build -o server cmd/server/*.go
	$(GO) build -o client cmd/client/*.go
