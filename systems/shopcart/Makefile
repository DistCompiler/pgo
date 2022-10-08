GO=go
JAVA=java
JAVA_OPTS=-XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC
TLA2TOOLS_JAR=../../tools/tla2tools.jar

TLC_CMD=$(JAVA) $(JAVA_OPTS) -cp $(TLA2TOOLS_JAR)

TLC=$(TLC_CMD) tlc2.TLC
PCAL=$(TLC_CMD) pcal.trans
SANY=$(TLC_CMD) tla2sany.SANY

all: build

mc: 
	$(TLC) -config shopcart.cfg -workers 'auto' -cleanup shopcart.tla

tlaplusgen:
	$(PCAL) -nocfg shopcart.tla

sany:
	$(SANY) shopcart.tla

build:
	$(GO) build -o node cmd/*.go

test:
	$(GO) test -v

racetest:
	$(GO) test -v -race