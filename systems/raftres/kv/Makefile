GO=go
JAVA=java
JAVA_OPTS=-XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC
TLA2TOOLS_JAR=../../../tools/tla2tools.jar

TLC_CMD=$(JAVA) $(JAVA_OPTS) -cp $(TLA2TOOLS_JAR)

TLC=$(TLC_CMD) tlc2.TLC
PCAL=$(TLC_CMD) pcal.trans
SANY=$(TLC_CMD) tla2sany.SANY

mc:
	$(TLC) -config kv.cfg -workers 'auto' -cleanup kv.tla

tlaplusgen:
	$(PCAL) -nocfg kv.tla

sany:
	$(SANY) kv.tla

test:
	$(GO) test -v

racetest:
	$(GO) test -race -v
