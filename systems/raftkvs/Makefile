TLC=tlc
PCAL=pcal
SANY=sany

GO=go

.PHONY: sim mc tlaplusgen sany test racetest

sim:
	$(TLC) -config models/sim/SIM.cfg -depth '500' -simulate num=100 -workers 'auto' -cleanup models/sim/SIM.tla

mc: 
	$(TLC) -config models/mc/MC.cfg -workers 'auto' -cleanup models/mc/MC.tla

tlaplusgen:
	$(PCAL) -nocfg raftkvs.tla

sany:
	$(SANY) raftkvs.tla

test:
	$(GO) test -v

racetest:
	$(GO) test -race -v 