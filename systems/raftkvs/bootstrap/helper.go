package bootstrap

import (
	"log"

	"github.com/DistCompiler/pgo/systems/raftkvs"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

type archetypeConfig struct {
	MailboxAddr string
	MonitorAddr string
}

func getArchetypesConfig(c configs.Root) map[int]archetypeConfig {
	res := make(map[int]archetypeConfig)
	for srvId, srvCfg := range c.Servers {
		res[srvId] = archetypeConfig{
			MailboxAddr: srvCfg.MailboxAddr,
			MonitorAddr: srvCfg.MonitorAddr,
		}
	}

	clientIdOffset := 6 * c.NumServers
	for clientId, clientCfg := range c.Clients {
		res[clientId+clientIdOffset] = archetypeConfig{
			MailboxAddr: clientCfg.MailboxAddr,
		}
	}
	return res
}

func makeConstants(c configs.Root) []distsys.MPCalContextConfigFn {
	constants := append([]distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(c.NumServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(int32(c.NumClients))),
		distsys.DefineConstantValue("ExploreFail", tla.TLA_FALSE),
		distsys.DefineConstantValue("Debug", tla.MakeTLABool(c.Debug)),
	}, raftkvs.PersistentLogConstantDefs, raftkvs.LeaderTimeoutConstantDefs)
	return constants
}

func newNetwork(self tla.TLAValue, c configs.Root) *resources.Mailboxes {
	archetypesConfig := getArchetypesConfig(c)

	return resources.NewRelaxedMailboxes(
		func(idx tla.TLAValue) (resources.MailboxKind, string) {
			aid := idx.AsNumber()
			kind := resources.MailboxesRemote
			if aid == self.AsNumber() {
				kind = resources.MailboxesLocal
			}
			addr := archetypesConfig[int(aid)].MailboxAddr
			return kind, addr
		},
		resources.WithMailboxesReceiveChanSize(c.Mailboxes.ReceiveChanSize),
		resources.WithMailboxesDialTimeout(c.Mailboxes.DialTimeout),
		resources.WithMailboxesReadTimeout(c.Mailboxes.ReadTimeout),
		resources.WithMailboxesWriteTimeout(c.Mailboxes.WriteTimeout),
	)
}

func setupMonitor(self tla.TLAValue, c configs.Root) *resources.Monitor {
	selfInt := int(self.AsNumber())
	archetypesConfig := getArchetypesConfig(c)
	archetypeConfig, ok := archetypesConfig[selfInt]
	if !ok || archetypeConfig.MonitorAddr == "" {
		log.Fatal("monitor not found")
	}
	mon := resources.NewMonitor(archetypeConfig.MonitorAddr)
	go func() {
		if err := mon.ListenAndServe(); err != nil {
			log.Fatal(err)
		}
	}()
	return mon
}

func fdAddrMapper(c configs.Root, index tla.TLAValue) string {
	aid := int(index.AsNumber())
	archetypesConfig := getArchetypesConfig(c)
	archetypeConfig, ok := archetypesConfig[aid]
	if !ok || archetypeConfig.MonitorAddr == "" {
		log.Fatal("monitor not found")
	}
	return archetypeConfig.MonitorAddr
}

func newSingleFD(c configs.Root, index tla.TLAValue) *resources.SingleFailureDetector {
	monAddr := fdAddrMapper(c, index)

	singleFd := resources.NewSingleFailureDetector(
		index,
		monAddr,
		resources.WithFailureDetectorPullInterval(c.FD.PullInterval),
		resources.WithFailureDetectorTimeout(c.FD.Timeout),
	)
	return singleFd
}
