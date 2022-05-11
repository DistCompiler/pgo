package bootstrap

import (
	"log"

	"example.org/raftkvs"
	"example.org/raftkvs/configs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

type ArchetypeConfig struct {
	MailboxAddr string
	MonitorAddr string
}

func GetArchetypesConfig(c configs.Root) map[int]ArchetypeConfig {
	res := make(map[int]ArchetypeConfig)
	for srvId, srvCfg := range c.Servers {
		res[srvId] = ArchetypeConfig{
			MailboxAddr: srvCfg.MailboxAddr,
			MonitorAddr: srvCfg.MonitorAddr,
		}
	}

	clientIdOffset := 6 * c.NumServers
	for clientId, clientCfg := range c.Clients {
		res[clientId+clientIdOffset] = ArchetypeConfig{
			MailboxAddr: clientCfg.MailboxAddr,
		}
	}
	return res
}

func MakeConstants(c configs.Root) []distsys.MPCalContextConfigFn {
	constants := append([]distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(c.NumServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(int32(c.NumClients))),
		distsys.DefineConstantValue("ExploreFail", tla.TLA_FALSE),
		distsys.DefineConstantValue("Debug", tla.MakeTLABool(c.Debug)),
	}, raftkvs.PersistentLogConstantDefs, raftkvs.LeaderTimeoutConstantDefs)
	return constants
}

func NewNetwork(self tla.TLAValue, c configs.Root) *resources.Mailboxes {
	archetypesConfig := GetArchetypesConfig(c)

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
		resources.WithMailboxesDialTimeout(c.Mailboxes.DialTimeout),
		resources.WithMailboxesReadTimeout(c.Mailboxes.ReadTimeout),
		resources.WithMailboxesWriteTimeout(c.Mailboxes.WriteTimeout),
	)
}

func SetupMonitor(self tla.TLAValue, c configs.Root) *resources.Monitor {
	selfInt := int(self.AsNumber())
	archetypesConfig := GetArchetypesConfig(c)
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

func NewSingleFD(c configs.Root, index tla.TLAValue) *resources.SingleFailureDetector {
	aid := int(index.AsNumber())
	archetypesConfig := GetArchetypesConfig(c)
	archetypeConfig, ok := archetypesConfig[aid]
	if !ok || archetypeConfig.MonitorAddr == "" {
		log.Fatal("monitor not found")
	}

	singleFd := resources.NewSingleFailureDetector(
		index,
		archetypeConfig.MonitorAddr,
		resources.WithFailureDetectorPullInterval(c.FD.PullInterval),
		resources.WithFailureDetectorTimeout(c.FD.Timeout),
	)
	return singleFd
}
