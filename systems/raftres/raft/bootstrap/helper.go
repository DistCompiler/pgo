package bootstrap

import (
	"log"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/resources"
	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/DistCompiler/pgo/systems/raftres/configs"
	"github.com/DistCompiler/pgo/systems/raftres/raft"
)

type archetypeConfig struct {
	MailboxAddr string
	MonitorAddr string
}

func getArchetypesConfig(c configs.Root) map[int]archetypeConfig {
	res := make(map[int]archetypeConfig)
	for srvId, srvCfg := range c.Servers {
		res[srvId] = archetypeConfig{
			MailboxAddr: srvCfg.RaftAddr,
			MonitorAddr: srvCfg.MonitorAddr,
		}
	}
	return res
}

func makeConstants(c configs.Root) []distsys.MPCalContextConfigFn {
	constants := append([]distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeNumber(int32(c.NumServers))),
		distsys.DefineConstantValue("ExploreFail", tla.ModuleFALSE),
		distsys.DefineConstantValue("Debug", tla.MakeBool(c.Debug)),
	}, raft.PersistentLogConstantDefs, raft.LeaderTimeoutConstantDefs)
	return constants
}

func newNetwork(self tla.Value, c configs.Root) *resources.Mailboxes {
	archetypesConfig := getArchetypesConfig(c)

	return resources.NewRelaxedMailboxes(
		func(idx tla.Value) (resources.MailboxKind, string) {
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

func fdAddrMapper(c configs.Root, index tla.Value) string {
	aid := int(index.AsNumber())
	archetypesConfig := getArchetypesConfig(c)
	archetypeConfig, ok := archetypesConfig[aid]
	if !ok || archetypeConfig.MonitorAddr == "" {
		log.Fatal("monitor not found")
	}
	return archetypeConfig.MonitorAddr
}

func newSingleFD(c configs.Root, index tla.Value) *resources.SingleFailureDetector {
	monAddr := fdAddrMapper(c, index)

	singleFd := resources.NewSingleFailureDetector(
		index,
		monAddr,
		resources.WithFailureDetectorPullInterval(c.FD.PullInterval),
		resources.WithFailureDetectorTimeout(c.FD.Timeout),
	)
	return singleFd
}
