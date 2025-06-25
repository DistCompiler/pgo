package kv

import (
	"log"
	"runtime/debug"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/resources"
	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/DistCompiler/pgo/systems/raftres/configs"
)

type archetypeConfig struct {
	MailboxAddr string
	MonitorAddr string
}

func getArchetypesConfig(c configs.Root) map[int]archetypeConfig {
	res := make(map[int]archetypeConfig)

	for srvId, cfg := range c.Servers {
		aid := serverPropId(c, srvId)
		res[aid] = archetypeConfig{
			MailboxAddr: cfg.KVAddr,
			MonitorAddr: cfg.MonitorAddr,
		}
	}

	for id, cfg := range c.Clients {
		aid := clientId(c, id)
		res[aid] = archetypeConfig{
			MailboxAddr: cfg.MailboxAddr,
		}
	}

	return res
}

func makeConstants(c configs.Root) []distsys.MPCalContextConfigFn {
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeNumber(int32(c.NumServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeNumber(int32(c.NumClients))),
		distsys.DefineConstantValue("Debug", tla.MakeBool(c.Debug)),
	}
	return constants
}

func newNetwork(c configs.Root, self tla.Value) *resources.Mailboxes {
	archetypesConfig := getArchetypesConfig(c)

	return resources.NewRelaxedMailboxes(
		func(idx tla.Value) (resources.MailboxKind, string) {
			kind := resources.MailboxesRemote
			if idx.Equal(self) {
				kind = resources.MailboxesLocal
			}
			idxInt := int(idx.AsNumber())
			addr := archetypesConfig[idxInt].MailboxAddr
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
		log.Fatalf("monitor not found for archetype %d\n%s", aid, debug.Stack())
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
