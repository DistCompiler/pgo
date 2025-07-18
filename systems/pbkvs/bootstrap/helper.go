package bootstrap

import (
	"log"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/resources"
	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/DistCompiler/pgo/systems/pbkvs"
	"github.com/DistCompiler/pgo/systems/pbkvs/configs"
)

type archetypeConfig struct {
	ReqMailboxAddr  string
	RespMailboxAddr string
	MonitorAddr     string
}

func getArchetypesConfig(c configs.Root) map[int]archetypeConfig {
	res := make(map[int]archetypeConfig)
	for replicaId, replicaCfg := range c.Replicas {
		res[replicaId] = archetypeConfig{
			ReqMailboxAddr:  replicaCfg.ReqMailboxAddr,
			RespMailboxAddr: replicaCfg.RespMailboxAddr,
			MonitorAddr:     replicaCfg.MonitorAddr,
		}
	}

	clientIdOffset := c.NumReplicas
	for clientId, clientCfg := range c.Clients {
		res[clientId+clientIdOffset] = archetypeConfig{
			ReqMailboxAddr:  clientCfg.ReqMailboxAddr,
			RespMailboxAddr: clientCfg.RespMailboxAddr,
		}
	}
	return res
}

func newNetwork(self tla.Value, c configs.Root) *resources.Mailboxes {
	var iface = distsys.NewMPCalContextWithoutArchetype().IFace()
	archetypesConfig := getArchetypesConfig(c)

	return resources.NewRelaxedMailboxes(
		func(idx tla.Value) (resources.MailboxKind, string) {
			aid := idx.AsTuple().Get(0).AsNumber()
			msgType := idx.AsTuple().Get(1)

			var addr string
			kind := resources.MailboxesRemote
			if aid == self.AsNumber() {
				kind = resources.MailboxesLocal
			}
			if msgType.Equal(pbkvs.REQ_INDEX(iface)) {
				addr = archetypesConfig[int(aid)].ReqMailboxAddr
			} else if msgType.Equal(pbkvs.RESP_INDEX(iface)) {
				addr = archetypesConfig[int(aid)].RespMailboxAddr
			} else {
				panic("invalid mailbox type")
			}
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

func makeConstants(c configs.Root) []distsys.MPCalContextConfigFn {
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_REPLICAS", tla.MakeNumber(int32(c.NumReplicas))),
		distsys.DefineConstantValue("NUM_CLIENTS", tla.MakeNumber(int32(c.NumClients))),
		distsys.DefineConstantValue("EXPLORE_FAIL", tla.ModuleFALSE),
		distsys.DefineConstantValue("DEBUG", tla.MakeBool(c.Debug)),
	}
	return constants
}

func setupMonitor(self tla.Value, c configs.Root) *resources.Monitor {
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
