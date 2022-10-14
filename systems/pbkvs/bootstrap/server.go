package bootstrap

import (
	"github.com/DistCompiler/pgo/systems/pbkvs"
	"github.com/DistCompiler/pgo/systems/pbkvs/configs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getReplicaCtx(self tla.TLAValue, c configs.Root) *distsys.MPCalContext {
	network := newNetwork(self, c)
	networkLen := resources.NewMailboxesLength(network)
	constants := makeConstants(c)

	ctx := distsys.NewMPCalContext(self, pbkvs.AReplica, append(constants,
		distsys.EnsureArchetypeRefParam("net", network),
		distsys.EnsureArchetypeRefParam("fs", resources.NewIncMap(func(index tla.TLAValue) distsys.ArchetypeResource {
			if !index.Equal(self) {
				panic("wrong index")
			}
			return resources.NewIncMap(func(index tla.TLAValue) distsys.ArchetypeResource {
				return distsys.NewLocalArchetypeResource(tla.MakeTLAString(""))
			})
		})),
		distsys.EnsureArchetypeRefParam("fd", resources.NewFailureDetector(
			func(t tla.TLAValue) string {
				return fdAddrMapper(c, t)
			},
			resources.WithFailureDetectorPullInterval(c.FD.PullInterval),
			resources.WithFailureDetectorTimeout(c.FD.Timeout),
		)),
		distsys.EnsureArchetypeRefParam("netEnabled", resources.NewPlaceHolder()),
		distsys.EnsureArchetypeRefParam("primary", pbkvs.NewLeaderElection()),
		distsys.EnsureArchetypeRefParam("netLen", networkLen),
	)...)
	return ctx
}

type Replica struct {
	Id     int
	Config configs.Root

	ctx *distsys.MPCalContext
	mon *resources.Monitor
}

func NewReplica(srvId int, c configs.Root) *Replica {
	srvIdTLA := tla.MakeTLANumber(int32(srvId))
	mon := setupMonitor(srvIdTLA, c)
	ctx := getReplicaCtx(srvIdTLA, c)

	return &Replica{
		Id:     srvId,
		Config: c,
		ctx:    ctx,
		mon:    mon,
	}
}

func (r *Replica) Run() error {
	return r.mon.RunArchetype(r.ctx)
}

func (r *Replica) Close() error {
	r.ctx.Stop()
	return r.mon.Close()
}
