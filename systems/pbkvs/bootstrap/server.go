package bootstrap

import (
	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/resources"
	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/DistCompiler/pgo/systems/pbkvs"
	"github.com/DistCompiler/pgo/systems/pbkvs/configs"
)

func getReplicaCtx(self tla.Value, c configs.Root) *distsys.MPCalContext {
	network := newNetwork(self, c)
	networkLen := resources.NewMailboxesLength(network)
	constants := makeConstants(c)

	ctx := distsys.NewMPCalContext(self, pbkvs.AReplica, append(constants,
		distsys.EnsureArchetypeRefParam("net", network),
		distsys.EnsureArchetypeRefParam("fs", resources.NewIncMap(func(index tla.Value) distsys.ArchetypeResource {
			if !index.Equal(self) {
				panic("wrong index")
			}
			return resources.NewIncMap(func(index tla.Value) distsys.ArchetypeResource {
				return distsys.NewLocalArchetypeResource(tla.MakeString(""))
			})
		})),
		distsys.EnsureArchetypeRefParam("fd", resources.NewFailureDetector(
			func(t tla.Value) string {
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
	srvIdTLA := tla.MakeNumber(int32(srvId))
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
