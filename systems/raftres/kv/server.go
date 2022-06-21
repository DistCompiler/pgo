package kv

import (
	"log"

	"github.com/DistCompiler/pgo/systems/raftres/configs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func serverPropId(c configs.Root, srvId int) int {
	return c.NumServers*7 + srvId
}

func serverAcctId(c configs.Root, srvId int) int {
	return c.NumServers*8 + srvId
}

func newServerCtxs(srvId int, c configs.Root, propChan, acctChan chan tla.TLAValue) []*distsys.MPCalContext {
	constants := makeConstants(c)

	tlaSrvId := tla.MakeTLANumber(int32(serverPropId(c, srvId)))

	toMap := func(res distsys.ArchetypeResource) distsys.ArchetypeResource {
		return resources.NewIncMap(func(index tla.TLAValue) distsys.ArchetypeResource {
			if index.Equal(tlaSrvId) {
				return res
			}
			panic("wrong index")
		})
	}

	serverPropCtx := func() *distsys.MPCalContext {
		self := serverPropId(c, srvId)
		tlaSelf := tla.MakeTLANumber(int32(self))

		net := newNetwork(c, tlaSelf)
		propCh := resources.NewOutputChan(propChan)

		resourcesConfig := []distsys.MPCalContextConfigFn{
			distsys.EnsureArchetypeValueParam("srvId", tlaSrvId),
			distsys.EnsureArchetypeRefParam("net", net),
			distsys.EnsureArchetypeRefParam("propCh", propCh),
		}

		ctx := distsys.NewMPCalContext(
			tlaSelf, AServerProp,
			distsys.EnsureMPCalContextConfigs(resourcesConfig...),
			distsys.EnsureMPCalContextConfigs(constants...),
		)
		return ctx
	}()

	serverAcctCtx := func() *distsys.MPCalContext {
		self := serverAcctId(c, srvId)
		tlaSelf := tla.MakeTLANumber(int32(self))

		net := newNetwork(c, tlaSelf)
		acctCh := resources.NewInputChan(acctChan,
			resources.WithInputChanReadTimeout(c.InputChanReadTimeout))

		resourcesConfig := []distsys.MPCalContextConfigFn{
			distsys.EnsureArchetypeValueParam("srvId", tlaSrvId),
			distsys.EnsureArchetypeRefParam("net", net),
			distsys.EnsureArchetypeRefParam("acctCh", toMap(acctCh)),
		}

		ctx := distsys.NewMPCalContext(
			tlaSelf, AServerAcct,
			distsys.EnsureMPCalContextConfigs(resourcesConfig...),
			distsys.EnsureMPCalContextConfigs(constants...),
		)
		return ctx
	}()

	return []*distsys.MPCalContext{serverPropCtx, serverAcctCtx}
}

type Server struct {
	Id     int
	Config configs.Root

	ctxs []*distsys.MPCalContext
	mon  *resources.Monitor
}

func NewServer(srvId int, c configs.Root, mon *resources.Monitor, propCh, acctCh chan tla.TLAValue) *Server {
	ctxs := newServerCtxs(srvId, c, propCh, acctCh)
	return &Server{
		Id:     srvId,
		Config: c,
		ctxs:   ctxs,
		mon:    mon,
	}
}

func (s *Server) Run() error {
	errCh := make(chan error)
	for i := range s.ctxs {
		ctx := s.ctxs[i]
		go func() {
			err := s.mon.RunArchetype(ctx)
			log.Printf("archetype %v finished, err = %v", ctx.IFace().Self(), err)
			errCh <- err
		}()
	}

	for range s.ctxs {
		err := <-errCh
		if err != nil {
			return err
		}
	}
	return nil
}

func (s *Server) Close() error {
	for _, ctx := range s.ctxs {
		ctx.Stop()
	}
	return nil
}
