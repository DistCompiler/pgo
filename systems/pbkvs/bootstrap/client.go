package bootstrap

import (
	"errors"
	"time"

	"github.com/DistCompiler/pgo/systems/pbkvs"
	"github.com/DistCompiler/pgo/systems/pbkvs/configs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getClientCtx(self tla.TLAValue, c configs.Root, inChan <-chan tla.TLAValue, outChan chan<- tla.TLAValue) *distsys.MPCalContext {
	network := newNetwork(self, c)
	networkLen := resources.NewMailboxesLength(network)
	constants := makeConstants(c)

	ctx := distsys.NewMPCalContext(self, pbkvs.AClient, append(constants,
		distsys.EnsureArchetypeRefParam("net", network),
		distsys.EnsureArchetypeRefParam("fd", resources.NewFailureDetector(
			func(t tla.TLAValue) string {
				return fdAddrMapper(c, t)
			},
			resources.WithFailureDetectorPullInterval(c.FD.PullInterval),
			resources.WithFailureDetectorTimeout(c.FD.Timeout),
		)),
		distsys.EnsureArchetypeRefParam("primary", pbkvs.NewLeaderElection()),
		distsys.EnsureArchetypeRefParam("netLen", networkLen),
		distsys.EnsureArchetypeRefParam("input", resources.NewInputChan(inChan)),
		distsys.EnsureArchetypeRefParam("output", resources.NewOutputChan(outChan)),
	)...)
	return ctx
}

type Client struct {
	Id     int
	Config configs.Root

	ctx    *distsys.MPCalContext
	reqCh  chan tla.TLAValue
	respCh chan tla.TLAValue

	timer        *time.Timer
	timerDrained bool
}

func NewClient(clientId int, c configs.Root) *Client {
	clientIdOffset := c.NumReplicas
	self := tla.MakeTLANumber(int32(clientIdOffset + clientId))

	reqCh := make(chan tla.TLAValue)
	respCh := make(chan tla.TLAValue)
	ctx := getClientCtx(self, c, reqCh, respCh)

	return &Client{
		Id:           clientId,
		Config:       c,
		ctx:          ctx,
		reqCh:        reqCh,
		respCh:       respCh,
		timer:        time.NewTimer(c.ClientRequestTimeout),
		timerDrained: false,
	}
}

func (c *Client) Run() error {
	return c.ctx.Run()
}

type Response string

func (c *Client) Put(key, value string) (Response, error) {
	c.reqCh <- tla.MakeTLARecord([]tla.TLARecordField{
		{Key: tla.MakeTLAString("typ"), Value: pbkvs.PUT_REQ(c.ctx.IFace())},
		{
			Key: tla.MakeTLAString("body"),
			Value: tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("key"), Value: tla.MakeTLAString(key)},
				{Key: tla.MakeTLAString("value"), Value: tla.MakeTLAString(value)},
			}),
		},
	})

	if !c.timer.Stop() {
		if !c.timerDrained {
			<-c.timer.C
		}
	}
	c.timer.Reset(c.Config.ClientRequestTimeout)
	c.timerDrained = false

	select {
	case resp := <-c.respCh:
		return Response(resp.AsString()), nil
	case <-c.timer.C:
		c.timerDrained = true
		return Response(""), errors.New("timeout")
	}
}

func (c *Client) Get(key string) (Response, error) {
	c.reqCh <- tla.MakeTLARecord([]tla.TLARecordField{
		{Key: tla.MakeTLAString("typ"), Value: pbkvs.GET_REQ(c.ctx.IFace())},
		{
			Key: tla.MakeTLAString("body"),
			Value: tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("key"), Value: tla.MakeTLAString(key)},
			}),
		},
	})

	if !c.timer.Stop() {
		if !c.timerDrained {
			<-c.timer.C
		}
	}
	c.timer.Reset(c.Config.ClientRequestTimeout)
	c.timerDrained = false

	select {
	case respTLA := <-c.respCh:
		resp := Response(respTLA.AsString())
		if resp == "" {
			return resp, errors.New("key not found")
		}
		return resp, nil
	case <-c.timer.C:
		c.timerDrained = true
		return Response(""), errors.New("timeout")
	}
}

func (c *Client) Close() error {
	c.ctx.Stop()
	c.timer.Stop()
	return nil
}
