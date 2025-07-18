package bootstrap

import (
	"errors"
	"log"
	"sync"
	"time"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/hashmap"
	"github.com/DistCompiler/pgo/distsys/resources"
	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/DistCompiler/pgo/systems/pbkvs"
	"github.com/DistCompiler/pgo/systems/pbkvs/configs"
)

var fdMap *hashmap.HashMap[distsys.ArchetypeResource]
var lock sync.Mutex

func init() {
	ResetClientFailureDetector()
}

func ResetClientFailureDetector() {
	log.Println("resetting client failure detector")

	lock.Lock()
	defer lock.Unlock()

	if fdMap != nil {
		fdMap.Clear()
	} else {
		fdMap = hashmap.New[distsys.ArchetypeResource]()
	}
}

func getFailureDetector(c configs.Root) distsys.ArchetypeResource {
	lock.Lock()
	for i := 1; i <= c.NumReplicas; i++ {
		tlaIndex := tla.MakeNumber(int32(i))
		_, ok := fdMap.Get(tlaIndex)
		if !ok {
			singleFD := newSingleFD(c, tlaIndex)
			fdMap.Set(tlaIndex, singleFD)
		}
	}
	lock.Unlock()

	return resources.NewHashMap(fdMap)
}

func getClientCtx(self tla.Value, c configs.Root, inChan <-chan tla.Value, outChan chan<- tla.Value) *distsys.MPCalContext {
	network := newNetwork(self, c)
	networkLen := resources.NewMailboxesLength(network)
	constants := makeConstants(c)
	fd := getFailureDetector(c)

	ctx := distsys.NewMPCalContext(self, pbkvs.AClient, append(constants,
		distsys.EnsureArchetypeRefParam("net", network),
		distsys.EnsureArchetypeRefParam("fd", fd),
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
	reqCh  chan tla.Value
	respCh chan tla.Value

	timer        *time.Timer
	timerDrained bool
}

func NewClient(clientId int, c configs.Root) *Client {
	clientIdOffset := c.NumReplicas
	self := tla.MakeNumber(int32(clientIdOffset + clientId))

	reqCh := make(chan tla.Value)
	respCh := make(chan tla.Value)
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
	c.reqCh <- tla.MakeRecord([]tla.RecordField{
		{Key: tla.MakeString("typ"), Value: pbkvs.PUT_REQ(c.ctx.IFace())},
		{
			Key: tla.MakeString("body"),
			Value: tla.MakeRecord([]tla.RecordField{
				{Key: tla.MakeString("key"), Value: tla.MakeString(key)},
				{Key: tla.MakeString("value"), Value: tla.MakeString(value)},
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
	c.reqCh <- tla.MakeRecord([]tla.RecordField{
		{Key: tla.MakeString("typ"), Value: pbkvs.GET_REQ(c.ctx.IFace())},
		{
			Key: tla.MakeString("body"),
			Value: tla.MakeRecord([]tla.RecordField{
				{Key: tla.MakeString("key"), Value: tla.MakeString(key)},
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
