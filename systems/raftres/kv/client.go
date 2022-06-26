package kv

import (
	"fmt"
	"log"
	"sync"
	"time"

	"github.com/DistCompiler/pgo/systems/raftres/configs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/hashmap"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func clientId(c configs.Root, clientId int) int {
	return c.NumServers*9 + clientId
}

var fdMap *hashmap.HashMap[distsys.ArchetypeResource]
var lock sync.Mutex

func getFailureDetector(c configs.Root) distsys.ArchetypeResource {
	lock.Lock()
	if fdMap == nil {
		fdMap = hashmap.New[distsys.ArchetypeResource]()
		for i := 1; i <= c.NumServers; i++ {
			id := serverPropId(c, i)
			tlaId := tla.MakeTLANumber(int32(id))
			singleFD := newSingleFD(c, tlaId)
			fdMap.Set(tlaId, singleFD)
		}
	}
	lock.Unlock()

	return resources.NewIncMap(func(index tla.TLAValue) distsys.ArchetypeResource {
		res, ok := fdMap.Get(index)
		if !ok {
			panic("failure detector not found")
		}
		return res
	})
}

func newClientCtx(cId int, c configs.Root, reqCh, respCh, timeoutCh chan tla.TLAValue) *distsys.MPCalContext {
	self := clientId(c, cId)
	tlaSelf := tla.MakeTLANumber(int32(self))

	constants := makeConstants(c)
	net := newNetwork(c, tlaSelf)
	netLen := resources.NewMailboxesLength(net)
	fd := getFailureDetector(c)
	reqChRes := resources.NewInputChan(reqCh,
		resources.WithInputChanReadTimeout(c.InputChanReadTimeout))
	respChRes := resources.NewOutputChan(respCh)
	timeoutChRes := resources.NewInputChan(timeoutCh,
		resources.WithInputChanReadTimeout(c.InputChanReadTimeout))

	ctx := distsys.NewMPCalContext(
		tlaSelf, AClient,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", net),
		distsys.EnsureArchetypeRefParam("netLen", netLen),
		distsys.EnsureArchetypeRefParam("fd", fd),
		distsys.EnsureArchetypeRefParam("reqCh", reqChRes),
		distsys.EnsureArchetypeRefParam("respCh", respChRes),
		distsys.EnsureArchetypeRefParam("timeout", timeoutChRes),
	)
	return ctx
}

type Client struct {
	Id     int
	Config configs.Root

	ctx       *distsys.MPCalContext
	reqCh     chan tla.TLAValue
	respCh    chan tla.TLAValue
	timeoutCh chan tla.TLAValue
	timer     *time.Timer
}

func NewClient(clientId int, c configs.Root) *Client {
	reqCh := make(chan tla.TLAValue)
	respCh := make(chan tla.TLAValue)
	timeoutCh := make(chan tla.TLAValue)
	ctx := newClientCtx(clientId, c, reqCh, respCh, timeoutCh)

	return &Client{
		Id:        clientId,
		Config:    c,
		ctx:       ctx,
		reqCh:     reqCh,
		respCh:    respCh,
		timeoutCh: timeoutCh,
		timer:     time.NewTimer(c.ClientRequestTimeout),
	}
}

type RequestType int

const (
	GetRequestType = iota + 1
	PutRequestType
)

type Request interface {
	Type() RequestType
	String() string
}

type GetRequest struct {
	Key string
}

func (r GetRequest) Type() RequestType {
	return GetRequestType
}

func (r GetRequest) String() string {
	return fmt.Sprintf("GET %s", r.Key)
}

type PutRequest struct {
	Key   string
	Value string
}

func (r PutRequest) Type() RequestType {
	return PutRequestType
}

func (r PutRequest) String() string {
	return fmt.Sprintf("PUT %s %s", r.Key, r.Value)
}

type Response struct {
	Index int
	OK    bool
	Key   string
	Value string
}

func (r Response) String() string {
	return fmt.Sprintf("Key: %s, Value: %s, OK: %v", r.Key, r.Value, r.OK)
}

func (c *Client) parseResp(tlaResp tla.TLAValue) Response {
	tlaMResp := tlaResp.ApplyFunction(tla.MakeTLAString("mresponse"))
	tlaFunc := tlaMResp.AsFunction()
	getField := func(fieldName string) (interface{}, bool) {
		return tlaFunc.Get(tla.MakeTLAString(fieldName))
	}

	var index int
	if val, ok := getField("idx"); ok {
		index = int(val.(tla.TLAValue).AsNumber())
	}

	var ok bool
	if val, fOk := getField("ok"); fOk {
		ok = val.(tla.TLAValue).AsBool()
	}

	var key string
	if val, ok := getField("key"); ok {
		key = val.(tla.TLAValue).AsString()
	}

	var value string
	if val, ok := getField("value"); ok {
		tlaValue := val.(tla.TLAValue)
		if !tlaValue.Equal(Nil(c.ctx.IFace())) {
			value = tlaValue.AsString()
		}
	}

	return Response{
		Index: index,
		OK:    ok,
		Key:   key,
		Value: value,
	}
}

func (c *Client) Run(reqCh chan Request, respCh chan Response) error {
	errCh := make(chan error)
	go func() {
		err := c.ctx.Run()
		log.Printf("archetype %v finished, err = %v", c.ctx.IFace().Self(), err)
		errCh <- err
	}()

	for req := range reqCh {
		var tlaReq tla.TLAValue
		switch typedReq := req.(type) {
		case GetRequest:
			tlaReq = tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("type"), Value: Get(c.ctx.IFace())},
				{Key: tla.MakeTLAString("key"), Value: tla.MakeTLAString(typedReq.Key)},
			})
		case PutRequest:
			tlaReq = tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("type"), Value: Put(c.ctx.IFace())},
				{Key: tla.MakeTLAString("key"), Value: tla.MakeTLAString(typedReq.Key)},
				{Key: tla.MakeTLAString("value"), Value: tla.MakeTLAString(typedReq.Value)},
			})
		}
		c.reqCh <- tlaReq

		var tlaResp tla.TLAValue
	forLoop:
		for {
			if !c.timer.Stop() {
				<-c.timer.C
			}
			c.timer.Reset(c.Config.ClientRequestTimeout)

			select {
			case tlaResp = <-c.respCh:
				break forLoop
			case <-c.timer.C:
				log.Printf("client %d sending timeout", c.Id)

				c.timer.Reset(c.Config.ClientRequestTimeout)
				select {
				case c.timeoutCh <- tla.TLA_TRUE:
					log.Printf("client %d sent timeout", c.Id)
				case <-c.timer.C:
					log.Printf("client %d cannot timeout", c.Id)
				}
			}
		}
		respCh <- c.parseResp(tlaResp)
	}

	return <-errCh
}

func (c *Client) Close() error {
	c.ctx.Stop()
	c.timer.Stop()
	return nil
}
