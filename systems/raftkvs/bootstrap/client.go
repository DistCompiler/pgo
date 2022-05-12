package bootstrap

import (
	"log"
	"time"

	"github.com/DistCompiler/pgo/systems/raftkvs"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func newClientCtx(self tla.TLAValue, c configs.Root, reqCh, respCh, timeoutCh chan tla.TLAValue) *distsys.MPCalContext {
	constants := makeConstants(c)
	net := newNetwork(self, c)
	netLen := resources.NewMailboxesLength(net)
	fd := resources.NewFailureDetector(
		func(index tla.TLAValue) string {
			return fdAddrMapper(c, index)
		},
		resources.WithFailureDetectorPullInterval(c.FD.PullInterval),
		resources.WithFailureDetectorTimeout(c.FD.Timeout),
	)
	reqChRes := resources.NewInputChan(reqCh,
		resources.WithInputChanReadTimeout(c.InputChanReadTimeout))
	respChRes := resources.NewOutputChan(respCh)
	timeoutChRes := resources.NewInputChan(timeoutCh,
		resources.WithInputChanReadTimeout(c.InputChanReadTimeout))

	ctx := distsys.NewMPCalContext(
		self, raftkvs.AClient,
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
}

func NewClient(clientId int, c configs.Root) *Client {
	clientIdOffset := 6 * c.NumServers
	self := tla.MakeTLANumber(int32(clientIdOffset + clientId))

	reqCh := make(chan tla.TLAValue)
	respCh := make(chan tla.TLAValue)
	timeoutCh := make(chan tla.TLAValue)
	ctx := newClientCtx(self, c, reqCh, respCh, timeoutCh)

	return &Client{
		Id:        clientId,
		Config:    c,
		ctx:       ctx,
		reqCh:     reqCh,
		respCh:    respCh,
		timeoutCh: timeoutCh,
	}
}

type RequestType int

const (
	GetRequestType = iota + 1
	PutRequestType
)

type Request interface {
	Type() RequestType
}

type GetRequest struct {
	Key string
}

func (r GetRequest) Type() RequestType {
	return GetRequestType
}

type PutRequest struct {
	Key   string
	Value string
}

func (r PutRequest) Type() RequestType {
	return PutRequestType
}

type Response struct {
	Index int
	OK    bool
	Key   string
	Value interface{}
}

func parseResp(tlaResp tla.TLAValue) Response {
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

	var value interface{}
	if val, ok := getField("value"); ok {
		value = val.(tla.TLAValue)
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
				{Key: tla.MakeTLAString("type"), Value: raftkvs.Get(c.ctx.IFace())},
				{Key: tla.MakeTLAString("key"), Value: tla.MakeTLAString(typedReq.Key)},
			})
		case PutRequest:
			tlaReq = tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("type"), Value: raftkvs.Put(c.ctx.IFace())},
				{Key: tla.MakeTLAString("key"), Value: tla.MakeTLAString(typedReq.Key)},
				{Key: tla.MakeTLAString("value"), Value: tla.MakeTLAString(typedReq.Value)},
			})
		}
		c.reqCh <- tlaReq

		var tlaResp tla.TLAValue
	forLoop:
		for {
			select {
			case tlaResp = <-c.respCh:
				break forLoop
			case <-time.After(c.Config.ClientRequestTimeout):
				log.Printf("sending timeout")
				select {
				case c.timeoutCh <- tla.TLA_TRUE:
					log.Printf("sent timeout")
				case <-time.After(c.Config.ClientRequestTimeout):
				}
			}
		}
		respCh <- Response(parseResp(tlaResp))
	}

	return <-errCh
}

func (c *Client) Close() error {
	c.ctx.Stop()
	return nil
}
