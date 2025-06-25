package bootstrap

import (
	"fmt"
	"log"
	"sync"
	"time"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/hashmap"
	"github.com/DistCompiler/pgo/distsys/resources"
	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/DistCompiler/pgo/systems/raftkvs"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
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
	defer lock.Unlock()
	for i := 1; i <= c.NumServers; i++ {
		tlaIndex := tla.MakeNumber(int32(i))
		_, ok := fdMap.Get(tlaIndex)
		if !ok {
			singleFD := newSingleFD(c, tlaIndex)
			fdMap.Set(tlaIndex, singleFD)
		}
	}

	return resources.NewHashMap(fdMap)
}

func newClientCtx(self tla.Value, c configs.Root, reqCh, respCh, timeoutCh chan tla.Value) *distsys.MPCalContext {
	constants := makeConstants(c)
	net := newNetwork(self, c)
	netLen := resources.NewMailboxesLength(net)
	fd := getFailureDetector(c)
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
	reqCh     chan tla.Value
	respCh    chan tla.Value
	timeoutCh chan tla.Value
	timer     *time.Timer
}

func NewClient(clientId int, c configs.Root) *Client {
	clientIdOffset := 6 * c.NumServers
	self := tla.MakeNumber(int32(clientIdOffset + clientId))

	reqCh := make(chan tla.Value)
	respCh := make(chan tla.Value)
	timeoutCh := make(chan tla.Value)
	ctx := newClientCtx(self, c, reqCh, respCh, timeoutCh)

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

type ResponseType int

const (
	GetResponseType = iota + 1
	PutResponseType
)

type Response struct {
	Index int
	OK    bool
	Key   string
	Value string

	typ ResponseType
}

func (r Response) Type() ResponseType {
	return r.typ
}

func (c *Client) parseResp(tlaResp tla.Value) Response {
	tlaMResp := tlaResp.ApplyFunction(tla.MakeString("mresponse"))
	tlaFunc := tlaMResp.AsFunction()
	getField := func(fieldName string) (interface{}, bool) {
		return tlaFunc.Get(tla.MakeString(fieldName))
	}

	var index int
	if val, ok := getField("idx"); ok {
		index = int(val.(tla.Value).AsNumber())
	}

	var ok bool
	if val, fOk := getField("ok"); fOk {
		ok = val.(tla.Value).AsBool()
	}

	var key string
	if val, ok := getField("key"); ok {
		key = val.(tla.Value).AsString()
	}

	var value string
	if val, ok := getField("value"); ok {
		Value := val.(tla.Value)
		if !Value.Equal(raftkvs.Nil(c.ctx.IFace())) {
			value = Value.AsString()
		}
	}

	var typ ResponseType
	if val, ok := getField("mtype"); ok {
		Value := val.(tla.Value)
		if Value.Equal(raftkvs.ClientGetResponse(c.ctx.IFace())) {
			typ = GetResponseType
		} else if Value.Equal(raftkvs.ClientPutResponse(c.ctx.IFace())) {
			typ = PutResponseType
		}
	}

	return Response{
		Index: index,
		OK:    ok,
		Key:   key,
		Value: value,
		typ:   typ,
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
		var tlaReq tla.Value
		switch typedReq := req.(type) {
		case GetRequest:
			tlaReq = tla.MakeRecord([]tla.RecordField{
				{Key: tla.MakeString("type"), Value: raftkvs.Get(c.ctx.IFace())},
				{Key: tla.MakeString("key"), Value: tla.MakeString(typedReq.Key)},
			})
		case PutRequest:
			tlaReq = tla.MakeRecord([]tla.RecordField{
				{Key: tla.MakeString("type"), Value: raftkvs.Put(c.ctx.IFace())},
				{Key: tla.MakeString("key"), Value: tla.MakeString(typedReq.Key)},
				{Key: tla.MakeString("value"), Value: tla.MakeString(typedReq.Value)},
			})
		}
		c.reqCh <- tlaReq

		var tlaResp tla.Value
		timerDrained := false
	forLoop:
		for {
			if !c.timer.Stop() {
				if !timerDrained {
					<-c.timer.C
				}
			}
			c.timer.Reset(c.Config.ClientRequestTimeout)
			timerDrained = false

			select {
			case tlaResp = <-c.respCh:
				break forLoop
			case <-c.timer.C:
				log.Printf("client %d sending timeout", c.Id)

				c.timer.Reset(c.Config.ClientRequestTimeout)
				select {
				case c.timeoutCh <- tla.ModuleTRUE:
					log.Printf("client %d sent timeout", c.Id)
				case <-c.timer.C:
					log.Printf("client %d cannot timeout", c.Id)
					timerDrained = true
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
