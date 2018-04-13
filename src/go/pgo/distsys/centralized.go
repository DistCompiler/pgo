package distsys

import (
	"bytes"
	"encoding/gob"
	"encoding/hex"
	"fmt"
	"net"
	"net/rpc"
	"sort"
	"sync"
	"time"
)

type StateServerError int

const (
	ErrorKeyNotFound StateServerError = iota
	ErrorUnknownClientId
	ErrorUnknownLockId
	ErrorTryAgain
	ErrorInvalidRequest
)

func (e StateServerError) Error() string {
	switch e {
	case ErrorKeyNotFound:
		return "Key not found"
	case ErrorUnknownClientId:
		return "Unknown client ID"
	case ErrorUnknownLockId:
		return "Unknown lock ID"
	case ErrorTryAgain:
		return "Try again"
	case ErrorInvalidRequest:
		return "Invalid request"
	default:
		panic("Unknown StateServerError value")
	}
}

type ClientInfo struct {
	IpPort string // where the client listens
}

type ClientConfig struct {
	ClientId          string
	HeartBeatInterval int // in seconds
}

type client struct {
	clientId  string
	ipPort    string
	rpcClient *rpc.Client
	lastHeard time.Time
}

type SLock struct {
	ClientId string
	LockId   string
}

type AcquireRequest struct {
	ClientId string
	ToRead   []string
	ToWrite  []string
}

type AcquireResponse struct {
	Lock   SLock
	Values map[string]interface{}
}

type ReleaseRequest struct {
	Lock   SLock
	Values []interface{}
}

type slot struct {
	locked bool
	value  interface{}
}

type lockInfo struct {
	clientId string
	names    []string
}

/// Server is an interface of a state server.
type Server interface {
	// Register notifies the server of the client also starts a reverse
	// RPC communication channel from the server to the client
	Register(clientInfo ClientInfo, clientConfig *ClientConfig) error
	// HeartBeat notifies the server whether the client is alive
	HeartBeat(clientId string, ok *bool) error
	SAcquire(request AcquireRequest, response *AcquireResponse) error
	SRelease(request ReleaseRequest, ok *bool) error
}

/// StateServer implements a centralized state server.
/// Example usage:
///     server := distsys.NewStateServer("127.0.0.1:12345")
///     server.HeartBeatInterval = 3 // Optional
///     go server.Serve()
type StateServer struct {
	HeartBeatInterval int // in seconds, defaults to 3 seconds

	ipPort    string
	clientId  string
	startChan chan bool
	lock      sync.RWMutex
	clients   map[string]*client
	data      map[string]*slot
	locks     map[string]*lockInfo
	rpcServer *rpc.Server
}

func NewStateServer(ipPort string /*, peers []string, varLocations map[string][]string*/, initialValues map[string]interface{}) *StateServer {
	startChan := make(chan bool, 1)
	startChan <- true
	clientId := RandString(32)
	data := make(map[string]*slot)
	for k, v := range initialValues {
		data[k] = &slot{
			locked: false,
			value:  v,
		}
	}
	return &StateServer{
		HeartBeatInterval: 3,
		ipPort:            ipPort,
		clientId:          clientId,
		startChan:         startChan,
		data:              data,
		locks:             make(map[string]*lockInfo),
		clients: map[string]*client{
			clientId: &client{},
		},
	}
}

func monitor(s *StateServer, c *client) {
	for {
		s.lock.RLock()
		if c.lastHeard.Add(time.Duration(s.HeartBeatInterval*2) * time.Second).Before(time.Now()) {
			s.lock.RUnlock()
			s.lock.Lock()
			delete(s.clients, c.clientId)
			s.lock.Unlock()
			return
		}
		s.lock.RUnlock()
		time.Sleep(time.Duration(s.HeartBeatInterval) * time.Second)
	}
}

func (s *StateServer) Register(clientInfo ClientInfo, clientConfig *ClientConfig) error {
	s.lock.Lock()
	defer s.lock.Unlock()
	rpcClient, err := rpc.Dial("tcp", clientInfo.IpPort)
	if err != nil {
		return err
	}
	for {
		// TODO parameterize length of client IDs
		clientConfig.ClientId = RandString(32)
		if _, exists := s.clients[clientConfig.ClientId]; !exists {
			break
		}
	}
	c := &client{
		clientId:  clientConfig.ClientId,
		ipPort:    clientInfo.IpPort,
		rpcClient: rpcClient,
		lastHeard: time.Now(),
	}
	s.clients[clientConfig.ClientId] = c
	go monitor(s, c)
	return nil
}

func (s *StateServer) HeartBeat(clientId string, ok *bool) error {
	s.lock.Lock()
	defer s.lock.Unlock()

	*ok = false

	c, exists := s.clients[clientId]
	if !exists {
		return ErrorUnknownClientId
	}
	c.lastHeard = time.Now()
	*ok = true
	return nil
}

func (s *StateServer) SAcquire(request AcquireRequest, response *AcquireResponse) error {
	m := make(map[string]interface{})
	nread := len(request.ToRead)
	nwrite := len(request.ToWrite)
	names := make([]string, nread+nwrite)
	for i, name := range request.ToRead {
		names[i] = name
	}
	for i, name := range request.ToWrite {
		names[nread+i] = name
	}
	sort.Strings(names)
	s.lock.Lock()
	defer s.lock.Unlock()
	if _, exists := s.clients[request.ClientId]; !exists {
		return ErrorUnknownClientId
	}
	for _, name := range names {
		spot, exists := s.data[name]
		if spot.locked {
			return ErrorTryAgain
		}
		if !exists {
			return ErrorKeyNotFound
		}
		m[name] = spot.value
		spot.locked = true
	}
	lockId := ""
	for {
		// TODO parameterize length of lock IDs
		lockId = RandString(32)
		if _, exists := s.locks[lockId]; !exists {
			break
		}
	}
	s.locks[lockId] = &lockInfo{
		clientId: request.ClientId,
		names:    names,
	}
	response.Lock = SLock{
		ClientId: request.ClientId,
		LockId:   lockId,
	}
	response.Values = m
	return nil
}

func (s *StateServer) SRelease(request ReleaseRequest, ok *bool) error {
	*ok = false
	s.lock.Lock()
	defer s.lock.Unlock()
	if _, exists := s.clients[request.Lock.ClientId]; !exists {
		return ErrorUnknownClientId
	}
	if linfo, exists := s.locks[request.Lock.LockId]; !exists {
		return ErrorUnknownLockId
	} else {
		if linfo.clientId != request.Lock.ClientId {
			return ErrorInvalidRequest
		}
		for i, name := range linfo.names {
			s.data[name].value = request.Values[i]
			s.data[name].locked = false
		}
		*ok = true
	}
	return nil
}

func (s *StateServer) Acquire(reads []string, writes []string) (Lock, map[string]interface{}) {
	for {
		var response AcquireResponse
		err := s.SAcquire(AcquireRequest{
			ClientId: s.clientId,
			ToRead:   reads,
			ToWrite:  writes,
		}, &response)
		ssErr, ok := err.(StateServerError)
		if ok && ssErr == ErrorTryAgain {
			continue
		}
		if err != nil {
			panic(err)
		}
		return Lock{response.Lock}, response.Values
	}
}

func (s *StateServer) Release(lock Lock, values []interface{}) {
	ok := false
	err := s.SRelease(ReleaseRequest{
		Lock:   lock.sLock,
		Values: values,
	}, &ok)
	if !ok || err != nil {
		panic(err)
	}
}

func (s *StateServer) Serve() {
	server := rpc.NewServer()
	server.Register(Server(s))
	tcpAddr, err := net.ResolveTCPAddr("tcp", s.ipPort)
	if err != nil {
		panic(err)
	}
	listener, err := net.ListenTCP("tcp", tcpAddr)
	if err != nil {
		panic(err)
	}
	s.rpcServer = server
	server.Accept(listener)
}

func (s *StateServer) StartChan() chan bool {
	return s.startChan
}

type CentralizedStateClient interface {
	StartAlgorithm(_ignored bool, _ignoredResult *bool) error
}

type Lock struct {
	sLock SLock
}

type State interface {
	Acquire(reads []string, writes []string) (Lock, map[string]interface{})
	Release(lock Lock, values []interface{})
	StartChan() chan bool
}

type CentralizedState struct {
	ipPort     string
	endpoints  []string
	rpcServer  *rpc.Server
	rpcClients []*rpc.Client
	ids        []string
	startChan  chan bool
}

func NewCentralizedState(ipPort string, endpoints []string) (*CentralizedState, error) {
	tcpAddr, err := net.ResolveTCPAddr("tcp", ipPort)
	if err != nil {
		return nil, err
	}
	listener, err := net.ListenTCP("tcp", tcpAddr)
	if err != nil {
		return nil, err
	}
	server := rpc.NewServer()
	state := &CentralizedState{
		ipPort:    ipPort,
		endpoints: endpoints,
		rpcServer: server,
		startChan: make(chan bool),
	}
	server.Register(CentralizedStateClient(state))
	go server.Accept(listener)
	wg := sync.WaitGroup{}
	clients := make([]*rpc.Client, len(endpoints))
	ids := make([]string, len(endpoints))
	for i, e := range endpoints {
		wg.Add(1)
		go func(endpoint string, i int) {
			for {
				c, err := rpc.Dial("tcp", endpoint)
				if err != nil {
					continue
				}
				var clientConfig ClientConfig
				err = c.Call("Server.Register", ClientInfo{ipPort}, &clientConfig)
				if err != nil {
					c.Close()
					continue
				}
				go heartBeat(c, clientConfig.ClientId, clientConfig.HeartBeatInterval)
				clients[i] = c
				ids[i] = clientConfig.ClientId
				wg.Done()
				return
			}
		}(e, i)
	}
	wg.Wait()
	state.rpcClients = clients
	state.ids = ids
	return state, nil
}

func heartBeat(c *rpc.Client, clientId string, heartBeatInterval int) {
	duration := time.Duration(heartBeatInterval) * time.Second
	var ok bool
	for {
		err := c.Call("Server.HeartBeat", clientId, &ok)
		if err != nil || !ok {
			panic(err)
		}
		time.Sleep(duration)
	}
}

func (s *CentralizedState) StartAlgorithm(_ignored bool, _ignoredResult *bool) error {
	s.startChan <- true
	return nil
}

func (s *CentralizedState) Acquire(reads []string, writes []string) (Lock, map[string]interface{}) {
	for {
		var response AcquireResponse
		// TODO load balance among servers
		err := s.rpcClients[0].Call("Server.SAcquire", AcquireRequest{
			ClientId: s.ids[0],
			ToRead:   reads,
			ToWrite:  writes,
		}, &response)
		ssErr, ok := err.(StateServerError)
		if ok && ssErr == ErrorTryAgain {
			continue
		}
		if err != nil {
			panic(err)
		}
		return Lock{response.Lock}, response.Values
	}
}

func (s *CentralizedState) Release(lock Lock, values []interface{}) {
	ok := false
	err := s.rpcClients[0].Call("Server.SRelease", ReleaseRequest{
		Lock:   lock.sLock,
		Values: values,
	}, &ok)
	if !ok || err != nil {
		panic(err)
	}
}

func marshal(value interface{}) string {
	buffer := bytes.Buffer{}
	encoder := gob.NewEncoder(&buffer)
	err := encoder.Encode(value)
	if err != nil {
		panic(fmt.Sprintf("Unable to GobEncode %v, err = %s", value, err.Error()))
	}
	return hex.EncodeToString(buffer.Bytes())
}

func unmarshal(value string, variable interface{}) {
	buffer, err := hex.DecodeString(value)
	if err != nil {
		panic(fmt.Sprintf("Unable to hex.Decode %s, err = %s", value, err.Error()))
	}
	decoder := gob.NewDecoder(bytes.NewReader(buffer))
	err = decoder.Decode(variable)
	if err != nil {
		panic(fmt.Sprintf("Unable to GobDecode %v, err = %s", buffer, err.Error()))
	}
}

func (self *CentralizedState) StartChan() chan bool {
	return self.startChan
}
