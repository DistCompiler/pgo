package loadbalancer

import (
	"fmt"
	"io/ioutil"
	"log"
	"math/rand"
	"os"
	"path"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
)

func TestOneServerOneClient(t *testing.T) {
	constants := Constants{
		LoadBalancerId: distsys.NewTLANumber(0),
		NUM_SERVERS:    distsys.NewTLANumber(1),
		NUM_CLIENTS:    distsys.NewTLANumber(1),
		GET_PAGE:       distsys.NewTLAString("GET_PAGE"),
	}

	tempDir, err := ioutil.TempDir("", "")
	if err != nil {
		panic(err)
	}
	defer func() {
		err := os.RemoveAll(tempDir)
		if err != nil {
			panic(err)
		}
	}()
	err = ioutil.WriteFile(path.Join(tempDir, "test1.txt"), []byte("test 1"), 0777)
	if err != nil {
		panic(err)
	}
	err = ioutil.WriteFile(path.Join(tempDir, "test2.txt"), []byte("test 2"), 0777)
	if err != nil {
		panic(err)
	}

	makeAddressFn := func(ownId int) func(index distsys.TLAValue) (resources.TCPMailboxKind, string) {
		return func(index distsys.TLAValue) (resources.TCPMailboxKind, string) {
			kind := [3]resources.TCPMailboxKind{resources.TCPMailboxesRemote, resources.TCPMailboxesRemote, resources.TCPMailboxesRemote}
			kind[ownId] = resources.TCPMailboxesLocal
			switch index.AsNumber() {
			case 0:
				return kind[0], "localhost:8001"
			case 1:
				return kind[1], "localhost:8002"
			case 2:
				return kind[2], "localhost:8003"
			default:
				panic(fmt.Errorf("unknown mailbox index %v", index))
			}
		}
	}

	ctxLoadBalancer := distsys.NewMPCalContext()
	go func(ctx *distsys.MPCalContext) {
		self := distsys.NewTLANumber(0)
		mailboxes := ctx.EnsureArchetypeResourceByName("mailboxes", resources.TCPMailboxesArchetypeResourceMaker(makeAddressFn(0)))
		err := ALoadBalancer(ctx, self, constants, mailboxes)
		if err != nil && err != distsys.ErrContextClosed {
			panic(err)
		}
	}(ctxLoadBalancer)

	ctxServer := distsys.NewMPCalContext()
	go func(ctx *distsys.MPCalContext) {
		self := distsys.NewTLANumber(1)
		mailboxes := ctx.EnsureArchetypeResourceByName("mailboxes", resources.TCPMailboxesArchetypeResourceMaker(makeAddressFn(1)))
		filesystem := ctx.EnsureArchetypeResourceByName("filesystem", resources.FileSystemArchetypeResourceMaker(tempDir))
		err := AServer(ctx, self, constants, mailboxes, filesystem)
		if err != nil && err != distsys.ErrContextClosed {
			panic(err)
		}
	}(ctxServer)

	ctxClient := distsys.NewMPCalContext()
	requestChannel := make(chan distsys.TLAValue, 32)
	responseChannel := make(chan distsys.TLAValue, 32)
	go func(ctx *distsys.MPCalContext) {
		self := distsys.NewTLANumber(2)
		mailboxes := ctx.EnsureArchetypeResourceByName("mailboxes", resources.TCPMailboxesArchetypeResourceMaker(makeAddressFn(2)))
		instream := ctx.EnsureArchetypeResourceByName("instream", resources.InputChannelResourceMaker(requestChannel))
		outstream := ctx.EnsureArchetypeResourceByName("outstream", resources.OutputChannelResourceMaker(responseChannel))
		err := AClient(ctx, self, constants, mailboxes, instream, outstream)
		if err != nil && err != distsys.ErrContextClosed {
			panic(err)
		}
	}(ctxClient)

	defer func() {
		if err := ctxLoadBalancer.Close(); err != nil {
			log.Println(err)
		}
		if err := ctxServer.Close(); err != nil {
			log.Println(err)
		}
		if err := ctxClient.Close(); err != nil {
			log.Println(err)
		}
	}()

	type RequestResponse struct {
		Request, Response distsys.TLAValue
	}
	choices := []RequestResponse{
		{Request: distsys.NewTLAString("test1.txt"), Response: distsys.NewTLAString("test 1")},
		{Request: distsys.NewTLAString("test2.txt"), Response: distsys.NewTLAString("test 2")},
	}

	rand.Seed(time.Now().UnixNano())
	requestResponsePairs := make([]RequestResponse, 32)
	for i := 0; i < 32; i++ {
		requestResponsePairs[i] = choices[rand.Intn(len(choices))]
	}
	// send requests
	for i := range requestResponsePairs {
		requestChannel <- requestResponsePairs[i].Request
	}
	var receivedValues []distsys.TLAValue
	for range requestResponsePairs {
		response := <-responseChannel
		receivedValues = append(receivedValues, response)
	}
	close(responseChannel)
	time.Sleep(100 * time.Millisecond) // make sure the model isn't replying more than necessary
	// if so, it will crash due to the channel being closed, assuming it would reply again within 100ms

	// compare received values
	for i, receivedValue := range receivedValues {
		if !requestResponsePairs[i].Response.Equal(receivedValue) {
			var expectedValues []distsys.TLAValue
			for _, pair := range requestResponsePairs {
				expectedValues = append(expectedValues, pair.Response)
			}
			t.Fatalf("expected received values %v do not match actual received values %v", expectedValues, receivedValues)
		}
	}
}
