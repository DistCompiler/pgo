package loadbalancer

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/archetype_resources"
	"io/ioutil"
	"math/rand"
	"os"
	"path"
	"testing"
	"time"
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

	go func() {
		ctx := distsys.NewMPCalContext()
		self := distsys.NewTLANumber(0)
		mailboxes := ctx.EnsureArchetypeResourceByName("mailboxes", archetype_resources.TCPMailboxesArchetypeResourceMaker(func(index distsys.TLAValue) (archetype_resources.TCPMailboxKind, string) {
			switch index.AsNumber() {
			case 0:
				return archetype_resources.TCPMailboxesLocal, "localhost:8001"
			case 1:
				return archetype_resources.TCPMailboxesRemote, "localhost:8002"
			case 2:
				return archetype_resources.TCPMailboxesRemote, "localhost:8003"
			default:
				panic(fmt.Errorf("unknown mailbox index %v", index))
			}
		}))
		err := ALoadBalancer(ctx, self, constants, mailboxes)
		if err != nil {
			panic(err)
		}
	}()

	go func() {
		ctx := distsys.NewMPCalContext()
		self := distsys.NewTLANumber(1)
		mailboxes := ctx.EnsureArchetypeResourceByName("mailboxes", archetype_resources.TCPMailboxesArchetypeResourceMaker(func(index distsys.TLAValue) (archetype_resources.TCPMailboxKind, string) {
			switch index.AsNumber() {
			case 0:
				return archetype_resources.TCPMailboxesRemote, "localhost:8001"
			case 1:
				return archetype_resources.TCPMailboxesLocal, "localhost:8002"
			case 2:
				return archetype_resources.TCPMailboxesRemote, "localhost:8003"
			default:
				panic(fmt.Errorf("unknown mailbox index %v", index))
			}
		}))
		filesystem := ctx.EnsureArchetypeResourceByName("filesystem", archetype_resources.FilesystemArchetypeResourceMaker(tempDir))
		err := AServer(ctx, self, constants, mailboxes, filesystem)
		if err != nil {
			panic(err)
		}
	}()

	requestChannel := make(chan distsys.TLAValue, 32)
	responseChannel := make(chan distsys.TLAValue, 32)
	go func() {
		ctx := distsys.NewMPCalContext()
		self := distsys.NewTLANumber(2)
		mailboxes := ctx.EnsureArchetypeResourceByName("mailboxes", archetype_resources.TCPMailboxesArchetypeResourceMaker(func(index distsys.TLAValue) (archetype_resources.TCPMailboxKind, string) {
			switch index.AsNumber() {
			case 0:
				return archetype_resources.TCPMailboxesRemote, "localhost:8001"
			case 1:
				return archetype_resources.TCPMailboxesRemote, "localhost:8002"
			case 2:
				return archetype_resources.TCPMailboxesLocal, "localhost:8003"
			default:
				panic(fmt.Errorf("unknown mailbox index %v", index))
			}
		}))
		instream := ctx.EnsureArchetypeResourceByName("instream", archetype_resources.InputChannelResourceMaker(requestChannel))
		outstream := ctx.EnsureArchetypeResourceByName("outstream", archetype_resources.OutputChannelResourceMaker(responseChannel))
		err := AClient(ctx, self, constants, mailboxes, instream, outstream)
		if err != nil {
			panic(err)
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
	for i := range requestResponsePairs {
		response := <-responseChannel
		if !response.Equal(requestResponsePairs[i].Response) {
			t.Fatalf("actual response %v to request %v did not equal expected response %v", response, requestResponsePairs[i].Request, requestResponsePairs[i].Response)
		}
	}
}
