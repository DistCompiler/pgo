package main

import (
	"log"
	"time"

	"example.org/keylock_verdi"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

const serverHost = "localhost:8001"
const serverName = "server"

func main() {

	numClientsConstant := distsys.DefineConstantValue("NUM_CLIENTS", tla.MakeTLANumber(1))
	lockServerID := distsys.DefineConstantValue("LOCK_SERVER_ID", tla.MakeTLAString(serverName))

	clientMap := map[string]string{
		"client1": "localhost:8002",
		"client2": "localhost:8003",
	}

	serverCtx := createServerContext(numClientsConstant, lockServerID, clientMap)
	defer func() {
		err := serverCtx.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	client1Ctx := createClientContext("client1", numClientsConstant, lockServerID, clientMap)
	defer func() {
		err := client1Ctx.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	client2Ctx := createClientContext("client2", numClientsConstant, lockServerID, clientMap)
	defer func() {
		err := client2Ctx.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	go func() {
		err := serverCtx.Run()
		if err != nil {
			panic(err)
		}
	}()

	go func() {
		err := client1Ctx.Run()
		if err != nil {
			panic(err)
		}
	}()

	go func() {
		err := client2Ctx.Run()
		if err != nil {
			panic(err)
		}
	}()

	time.Sleep(5 * time.Second)

}

func createServerContext(numClientsConstant distsys.MPCalContextConfigFn, lockServerID distsys.MPCalContextConfigFn, clientMap map[string]string) *distsys.MPCalContext {
	serverCtx := distsys.NewMPCalContext(tla.MakeTLAString(serverName), keylock_verdi.AServer,
		numClientsConstant,
		lockServerID,
		distsys.EnsureArchetypeRefParam("network", resources.TCPMailboxesArchetypeResourceMaker(func(index tla.TLAValue) (resources.TCPMailboxKind, string) {
			switch index.AsString() {
			case serverName:
				return resources.TCPMailboxesLocal, serverHost
			default:
				return resources.TCPMailboxesRemote, clientMap[index.AsString()]
			}

		})))

	return serverCtx
}

func createClientContext(clientName string, numClientsConstant distsys.MPCalContextConfigFn, lockServerID distsys.MPCalContextConfigFn, clientMap map[string]string) *distsys.MPCalContext {
	clientCtx := distsys.NewMPCalContext(tla.MakeTLAString(clientName), keylock_verdi.AClient,
		numClientsConstant,
		lockServerID,
		distsys.EnsureArchetypeRefParam("network", resources.TCPMailboxesArchetypeResourceMaker(func(index tla.TLAValue) (resources.TCPMailboxKind, string) {
			switch index.AsString() {
			case serverName:
				return resources.TCPMailboxesRemote, serverHost
			default:
				return resources.TCPMailboxesLocal, clientMap[index.AsString()]
			}

		})))

	return clientCtx
}
