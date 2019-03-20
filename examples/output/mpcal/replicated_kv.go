package replicated_kv

import (
	"pgo/distsys"
	"sort"
)

var DISCONNECT_MSG string

var GET_MSG string

var GET_RESPONSE string

var NULL_MSG string

var NUM_CLIENTS int

var NUM_REPLICAS int

var PUT_MSG string

var PUT_RESPONSE string

func init() {
	DISCONNECT_MSG = "disconnect"
	GET_MSG = "get"
	GET_RESPONSE = "get_response"
	NULL_MSG = "clock_update"
	NUM_CLIENTS = 2
	NUM_REPLICAS = 3
	PUT_MSG = "put"
	PUT_RESPONSE = "put_response"
	distsys.DefineCustomType(map[string]interface{}{})
}

func NUM_NODES() int {
	return NUM_REPLICAS + NUM_CLIENTS
}

func ClientSet() []int {
	tmpRange := make([]int, NUM_NODES()-1-NUM_REPLICAS+1)
	for i := NUM_REPLICAS; i <= NUM_NODES()-1; i++ {
		tmpRange[i-NUM_REPLICAS] = i
	}
	return tmpRange
}

func AReplica(self int, clients distsys.ArchetypeResourceCollection, replicas distsys.ArchetypeResourceCollection, kv distsys.ArchetypeResourceCollection) error {
	liveClients := ClientSet()
	function := make([]struct {
		key   int
		value []map[string]interface{}
	}, 0, len(liveClients))
	for _, c := range liveClients {
		function = append(function, struct {
			key   int
			value []map[string]interface{}
		}{key: c, value: []map[string]interface{}{}})
	}
	pendingRequests := function
	stableMessages := []map[string]interface{}{}
	var i int
	var firstPending map[string]interface{}
	var timestamp int
	var nextClient int
	var lowestPending int
	var chooseMessage bool
	function0 := make([]struct {
		key   int
		value int
	}, 0, len(liveClients))
	for _, c := range liveClients {
		function0 = append(function0, struct {
			key   int
			value int
		}{key: c, value: 0})
	}
	currentClocks := function0
	var minClock int
	var continue0 bool
	var pendingClients []int
	var clientsIter []int
	var msg map[string]interface{}
	var ok interface{}
	var key interface{}
	var val interface{}
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// replicaLoop:
	acquiredResources = map[string]map[interface{}]bool{}
	for {
		if !true {
			break
		}
		stableMessages = []map[string]interface{}{}
		continue0 = true

		// receiveClientRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		if _, ok0 := acquiredResources["replicas"]; !ok0 {
			acquiredResources["replicas"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["replicas"][self]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, replicas.Get(self))
			if err != nil {
				return err
			}
			acquiredResources["replicas"][self] = true
		}
		msg = replicas.Get(self).Read().(map[string]interface{})
		for r, _ := range acquiredResources["replicas"] {
			err = distsys.ReleaseResources(replicas.Get(r))
			if err != nil {
				return err
			}
		}

		// clientDisconnected:
		acquiredResources = map[string]map[interface{}]bool{}
		if msg["op"].(string) == DISCONNECT_MSG {
			tmpSet := make([]int, 0, len(liveClients))
			for _, v := range liveClients {
				if v != msg["client"].(int) {
					tmpSet = append(tmpSet, v)
				}
			}
			liveClients = tmpSet
		}

		// replicaGetRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		if msg["op"].(string) == GET_MSG {
			index := sort.SearchInts(liveClients, msg["client"].(int))
			if !(index < len(liveClients) && liveClients[index] == msg["client"].(int)) {
				panic("((msg).client) \\in (liveClients)")
			}
			key0 := msg["client"].(int)
			index0 := sort.Search(len(currentClocks), func(i0 int) bool {
				return !(currentClocks[i0].key < key0)
			})
			currentClocks[index0].value = msg["timestamp"].(int)
			key1 := msg["client"].(int)
			index1 := sort.Search(len(pendingRequests), func(i1 int) bool {
				return !(pendingRequests[i1].key < key1)
			})
			key2 := msg["client"].(int)
			index2 := sort.Search(len(pendingRequests), func(i2 int) bool {
				return !(pendingRequests[i2].key < key2)
			})
			tmpSlice := make([]map[string]interface{}, len(pendingRequests[index2].value), len(pendingRequests[index2].value)+1)
			copy(tmpSlice, pendingRequests[index2].value)
			tmpSlice = append(tmpSlice, msg)
			pendingRequests[index1].value = tmpSlice
		}

		// replicaPutRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		if msg["op"].(string) == PUT_MSG {
			key0 := msg["client"].(int)
			index := sort.Search(len(currentClocks), func(i0 int) bool {
				return !(currentClocks[i0].key < key0)
			})
			currentClocks[index].value = msg["timestamp"].(int)
			key1 := msg["client"].(int)
			index0 := sort.Search(len(pendingRequests), func(i1 int) bool {
				return !(pendingRequests[i1].key < key1)
			})
			key2 := msg["client"].(int)
			index1 := sort.Search(len(pendingRequests), func(i2 int) bool {
				return !(pendingRequests[i2].key < key2)
			})
			tmpSlice := make([]map[string]interface{}, len(pendingRequests[index1].value), len(pendingRequests[index1].value)+1)
			copy(tmpSlice, pendingRequests[index1].value)
			tmpSlice = append(tmpSlice, msg)
			pendingRequests[index0].value = tmpSlice
		}

		// replicaNullRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		if msg["op"].(string) == NULL_MSG {
			key0 := msg["client"].(int)
			index := sort.Search(len(currentClocks), func(i0 int) bool {
				return !(currentClocks[i0].key < key0)
			})
			currentClocks[index].value = msg["timestamp"].(int)
		}

		// findStableRequestsLoop:
		acquiredResources = map[string]map[interface{}]bool{}
		for {
			if !continue0 {
				break
			}
			tmpSet := make([]int, 0)
			for _, c := range liveClients {
				key0 := c
				index := sort.Search(len(pendingRequests), func(i0 int) bool {
					return !(pendingRequests[i0].key < key0)
				})
				if len(pendingRequests[index].value) > 0 {
					tmpSet = append(tmpSet, c)
				}
			}
			pendingClients = tmpSet
			nextClient = NUM_NODES() + 1
			clientsIter = liveClients
			i = 0
			minClock = 0

			// findMinClock:
			acquiredResources = map[string]map[interface{}]bool{}
			for {
				if !(i < len(clientsIter)) {
					break
				}
				client := clientsIter[0]
				key0 := client
				index := sort.Search(len(currentClocks), func(i0 int) bool {
					return !(currentClocks[i0].key < key0)
				})
				if minClock == 0 || currentClocks[index].value < minClock {
					key1 := client
					index0 := sort.Search(len(currentClocks), func(i1 int) bool {
						return !(currentClocks[i1].key < key1)
					})
					minClock = currentClocks[index0].value
				}
				tmpSet0 := make([]int, 0, len(clientsIter))
				for _, v := range clientsIter {
					if v != client {
						tmpSet0 = append(tmpSet0, v)
					}
				}
				clientsIter = tmpSet0
				acquiredResources = map[string]map[interface{}]bool{}
			}
			lowestPending = minClock + 1
			i = 0

			// findMinClient:
			acquiredResources = map[string]map[interface{}]bool{}
			for {
				if !(i < len(pendingClients)) {
					break
				}
				client := pendingClients[0]
				key0 := client
				index := sort.Search(len(pendingRequests), func(i0 int) bool {
					return !(pendingRequests[i0].key < key0)
				})
				firstPending = pendingRequests[index].value[0]
				if !(firstPending["op"].(string) == GET_MSG || firstPending["op"].(string) == PUT_MSG) {
					panic("(((firstPending).op) = (GET_MSG)) \\/ (((firstPending).op) = (PUT_MSG))")
				}
				timestamp = firstPending["timestamp"].(int)
				if timestamp < minClock {
					chooseMessage = timestamp < lowestPending || timestamp == lowestPending && client < nextClient
					if chooseMessage {
						nextClient = client
						lowestPending = timestamp
					}
				}
				tmpSet0 := make([]int, 0, len(pendingClients))
				for _, v := range pendingClients {
					if v != client {
						tmpSet0 = append(tmpSet0, v)
					}
				}
				pendingClients = tmpSet0
				acquiredResources = map[string]map[interface{}]bool{}
			}

			// addStableMessage:
			acquiredResources = map[string]map[interface{}]bool{}
			if lowestPending < minClock {
				key0 := nextClient
				index := sort.Search(len(pendingRequests), func(i0 int) bool {
					return !(pendingRequests[i0].key < key0)
				})
				msg = pendingRequests[index].value[0]
				key1 := nextClient
				index0 := sort.Search(len(pendingRequests), func(i1 int) bool {
					return !(pendingRequests[i1].key < key1)
				})
				key2 := nextClient
				index1 := sort.Search(len(pendingRequests), func(i2 int) bool {
					return !(pendingRequests[i2].key < key2)
				})
				pendingRequests[index0].value = pendingRequests[index1].value[1:]
				tmpSlice := make([]map[string]interface{}, len(stableMessages), len(stableMessages)+1)
				copy(tmpSlice, stableMessages)
				tmpSlice = append(tmpSlice, msg)
				stableMessages = tmpSlice
			} else {
				continue0 = false
			}
			acquiredResources = map[string]map[interface{}]bool{}
		}
		i = 1

		// respondPendingRequestsLoop:
		acquiredResources = map[string]map[interface{}]bool{}
		for {
			if !(i <= len(stableMessages)) {
				break
			}
			msg = stableMessages[i-1]
			i = i + 1

			// respondStableGet:
			acquiredResources = map[string]map[interface{}]bool{}
			if msg["op"].(string) == GET_MSG {
				key = msg["key"]
				if _, ok0 := acquiredResources["kv"]; !ok0 {
					acquiredResources["kv"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["kv"][key]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, kv.Get(key))
					if err != nil {
						return err
					}
					acquiredResources["kv"][key] = true
				}
				val = kv.Get(key).Read()
				if _, ok0 := acquiredResources["clients"]; !ok0 {
					acquiredResources["clients"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clients"][msg["client"].(int)]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, clients.Get(msg["client"].(int)))
					if err != nil {
						return err
					}
					acquiredResources["clients"][msg["client"].(int)] = true
				}
				var resourceWrite interface{}
				resourceWrite = map[string]interface{}{
					"result": val,
					"type":   GET_RESPONSE,
				}
				clients.Get(msg["client"].(int)).Write(resourceWrite)
			}
			for r, _ := range acquiredResources["clients"] {
				err = distsys.ReleaseResources(clients.Get(r))
				if err != nil {
					return err
				}
			}
			for r, _ := range acquiredResources["kv"] {
				err = distsys.ReleaseResources(kv.Get(r))
				if err != nil {
					return err
				}
			}

			// respondStablePut:
			acquiredResources = map[string]map[interface{}]bool{}
			if msg["op"].(string) == PUT_MSG {
				key = msg["key"]
				val = msg["value"]
				if _, ok0 := acquiredResources["kv"]; !ok0 {
					acquiredResources["kv"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["kv"][key]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, kv.Get(key))
					if err != nil {
						return err
					}
					acquiredResources["kv"][key] = true
				}
				var resourceWrite interface{}
				resourceWrite = val
				kv.Get(key).Write(resourceWrite)
				if _, ok0 := acquiredResources["clients"]; !ok0 {
					acquiredResources["clients"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clients"][msg["client"].(int)]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, clients.Get(msg["client"].(int)))
					if err != nil {
						return err
					}
					acquiredResources["clients"][msg["client"].(int)] = true
				}
				var resourceWrite0 interface{}
				resourceWrite0 = map[string]interface{}{
					"result": ok,
					"type":   PUT_RESPONSE,
				}
				clients.Get(msg["client"].(int)).Write(resourceWrite0)
			}
			for r, _ := range acquiredResources["clients"] {
				err = distsys.ReleaseResources(clients.Get(r))
				if err != nil {
					return err
				}
			}
			for r, _ := range acquiredResources["kv"] {
				err = distsys.ReleaseResources(kv.Get(r))
				if err != nil {
					return err
				}
			}
			acquiredResources = map[string]map[interface{}]bool{}
		}
		acquiredResources = map[string]map[interface{}]bool{}
	}
	return nil
}

func ReplicaSet() []int {
	tmpRange := make([]int, NUM_REPLICAS-1-0+1)
	for i := 0; i <= NUM_REPLICAS-1; i++ {
		tmpRange[i-0] = i
	}
	return tmpRange
}

func Get(self int, clientId distsys.ArchetypeResource, replicas distsys.ArchetypeResourceCollection, clients distsys.ArchetypeResourceCollection, key distsys.ArchetypeResource, locked distsys.ArchetypeResourceCollection, clock distsys.ArchetypeResourceCollection, spin distsys.ArchetypeResource, outside distsys.ArchetypeResource) error {
	continue0 := true
	var getReq map[string]interface{}
	var getResp map[string]interface{}
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// getLoop:
	acquiredResources = map[string]map[interface{}]bool{}
	for {
		if !continue0 {
			break
		}

		// getRequest:
	getRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		err = distsys.AcquireResources(distsys.READ_ACCESS, clientId, key)
		if err != nil {
			return err
		}
		if _, ok := acquiredResources["locked"]; !ok {
			acquiredResources["locked"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["locked"][clientId.Read()]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, locked.Get(clientId.Read()))
			if err != nil {
				return err
			}
			acquiredResources["locked"][clientId.Read()] = true
		}
		if !!locked.Get(clientId.Read()).Read().(bool) {
			err = distsys.AbortResources(key, clientId)
			if err != nil {
				return err
			}
			for r, _ := range acquiredResources["locked"] {
				err = distsys.ReleaseResources(locked.Get(r))
				if err != nil {
					return err
				}
			}
			goto getRequest
		}
		if _, ok := acquiredResources["clock"]; !ok {
			acquiredResources["clock"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
			if err != nil {
				return err
			}
			acquiredResources["clock"][clientId.Read()] = true
		}
		if clock.Get(clientId.Read()).Read().(int) == -1 {
			continue0 = false
			err = distsys.ReleaseResources(key, clientId)
			if err != nil {
				return err
			}
			for r, _ := range acquiredResources["clock"] {
				err = distsys.ReleaseResources(clock.Get(r))
				if err != nil {
					return err
				}
			}
			for r, _ := range acquiredResources["locked"] {
				err = distsys.ReleaseResources(locked.Get(r))
				if err != nil {
					return err
				}
			}
		} else {
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["clock"][clientId.Read()] = true
			}
			var resourceWrite interface{}
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["clock"][clientId.Read()] = true
			}
			resourceWrite = clock.Get(clientId.Read()).Read().(int) + 1
			clock.Get(clientId.Read()).Write(resourceWrite)
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["clock"][clientId.Read()] = true
			}
			getReq = map[string]interface{}{
				"op":        GET_MSG,
				"client":    clientId.Read(),
				"timestamp": clock.Get(clientId.Read()).Read().(int),
				"key":       key.Read(),
			}
			dst := ReplicaSet()[0]
			if _, ok := acquiredResources["replicas"]; !ok {
				acquiredResources["replicas"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["replicas"][dst]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, replicas.Get(dst))
				if err != nil {
					return err
				}
				acquiredResources["replicas"][dst] = true
			}
			var resourceWrite0 interface{}
			resourceWrite0 = getReq
			replicas.Get(dst).Write(resourceWrite0)

			// getReply:
			err = distsys.ReleaseResources(key, clientId)
			if err != nil {
				return err
			}
			for r, _ := range acquiredResources["replicas"] {
				err = distsys.ReleaseResources(replicas.Get(r))
				if err != nil {
					return err
				}
			}
			for r, _ := range acquiredResources["clock"] {
				err = distsys.ReleaseResources(clock.Get(r))
				if err != nil {
					return err
				}
			}
			for r, _ := range acquiredResources["locked"] {
				err = distsys.ReleaseResources(locked.Get(r))
				if err != nil {
					return err
				}
			}
			acquiredResources = map[string]map[interface{}]bool{}
			err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
			if err != nil {
				return err
			}
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, outside)
			if err != nil {
				return err
			}
			if _, ok := acquiredResources["clients"]; !ok {
				acquiredResources["clients"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clients"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clients.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["clients"][clientId.Read()] = true
			}
			getResp = clients.Get(clientId.Read()).Read().(map[string]interface{})
			if !(getResp["type"].(string) == GET_RESPONSE) {
				panic("((getResp).type) = (GET_RESPONSE)")
			}
			var resourceWrite1 interface{}
			resourceWrite1 = getResp["result"]
			outside.Write(resourceWrite1)
			err = distsys.ReleaseResources(clientId, outside)
			if err != nil {
				return err
			}
			for r, _ := range acquiredResources["clients"] {
				err = distsys.ReleaseResources(clients.Get(r))
				if err != nil {
					return err
				}
			}
		}

		// getCheckSpin:
		acquiredResources = map[string]map[interface{}]bool{}
		err = distsys.AcquireResources(distsys.READ_ACCESS, spin)
		if err != nil {
			return err
		}
		if !spin.Read().(bool) {
			continue0 = false
		}
		err = distsys.ReleaseResources(spin)
		if err != nil {
			return err
		}
		acquiredResources = map[string]map[interface{}]bool{}
	}
	return nil
}

func Put(self int, clientId distsys.ArchetypeResource, replicas distsys.ArchetypeResourceCollection, clients distsys.ArchetypeResourceCollection, key distsys.ArchetypeResource, value distsys.ArchetypeResource, locked distsys.ArchetypeResourceCollection, clock distsys.ArchetypeResourceCollection, spin distsys.ArchetypeResource, outside distsys.ArchetypeResource) error {
	continue0 := true
	var i int
	var j int
	var putReq map[string]interface{}
	var putResp map[string]interface{}
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// putLoop:
	acquiredResources = map[string]map[interface{}]bool{}
	for {
		if !continue0 {
			break
		}

		// putRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		err = distsys.AcquireResources(distsys.READ_ACCESS, clientId, value, key)
		if err != nil {
			return err
		}
		if _, ok := acquiredResources["clock"]; !ok {
			acquiredResources["clock"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
			if err != nil {
				return err
			}
			acquiredResources["clock"][clientId.Read()] = true
		}
		if clock.Get(clientId.Read()).Read().(int) == -1 {
			continue0 = false
			err = distsys.ReleaseResources(key, value, clientId)
			if err != nil {
				return err
			}
			for r, _ := range acquiredResources["clock"] {
				err = distsys.ReleaseResources(clock.Get(r))
				if err != nil {
					return err
				}
			}
		} else {
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["clock"][clientId.Read()] = true
			}
			var resourceWrite interface{}
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["clock"][clientId.Read()] = true
			}
			resourceWrite = clock.Get(clientId.Read()).Read().(int) + 1
			clock.Get(clientId.Read()).Write(resourceWrite)
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["clock"][clientId.Read()] = true
			}
			putReq = map[string]interface{}{
				"op":        PUT_MSG,
				"client":    clientId.Read(),
				"value":     value.Read(),
				"timestamp": clock.Get(clientId.Read()).Read().(int),
				"key":       key.Read(),
			}
			if _, ok := acquiredResources["locked"]; !ok {
				acquiredResources["locked"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["locked"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, locked.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["locked"][clientId.Read()] = true
			}
			var resourceWrite0 interface{}
			resourceWrite0 = true
			locked.Get(clientId.Read()).Write(resourceWrite0)
			i = 0
			j = 0

			// putBroadcast:
			err = distsys.ReleaseResources(key, value, clientId)
			if err != nil {
				return err
			}
			for r, _ := range acquiredResources["clock"] {
				err = distsys.ReleaseResources(clock.Get(r))
				if err != nil {
					return err
				}
			}
			for r, _ := range acquiredResources["locked"] {
				err = distsys.ReleaseResources(locked.Get(r))
				if err != nil {
					return err
				}
			}
			acquiredResources = map[string]map[interface{}]bool{}
			for {
				if !(j <= NUM_REPLICAS-1) {
					break
				}
				if _, ok := acquiredResources["replicas"]; !ok {
					acquiredResources["replicas"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["replicas"][j]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, replicas.Get(j))
					if err != nil {
						return err
					}
					acquiredResources["replicas"][j] = true
				}
				var resourceWrite1 interface{}
				resourceWrite1 = putReq
				replicas.Get(j).Write(resourceWrite1)
				j = j + 1
				for r, _ := range acquiredResources["replicas"] {
					err = distsys.ReleaseResources(replicas.Get(r))
					if err != nil {
						return err
					}
				}
				acquiredResources = map[string]map[interface{}]bool{}
			}

			// putResponse:
			acquiredResources = map[string]map[interface{}]bool{}
			err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
			if err != nil {
				return err
			}
			for {
				if !(i < len(ReplicaSet())) {
					break
				}
				if _, ok := acquiredResources["clients"]; !ok {
					acquiredResources["clients"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clients"][clientId.Read()]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, clients.Get(clientId.Read()))
					if err != nil {
						return err
					}
					acquiredResources["clients"][clientId.Read()] = true
				}
				putResp = clients.Get(clientId.Read()).Read().(map[string]interface{})
				if !(putResp["type"].(string) == PUT_RESPONSE) {
					panic("((putResp).type) = (PUT_RESPONSE)")
				}
				i = i + 1
				err = distsys.ReleaseResources(clientId)
				if err != nil {
					return err
				}
				for r, _ := range acquiredResources["clients"] {
					err = distsys.ReleaseResources(clients.Get(r))
					if err != nil {
						return err
					}
				}
				acquiredResources = map[string]map[interface{}]bool{}
				err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
				if err != nil {
					return err
				}
			}
			if _, ok := acquiredResources["locked"]; !ok {
				acquiredResources["locked"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["locked"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, locked.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["locked"][clientId.Read()] = true
			}
			var resourceWrite1 interface{}
			resourceWrite1 = false
			locked.Get(clientId.Read()).Write(resourceWrite1)
			err = distsys.ReleaseResources(clientId)
			if err != nil {
				return err
			}
			for r, _ := range acquiredResources["locked"] {
				err = distsys.ReleaseResources(locked.Get(r))
				if err != nil {
					return err
				}
			}

			// putComplete:
			acquiredResources = map[string]map[interface{}]bool{}
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, outside)
			if err != nil {
				return err
			}
			var resourceWrite2 interface{}
			resourceWrite2 = PUT_RESPONSE
			outside.Write(resourceWrite2)
			err = distsys.ReleaseResources(outside)
			if err != nil {
				return err
			}
		}

		// putCheckSpin:
		acquiredResources = map[string]map[interface{}]bool{}
		err = distsys.AcquireResources(distsys.READ_ACCESS, spin)
		if err != nil {
			return err
		}
		if !spin.Read().(bool) {
			continue0 = false
		}
		err = distsys.ReleaseResources(spin)
		if err != nil {
			return err
		}
		acquiredResources = map[string]map[interface{}]bool{}
	}
	return nil
}

func Disconnect(self int, clientId distsys.ArchetypeResource, replicas distsys.ArchetypeResourceCollection, locked distsys.ArchetypeResourceCollection, clock distsys.ArchetypeResourceCollection) error {
	var msg map[string]interface{}
	var j int
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// sendDisconnectRequest:
sendDisconnectRequest:
	acquiredResources = map[string]map[interface{}]bool{}
	err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
	if err != nil {
		return err
	}
	if _, ok := acquiredResources["locked"]; !ok {
		acquiredResources["locked"] = map[interface{}]bool{}
	}
	if _, acquired := acquiredResources["locked"][clientId.Read()]; !acquired {
		err = distsys.AcquireResources(distsys.READ_ACCESS, locked.Get(clientId.Read()))
		if err != nil {
			return err
		}
		acquiredResources["locked"][clientId.Read()] = true
	}
	if !!locked.Get(clientId.Read()).Read().(bool) {
		err = distsys.AbortResources(clientId)
		if err != nil {
			return err
		}
		for r, _ := range acquiredResources["locked"] {
			err = distsys.ReleaseResources(locked.Get(r))
			if err != nil {
				return err
			}
		}
		goto sendDisconnectRequest
	}
	msg = map[string]interface{}{
		"op":     DISCONNECT_MSG,
		"client": clientId.Read(),
	}
	if _, ok := acquiredResources["clock"]; !ok {
		acquiredResources["clock"] = map[interface{}]bool{}
	}
	if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, clock.Get(clientId.Read()))
		if err != nil {
			return err
		}
		acquiredResources["clock"][clientId.Read()] = true
	}
	var resourceWrite interface{}
	resourceWrite = -1
	clock.Get(clientId.Read()).Write(resourceWrite)
	j = 0
	err = distsys.ReleaseResources(clientId)
	if err != nil {
		return err
	}
	for r, _ := range acquiredResources["clock"] {
		err = distsys.ReleaseResources(clock.Get(r))
		if err != nil {
			return err
		}
	}
	for r, _ := range acquiredResources["locked"] {
		err = distsys.ReleaseResources(locked.Get(r))
		if err != nil {
			return err
		}
	}

	// disconnectBroadcast:
	acquiredResources = map[string]map[interface{}]bool{}
	for {
		if !(j <= NUM_REPLICAS-1) {
			break
		}
		if _, ok := acquiredResources["replicas"]; !ok {
			acquiredResources["replicas"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["replicas"][j]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, replicas.Get(j))
			if err != nil {
				return err
			}
			acquiredResources["replicas"][j] = true
		}
		var resourceWrite0 interface{}
		resourceWrite0 = msg
		replicas.Get(j).Write(resourceWrite0)
		j = j + 1
		for r, _ := range acquiredResources["replicas"] {
			err = distsys.ReleaseResources(replicas.Get(r))
			if err != nil {
				return err
			}
		}
		acquiredResources = map[string]map[interface{}]bool{}
	}
	return nil
}

func ClockUpdate(self int, clientId distsys.ArchetypeResource, replicas distsys.ArchetypeResourceCollection, clock distsys.ArchetypeResourceCollection, spin distsys.ArchetypeResource) error {
	continue0 := true
	var j int
	var msg map[string]interface{}
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// clockUpdateLoop:
	acquiredResources = map[string]map[interface{}]bool{}
	err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
	if err != nil {
		return err
	}
	for {
		if !continue0 {
			err = distsys.ReleaseResources(clientId)
			if err != nil {
				return err
			}
			break
		}
		if _, ok := acquiredResources["clock"]; !ok {
			acquiredResources["clock"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
			if err != nil {
				return err
			}
			acquiredResources["clock"][clientId.Read()] = true
		}
		if clock.Get(clientId.Read()).Read().(int) == -1 {
			continue0 = false
			err = distsys.ReleaseResources(clientId)
			if err != nil {
				return err
			}
			for r, _ := range acquiredResources["clock"] {
				err = distsys.ReleaseResources(clock.Get(r))
				if err != nil {
					return err
				}
			}
		} else {
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["clock"][clientId.Read()] = true
			}
			var resourceWrite interface{}
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["clock"][clientId.Read()] = true
			}
			resourceWrite = clock.Get(clientId.Read()).Read().(int) + 1
			clock.Get(clientId.Read()).Write(resourceWrite)
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][clientId.Read()]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(clientId.Read()))
				if err != nil {
					return err
				}
				acquiredResources["clock"][clientId.Read()] = true
			}
			msg = map[string]interface{}{
				"op":        NULL_MSG,
				"client":    clientId.Read(),
				"timestamp": clock.Get(clientId.Read()).Read().(int),
			}
			j = 0

			// nullBroadcast:
			err = distsys.ReleaseResources(clientId)
			if err != nil {
				return err
			}
			for r, _ := range acquiredResources["clock"] {
				err = distsys.ReleaseResources(clock.Get(r))
				if err != nil {
					return err
				}
			}
			acquiredResources = map[string]map[interface{}]bool{}
			for {
				if !(j <= NUM_REPLICAS-1) {
					break
				}
				if _, ok := acquiredResources["replicas"]; !ok {
					acquiredResources["replicas"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["replicas"][j]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, replicas.Get(j))
					if err != nil {
						return err
					}
					acquiredResources["replicas"][j] = true
				}
				var resourceWrite0 interface{}
				resourceWrite0 = msg
				replicas.Get(j).Write(resourceWrite0)
				j = j + 1
				for r, _ := range acquiredResources["replicas"] {
					err = distsys.ReleaseResources(replicas.Get(r))
					if err != nil {
						return err
					}
				}
				acquiredResources = map[string]map[interface{}]bool{}
			}
		}

		// nullCheckSpin:
		acquiredResources = map[string]map[interface{}]bool{}
		err = distsys.AcquireResources(distsys.READ_ACCESS, spin)
		if err != nil {
			return err
		}
		if !spin.Read().(bool) {
			continue0 = false
		}
		err = distsys.ReleaseResources(spin)
		if err != nil {
			return err
		}
		acquiredResources = map[string]map[interface{}]bool{}
		err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
		if err != nil {
			return err
		}
	}
	return nil
}
