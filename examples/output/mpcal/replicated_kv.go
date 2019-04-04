package replicated_kv

import (
	"fmt"
	"math/rand"
	"pgo/distsys"
	"sort"
	"time"
)

var sleepMin = 100

var sleepMax = 300

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
	NUM_CLIENTS = 3
	NUM_REPLICAS = 2
	PUT_MSG = "put"
	PUT_RESPONSE = "put_response"
	distsys.DefineCustomType(map[string]interface{}{})
	rand.Seed(time.Now().UnixNano())
}

func shouldRetry(err error) bool {
	t := rand.Intn(sleepMax-sleepMin) + sleepMin
	switch err.(type) {
	case *distsys.AbortRetryError:
		return true
	case *distsys.ResourceInternalError:
		time.Sleep(time.Duration(t) * time.Millisecond)
		return false
	default:
		panic(fmt.Sprintf("Invalid error returned by Archetype Resource: %v", err))
	}
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
	var liveClientsCopy []int
	var pendingRequestsCopy []struct {
		key   int
		value []map[string]interface{}
	}
	var stableMessagesCopy []map[string]interface{}
	var iCopy int
	var firstPendingCopy map[string]interface{}
	var timestampCopy int
	var nextClientCopy int
	var lowestPendingCopy int
	var chooseMessageCopy bool
	var currentClocksCopy []struct {
		key   int
		value int
	}
	var minClockCopy int
	var continueCopy bool
	var pendingClientsCopy []int
	var clientsIterCopy []int
	var msgCopy map[string]interface{}
	var okCopy interface{}
	var keyCopy interface{}
	var valCopy interface{}
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// replicaLoop:
	acquiredResources = map[string]map[interface{}]bool{}
	continue0Copy := continue0
	continueCopy = continue0Copy
	stableMessagesCopy0 := make([]map[string]interface{}, len(stableMessages))
	for i0, e := range stableMessages {
		eCopy := make(map[string]interface{}, len(e))
		for k, v := range e {
			vCopy := v
			eCopy[k] = vCopy
		}
		stableMessagesCopy0[i0] = eCopy
	}
	stableMessagesCopy = stableMessagesCopy0
	for {
		if !true {
			continue0 = continueCopy
			stableMessages = stableMessagesCopy
			break
		}
		stableMessagesCopy = []map[string]interface{}{}
		continueCopy = true

		// receiveClientRequest:
		continue0 = continueCopy
		stableMessages = stableMessagesCopy
	receiveClientRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		msgCopy0 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy0[k] = vCopy
		}
		msgCopy = msgCopy0
		if _, ok0 := acquiredResources["replicas"]; !ok0 {
			acquiredResources["replicas"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["replicas"][self]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, replicas.Get(self))
			if err != nil {
				for r, _ := range acquiredResources["replicas"] {
					distsys.AbortResources(replicas.Get(r))
				}
				if shouldRetry(err) {
					goto receiveClientRequest
				} else {
					return err
				}
			}
			acquiredResources["replicas"][self] = true
		}
		var readTemp interface{}
		readTemp, err = replicas.Get(self).Read()
		if err != nil {
			for r, _ := range acquiredResources["replicas"] {
				distsys.AbortResources(replicas.Get(r))
			}
			if shouldRetry(err) {
				goto receiveClientRequest
			} else {
				return err
			}
		}
		msgCopy = readTemp.(map[string]interface{})
		for r, _ := range acquiredResources["replicas"] {
			err = distsys.ReleaseResources(replicas.Get(r))
			if err != nil {
				for r0, _ := range acquiredResources["replicas"] {
					distsys.AbortResources(replicas.Get(r0))
				}
				return err
			}
		}
		msg = msgCopy

		// clientDisconnected:
		acquiredResources = map[string]map[interface{}]bool{}
		msgCopy1 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy1[k] = vCopy
		}
		msgCopy = msgCopy1
		liveClientsCopy0 := make([]int, len(liveClients))
		for i0, e := range liveClients {
			eCopy := e
			liveClientsCopy0[i0] = eCopy
		}
		liveClientsCopy = liveClientsCopy0
		if msgCopy["op"].(string) == DISCONNECT_MSG {
			tmpSet := make([]int, 0, len(liveClientsCopy))
			for _, v := range liveClientsCopy {
				if v != msgCopy["client"].(int) {
					tmpSet = append(tmpSet, v)
				}
			}
			liveClientsCopy = tmpSet
		}
		msg = msgCopy
		liveClients = liveClientsCopy

		// replicaGetRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		pendingRequestsCopy0 := make([]struct {
			key   int
			value []map[string]interface{}
		}, len(pendingRequests))
		for i0, e := range pendingRequests {
			field := e.key
			fieldCopy := field
			field0 := e.value
			field0Copy := make([]map[string]interface{}, len(field0))
			for i1, e0 := range field0 {
				e0Copy := make(map[string]interface{}, len(e0))
				for k, v := range e0 {
					vCopy := v
					e0Copy[k] = vCopy
				}
				field0Copy[i1] = e0Copy
			}
			eCopy := struct {
				key   int
				value []map[string]interface{}
			}{key: fieldCopy, value: field0Copy}
			pendingRequestsCopy0[i0] = eCopy
		}
		pendingRequestsCopy = pendingRequestsCopy0
		currentClocksCopy0 := make([]struct {
			key   int
			value int
		}, len(currentClocks))
		for i0, e := range currentClocks {
			field := e.key
			fieldCopy := field
			field0 := e.value
			field0Copy := field0
			eCopy := struct {
				key   int
				value int
			}{key: fieldCopy, value: field0Copy}
			currentClocksCopy0[i0] = eCopy
		}
		currentClocksCopy = currentClocksCopy0
		msgCopy2 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy2[k] = vCopy
		}
		msgCopy = msgCopy2
		liveClientsCopy1 := make([]int, len(liveClients))
		for i0, e := range liveClients {
			eCopy := e
			liveClientsCopy1[i0] = eCopy
		}
		liveClientsCopy = liveClientsCopy1
		if msgCopy["op"].(string) == GET_MSG {
			index := sort.SearchInts(liveClientsCopy, msgCopy["client"].(int))
			if !(index < len(liveClientsCopy) && liveClientsCopy[index] == msgCopy["client"].(int)) {
				panic("((msg).client) \\in (liveClients)")
			}
			key0 := msgCopy["client"].(int)
			index0 := sort.Search(len(currentClocksCopy), func(i0 int) bool {
				return !(currentClocksCopy[i0].key < key0)
			})
			currentClocksCopy[index0].value = msgCopy["timestamp"].(int)
			key1 := msgCopy["client"].(int)
			index1 := sort.Search(len(pendingRequestsCopy), func(i1 int) bool {
				return !(pendingRequestsCopy[i1].key < key1)
			})
			key2 := msgCopy["client"].(int)
			index2 := sort.Search(len(pendingRequestsCopy), func(i2 int) bool {
				return !(pendingRequestsCopy[i2].key < key2)
			})
			tmpSlice := make([]map[string]interface{}, len(pendingRequestsCopy[index2].value), len(pendingRequestsCopy[index2].value)+1)
			copy(tmpSlice, pendingRequestsCopy[index2].value)
			tmpSlice = append(tmpSlice, msgCopy)
			pendingRequestsCopy[index1].value = tmpSlice
		}
		pendingRequests = pendingRequestsCopy
		currentClocks = currentClocksCopy
		msg = msgCopy
		liveClients = liveClientsCopy

		// replicaPutRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		pendingRequestsCopy1 := make([]struct {
			key   int
			value []map[string]interface{}
		}, len(pendingRequests))
		for i0, e := range pendingRequests {
			field := e.key
			fieldCopy := field
			field0 := e.value
			field0Copy := make([]map[string]interface{}, len(field0))
			for i1, e0 := range field0 {
				e0Copy := make(map[string]interface{}, len(e0))
				for k, v := range e0 {
					vCopy := v
					e0Copy[k] = vCopy
				}
				field0Copy[i1] = e0Copy
			}
			eCopy := struct {
				key   int
				value []map[string]interface{}
			}{key: fieldCopy, value: field0Copy}
			pendingRequestsCopy1[i0] = eCopy
		}
		pendingRequestsCopy = pendingRequestsCopy1
		currentClocksCopy1 := make([]struct {
			key   int
			value int
		}, len(currentClocks))
		for i0, e := range currentClocks {
			field := e.key
			fieldCopy := field
			field0 := e.value
			field0Copy := field0
			eCopy := struct {
				key   int
				value int
			}{key: fieldCopy, value: field0Copy}
			currentClocksCopy1[i0] = eCopy
		}
		currentClocksCopy = currentClocksCopy1
		msgCopy3 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy3[k] = vCopy
		}
		msgCopy = msgCopy3
		if msgCopy["op"].(string) == PUT_MSG {
			key0 := msgCopy["client"].(int)
			index := sort.Search(len(currentClocksCopy), func(i0 int) bool {
				return !(currentClocksCopy[i0].key < key0)
			})
			currentClocksCopy[index].value = msgCopy["timestamp"].(int)
			key1 := msgCopy["client"].(int)
			index0 := sort.Search(len(pendingRequestsCopy), func(i1 int) bool {
				return !(pendingRequestsCopy[i1].key < key1)
			})
			key2 := msgCopy["client"].(int)
			index1 := sort.Search(len(pendingRequestsCopy), func(i2 int) bool {
				return !(pendingRequestsCopy[i2].key < key2)
			})
			tmpSlice := make([]map[string]interface{}, len(pendingRequestsCopy[index1].value), len(pendingRequestsCopy[index1].value)+1)
			copy(tmpSlice, pendingRequestsCopy[index1].value)
			tmpSlice = append(tmpSlice, msgCopy)
			pendingRequestsCopy[index0].value = tmpSlice
		}
		pendingRequests = pendingRequestsCopy
		currentClocks = currentClocksCopy
		msg = msgCopy

		// replicaNullRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		currentClocksCopy2 := make([]struct {
			key   int
			value int
		}, len(currentClocks))
		for i0, e := range currentClocks {
			field := e.key
			fieldCopy := field
			field0 := e.value
			field0Copy := field0
			eCopy := struct {
				key   int
				value int
			}{key: fieldCopy, value: field0Copy}
			currentClocksCopy2[i0] = eCopy
		}
		currentClocksCopy = currentClocksCopy2
		msgCopy4 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy4[k] = vCopy
		}
		msgCopy = msgCopy4
		if msgCopy["op"].(string) == NULL_MSG {
			key0 := msgCopy["client"].(int)
			index := sort.Search(len(currentClocksCopy), func(i0 int) bool {
				return !(currentClocksCopy[i0].key < key0)
			})
			currentClocksCopy[index].value = msgCopy["timestamp"].(int)
		}
		currentClocks = currentClocksCopy
		msg = msgCopy

		// findStableRequestsLoop:
		acquiredResources = map[string]map[interface{}]bool{}
		clientsIterCopy0 := make([]int, len(clientsIter))
		for i0, e := range clientsIter {
			eCopy := e
			clientsIterCopy0[i0] = eCopy
		}
		clientsIterCopy = clientsIterCopy0
		iCopy0 := i
		iCopy = iCopy0
		pendingRequestsCopy2 := make([]struct {
			key   int
			value []map[string]interface{}
		}, len(pendingRequests))
		for i0, e := range pendingRequests {
			field := e.key
			fieldCopy := field
			field0 := e.value
			field0Copy := make([]map[string]interface{}, len(field0))
			for i1, e0 := range field0 {
				e0Copy := make(map[string]interface{}, len(e0))
				for k, v := range e0 {
					vCopy := v
					e0Copy[k] = vCopy
				}
				field0Copy[i1] = e0Copy
			}
			eCopy := struct {
				key   int
				value []map[string]interface{}
			}{key: fieldCopy, value: field0Copy}
			pendingRequestsCopy2[i0] = eCopy
		}
		pendingRequestsCopy = pendingRequestsCopy2
		pendingClientsCopy0 := make([]int, len(pendingClients))
		for i0, e := range pendingClients {
			eCopy := e
			pendingClientsCopy0[i0] = eCopy
		}
		pendingClientsCopy = pendingClientsCopy0
		nextClientCopy0 := nextClient
		nextClientCopy = nextClientCopy0
		continue0Copy0 := continue0
		continueCopy = continue0Copy0
		liveClientsCopy2 := make([]int, len(liveClients))
		for i0, e := range liveClients {
			eCopy := e
			liveClientsCopy2[i0] = eCopy
		}
		liveClientsCopy = liveClientsCopy2
		minClockCopy0 := minClock
		minClockCopy = minClockCopy0
		for {
			if !continueCopy {
				clientsIter = clientsIterCopy
				i = iCopy
				pendingRequests = pendingRequestsCopy
				pendingClients = pendingClientsCopy
				nextClient = nextClientCopy
				continue0 = continueCopy
				liveClients = liveClientsCopy
				minClock = minClockCopy
				break
			}
			tmpSet := make([]int, 0)
			for _, c := range liveClientsCopy {
				key0 := c
				index := sort.Search(len(pendingRequestsCopy), func(i0 int) bool {
					return !(pendingRequestsCopy[i0].key < key0)
				})
				if len(pendingRequestsCopy[index].value) > 0 {
					tmpSet = append(tmpSet, c)
				}
			}
			pendingClientsCopy = tmpSet
			nextClientCopy = NUM_NODES() + 1
			clientsIterCopy = liveClientsCopy
			iCopy = 0
			minClockCopy = 0

			// findMinClock:
			clientsIter = clientsIterCopy
			i = iCopy
			pendingRequests = pendingRequestsCopy
			pendingClients = pendingClientsCopy
			nextClient = nextClientCopy
			continue0 = continueCopy
			liveClients = liveClientsCopy
			minClock = minClockCopy
			acquiredResources = map[string]map[interface{}]bool{}
			iCopy1 := i
			iCopy = iCopy1
			clientsIterCopy1 := make([]int, len(clientsIter))
			for i0, e := range clientsIter {
				eCopy := e
				clientsIterCopy1[i0] = eCopy
			}
			clientsIterCopy = clientsIterCopy1
			lowestPendingCopy0 := lowestPending
			lowestPendingCopy = lowestPendingCopy0
			currentClocksCopy3 := make([]struct {
				key   int
				value int
			}, len(currentClocks))
			for i0, e := range currentClocks {
				field := e.key
				fieldCopy := field
				field0 := e.value
				field0Copy := field0
				eCopy := struct {
					key   int
					value int
				}{key: fieldCopy, value: field0Copy}
				currentClocksCopy3[i0] = eCopy
			}
			currentClocksCopy = currentClocksCopy3
			minClockCopy1 := minClock
			minClockCopy = minClockCopy1
			for {
				if !(iCopy < len(clientsIterCopy)) {
					break
				}
				client := clientsIterCopy[0]
				key0 := client
				index := sort.Search(len(currentClocksCopy), func(i0 int) bool {
					return !(currentClocksCopy[i0].key < key0)
				})
				if minClockCopy == 0 || currentClocksCopy[index].value < minClockCopy {
					key1 := client
					index0 := sort.Search(len(currentClocksCopy), func(i1 int) bool {
						return !(currentClocksCopy[i1].key < key1)
					})
					minClockCopy = currentClocksCopy[index0].value
				}
				tmpSet0 := make([]int, 0, len(clientsIterCopy))
				for _, v := range clientsIterCopy {
					if v != client {
						tmpSet0 = append(tmpSet0, v)
					}
				}
				clientsIterCopy = tmpSet0
				i = iCopy
				clientsIter = clientsIterCopy
				lowestPending = lowestPendingCopy
				currentClocks = currentClocksCopy
				minClock = minClockCopy
				acquiredResources = map[string]map[interface{}]bool{}
				iCopy2 := i
				iCopy = iCopy2
				clientsIterCopy2 := make([]int, len(clientsIter))
				for i1, e := range clientsIter {
					eCopy := e
					clientsIterCopy2[i1] = eCopy
				}
				clientsIterCopy = clientsIterCopy2
				lowestPendingCopy1 := lowestPending
				lowestPendingCopy = lowestPendingCopy1
				currentClocksCopy4 := make([]struct {
					key   int
					value int
				}, len(currentClocks))
				for i1, e := range currentClocks {
					field := e.key
					fieldCopy := field
					field0 := e.value
					field0Copy := field0
					eCopy := struct {
						key   int
						value int
					}{key: fieldCopy, value: field0Copy}
					currentClocksCopy4[i1] = eCopy
				}
				currentClocksCopy = currentClocksCopy4
				minClockCopy2 := minClock
				minClockCopy = minClockCopy2
			}
			lowestPendingCopy = minClockCopy + 1
			iCopy = 0
			i = iCopy
			clientsIter = clientsIterCopy
			lowestPending = lowestPendingCopy
			currentClocks = currentClocksCopy
			minClock = minClockCopy

			// findMinClient:
			acquiredResources = map[string]map[interface{}]bool{}
			iCopy2 := i
			iCopy = iCopy2
			pendingRequestsCopy3 := make([]struct {
				key   int
				value []map[string]interface{}
			}, len(pendingRequests))
			for i0, e := range pendingRequests {
				field := e.key
				fieldCopy := field
				field0 := e.value
				field0Copy := make([]map[string]interface{}, len(field0))
				for i1, e0 := range field0 {
					e0Copy := make(map[string]interface{}, len(e0))
					for k, v := range e0 {
						vCopy := v
						e0Copy[k] = vCopy
					}
					field0Copy[i1] = e0Copy
				}
				eCopy := struct {
					key   int
					value []map[string]interface{}
				}{key: fieldCopy, value: field0Copy}
				pendingRequestsCopy3[i0] = eCopy
			}
			pendingRequestsCopy = pendingRequestsCopy3
			lowestPendingCopy1 := lowestPending
			lowestPendingCopy = lowestPendingCopy1
			pendingClientsCopy1 := make([]int, len(pendingClients))
			for i0, e := range pendingClients {
				eCopy := e
				pendingClientsCopy1[i0] = eCopy
			}
			pendingClientsCopy = pendingClientsCopy1
			nextClientCopy1 := nextClient
			nextClientCopy = nextClientCopy1
			firstPendingCopy0 := make(map[string]interface{}, len(firstPending))
			for k, v := range firstPending {
				vCopy := v
				firstPendingCopy0[k] = vCopy
			}
			firstPendingCopy = firstPendingCopy0
			chooseMessageCopy0 := chooseMessage
			chooseMessageCopy = chooseMessageCopy0
			timestampCopy0 := timestamp
			timestampCopy = timestampCopy0
			minClockCopy2 := minClock
			minClockCopy = minClockCopy2
			for {
				if !(iCopy < len(pendingClientsCopy)) {
					break
				}
				client := pendingClientsCopy[0]
				key0 := client
				index := sort.Search(len(pendingRequestsCopy), func(i0 int) bool {
					return !(pendingRequestsCopy[i0].key < key0)
				})
				firstPendingCopy = pendingRequestsCopy[index].value[0]
				if !(firstPendingCopy["op"].(string) == GET_MSG || firstPendingCopy["op"].(string) == PUT_MSG) {
					panic("(((firstPending).op) = (GET_MSG)) \\/ (((firstPending).op) = (PUT_MSG))")
				}
				timestampCopy = firstPendingCopy["timestamp"].(int)
				if timestampCopy < minClockCopy {
					chooseMessageCopy = timestampCopy < lowestPendingCopy || timestampCopy == lowestPendingCopy && client < nextClientCopy
					if chooseMessageCopy {
						nextClientCopy = client
						lowestPendingCopy = timestampCopy
					}
				}
				tmpSet0 := make([]int, 0, len(pendingClientsCopy))
				for _, v := range pendingClientsCopy {
					if v != client {
						tmpSet0 = append(tmpSet0, v)
					}
				}
				pendingClientsCopy = tmpSet0
				i = iCopy
				pendingRequests = pendingRequestsCopy
				lowestPending = lowestPendingCopy
				pendingClients = pendingClientsCopy
				nextClient = nextClientCopy
				firstPending = firstPendingCopy
				chooseMessage = chooseMessageCopy
				timestamp = timestampCopy
				minClock = minClockCopy
				acquiredResources = map[string]map[interface{}]bool{}
				iCopy3 := i
				iCopy = iCopy3
				pendingRequestsCopy4 := make([]struct {
					key   int
					value []map[string]interface{}
				}, len(pendingRequests))
				for i1, e := range pendingRequests {
					field := e.key
					fieldCopy := field
					field0 := e.value
					field0Copy := make([]map[string]interface{}, len(field0))
					for i2, e0 := range field0 {
						e0Copy := make(map[string]interface{}, len(e0))
						for k, v := range e0 {
							vCopy := v
							e0Copy[k] = vCopy
						}
						field0Copy[i2] = e0Copy
					}
					eCopy := struct {
						key   int
						value []map[string]interface{}
					}{key: fieldCopy, value: field0Copy}
					pendingRequestsCopy4[i1] = eCopy
				}
				pendingRequestsCopy = pendingRequestsCopy4
				lowestPendingCopy2 := lowestPending
				lowestPendingCopy = lowestPendingCopy2
				pendingClientsCopy2 := make([]int, len(pendingClients))
				for i1, e := range pendingClients {
					eCopy := e
					pendingClientsCopy2[i1] = eCopy
				}
				pendingClientsCopy = pendingClientsCopy2
				nextClientCopy2 := nextClient
				nextClientCopy = nextClientCopy2
				firstPendingCopy1 := make(map[string]interface{}, len(firstPending))
				for k, v := range firstPending {
					vCopy := v
					firstPendingCopy1[k] = vCopy
				}
				firstPendingCopy = firstPendingCopy1
				chooseMessageCopy1 := chooseMessage
				chooseMessageCopy = chooseMessageCopy1
				timestampCopy1 := timestamp
				timestampCopy = timestampCopy1
				minClockCopy3 := minClock
				minClockCopy = minClockCopy3
			}
			i = iCopy
			pendingRequests = pendingRequestsCopy
			lowestPending = lowestPendingCopy
			pendingClients = pendingClientsCopy
			nextClient = nextClientCopy
			firstPending = firstPendingCopy
			chooseMessage = chooseMessageCopy
			timestamp = timestampCopy
			minClock = minClockCopy

			// addStableMessage:
			acquiredResources = map[string]map[interface{}]bool{}
			pendingRequestsCopy4 := make([]struct {
				key   int
				value []map[string]interface{}
			}, len(pendingRequests))
			for i0, e := range pendingRequests {
				field := e.key
				fieldCopy := field
				field0 := e.value
				field0Copy := make([]map[string]interface{}, len(field0))
				for i1, e0 := range field0 {
					e0Copy := make(map[string]interface{}, len(e0))
					for k, v := range e0 {
						vCopy := v
						e0Copy[k] = vCopy
					}
					field0Copy[i1] = e0Copy
				}
				eCopy := struct {
					key   int
					value []map[string]interface{}
				}{key: fieldCopy, value: field0Copy}
				pendingRequestsCopy4[i0] = eCopy
			}
			pendingRequestsCopy = pendingRequestsCopy4
			lowestPendingCopy2 := lowestPending
			lowestPendingCopy = lowestPendingCopy2
			msgCopy5 := make(map[string]interface{}, len(msg))
			for k, v := range msg {
				vCopy := v
				msgCopy5[k] = vCopy
			}
			msgCopy = msgCopy5
			nextClientCopy2 := nextClient
			nextClientCopy = nextClientCopy2
			continue0Copy1 := continue0
			continueCopy = continue0Copy1
			stableMessagesCopy1 := make([]map[string]interface{}, len(stableMessages))
			for i0, e := range stableMessages {
				eCopy := make(map[string]interface{}, len(e))
				for k, v := range e {
					vCopy := v
					eCopy[k] = vCopy
				}
				stableMessagesCopy1[i0] = eCopy
			}
			stableMessagesCopy = stableMessagesCopy1
			minClockCopy3 := minClock
			minClockCopy = minClockCopy3
			if lowestPendingCopy < minClockCopy {
				key0 := nextClientCopy
				index := sort.Search(len(pendingRequestsCopy), func(i0 int) bool {
					return !(pendingRequestsCopy[i0].key < key0)
				})
				msgCopy = pendingRequestsCopy[index].value[0]
				key1 := nextClientCopy
				index0 := sort.Search(len(pendingRequestsCopy), func(i1 int) bool {
					return !(pendingRequestsCopy[i1].key < key1)
				})
				key2 := nextClientCopy
				index1 := sort.Search(len(pendingRequestsCopy), func(i2 int) bool {
					return !(pendingRequestsCopy[i2].key < key2)
				})
				pendingRequestsCopy[index0].value = pendingRequestsCopy[index1].value[1:]
				tmpSlice := make([]map[string]interface{}, len(stableMessagesCopy), len(stableMessagesCopy)+1)
				copy(tmpSlice, stableMessagesCopy)
				tmpSlice = append(tmpSlice, msgCopy)
				stableMessagesCopy = tmpSlice
			} else {
				continueCopy = false
			}
			pendingRequests = pendingRequestsCopy
			lowestPending = lowestPendingCopy
			msg = msgCopy
			nextClient = nextClientCopy
			continue0 = continueCopy
			stableMessages = stableMessagesCopy
			minClock = minClockCopy
			acquiredResources = map[string]map[interface{}]bool{}
			clientsIterCopy2 := make([]int, len(clientsIter))
			for i0, e := range clientsIter {
				eCopy := e
				clientsIterCopy2[i0] = eCopy
			}
			clientsIterCopy = clientsIterCopy2
			iCopy3 := i
			iCopy = iCopy3
			pendingRequestsCopy5 := make([]struct {
				key   int
				value []map[string]interface{}
			}, len(pendingRequests))
			for i0, e := range pendingRequests {
				field := e.key
				fieldCopy := field
				field0 := e.value
				field0Copy := make([]map[string]interface{}, len(field0))
				for i1, e0 := range field0 {
					e0Copy := make(map[string]interface{}, len(e0))
					for k, v := range e0 {
						vCopy := v
						e0Copy[k] = vCopy
					}
					field0Copy[i1] = e0Copy
				}
				eCopy := struct {
					key   int
					value []map[string]interface{}
				}{key: fieldCopy, value: field0Copy}
				pendingRequestsCopy5[i0] = eCopy
			}
			pendingRequestsCopy = pendingRequestsCopy5
			pendingClientsCopy2 := make([]int, len(pendingClients))
			for i0, e := range pendingClients {
				eCopy := e
				pendingClientsCopy2[i0] = eCopy
			}
			pendingClientsCopy = pendingClientsCopy2
			nextClientCopy3 := nextClient
			nextClientCopy = nextClientCopy3
			continue0Copy2 := continue0
			continueCopy = continue0Copy2
			liveClientsCopy3 := make([]int, len(liveClients))
			for i0, e := range liveClients {
				eCopy := e
				liveClientsCopy3[i0] = eCopy
			}
			liveClientsCopy = liveClientsCopy3
			minClockCopy4 := minClock
			minClockCopy = minClockCopy4
		}
		iCopy = 1

		// respondPendingRequestsLoop:
		clientsIter = clientsIterCopy
		i = iCopy
		pendingRequests = pendingRequestsCopy
		pendingClients = pendingClientsCopy
		nextClient = nextClientCopy
		continue0 = continueCopy
		liveClients = liveClientsCopy
		minClock = minClockCopy
		acquiredResources = map[string]map[interface{}]bool{}
		iCopy1 := i
		iCopy = iCopy1
		msgCopy5 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy5[k] = vCopy
		}
		msgCopy = msgCopy5
		stableMessagesCopy1 := make([]map[string]interface{}, len(stableMessages))
		for i0, e := range stableMessages {
			eCopy := make(map[string]interface{}, len(e))
			for k, v := range e {
				vCopy := v
				eCopy[k] = vCopy
			}
			stableMessagesCopy1[i0] = eCopy
		}
		stableMessagesCopy = stableMessagesCopy1
		for {
			if !(iCopy <= len(stableMessagesCopy)) {
				i = iCopy
				msg = msgCopy
				stableMessages = stableMessagesCopy
				break
			}
			msgCopy = stableMessagesCopy[iCopy-1]
			iCopy = iCopy + 1

			// respondStableGet:
			i = iCopy
			msg = msgCopy
			stableMessages = stableMessagesCopy
		respondStableGet:
			acquiredResources = map[string]map[interface{}]bool{}
			keyCopy0 := key
			keyCopy = keyCopy0
			valCopy0 := val
			valCopy = valCopy0
			msgCopy6 := make(map[string]interface{}, len(msg))
			for k, v := range msg {
				vCopy := v
				msgCopy6[k] = vCopy
			}
			msgCopy = msgCopy6
			if msgCopy["op"].(string) == GET_MSG {
				keyCopy = msgCopy["key"]
				if _, ok0 := acquiredResources["kv"]; !ok0 {
					acquiredResources["kv"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["kv"][keyCopy]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, kv.Get(keyCopy))
					if err != nil {
						for r, _ := range acquiredResources["kv"] {
							distsys.AbortResources(kv.Get(r))
						}
						if shouldRetry(err) {
							goto respondStableGet
						} else {
							return err
						}
					}
					acquiredResources["kv"][keyCopy] = true
				}
				var readTemp0 interface{}
				readTemp0, err = kv.Get(keyCopy).Read()
				if err != nil {
					for r, _ := range acquiredResources["kv"] {
						distsys.AbortResources(kv.Get(r))
					}
					if shouldRetry(err) {
						goto respondStableGet
					} else {
						return err
					}
				}
				valCopy = readTemp0
				if _, ok0 := acquiredResources["clients"]; !ok0 {
					acquiredResources["clients"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clients"][msgCopy["client"].(int)]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, clients.Get(msgCopy["client"].(int)))
					if err != nil {
						for r, _ := range acquiredResources["clients"] {
							distsys.AbortResources(clients.Get(r))
						}
						for r, _ := range acquiredResources["kv"] {
							distsys.AbortResources(kv.Get(r))
						}
						if shouldRetry(err) {
							goto respondStableGet
						} else {
							return err
						}
					}
					acquiredResources["clients"][msgCopy["client"].(int)] = true
				}
				var resourceWrite interface{}
				resourceWrite = map[string]interface{}{
					"result": valCopy,
					"type":   GET_RESPONSE,
				}
				err = clients.Get(msgCopy["client"].(int)).Write(resourceWrite)
				if err != nil {
					for r, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r))
					}
					for r, _ := range acquiredResources["kv"] {
						distsys.AbortResources(kv.Get(r))
					}
					if shouldRetry(err) {
						goto respondStableGet
					} else {
						return err
					}
				}
			}
			for r, _ := range acquiredResources["clients"] {
				err = distsys.ReleaseResources(clients.Get(r))
				if err != nil {
					for r0, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r0))
					}
					for r0, _ := range acquiredResources["kv"] {
						distsys.AbortResources(kv.Get(r0))
					}
					return err
				}
			}
			for r, _ := range acquiredResources["kv"] {
				err = distsys.ReleaseResources(kv.Get(r))
				if err != nil {
					for r0, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r0))
					}
					for r0, _ := range acquiredResources["kv"] {
						distsys.AbortResources(kv.Get(r0))
					}
					return err
				}
			}
			key = keyCopy
			val = valCopy
			msg = msgCopy

			// respondStablePut:
		respondStablePut:
			acquiredResources = map[string]map[interface{}]bool{}
			okCopy0 := ok
			okCopy = okCopy0
			keyCopy1 := key
			keyCopy = keyCopy1
			valCopy1 := val
			valCopy = valCopy1
			msgCopy7 := make(map[string]interface{}, len(msg))
			for k, v := range msg {
				vCopy := v
				msgCopy7[k] = vCopy
			}
			msgCopy = msgCopy7
			if msgCopy["op"].(string) == PUT_MSG {
				keyCopy = msgCopy["key"]
				valCopy = msgCopy["value"]
				if _, ok0 := acquiredResources["kv"]; !ok0 {
					acquiredResources["kv"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["kv"][keyCopy]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, kv.Get(keyCopy))
					if err != nil {
						for r, _ := range acquiredResources["kv"] {
							distsys.AbortResources(kv.Get(r))
						}
						if shouldRetry(err) {
							goto respondStablePut
						} else {
							return err
						}
					}
					acquiredResources["kv"][keyCopy] = true
				}
				var resourceWrite interface{}
				resourceWrite = valCopy
				err = kv.Get(keyCopy).Write(resourceWrite)
				if err != nil {
					for r, _ := range acquiredResources["kv"] {
						distsys.AbortResources(kv.Get(r))
					}
					if shouldRetry(err) {
						goto respondStablePut
					} else {
						return err
					}
				}
				if _, ok0 := acquiredResources["clients"]; !ok0 {
					acquiredResources["clients"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clients"][msgCopy["client"].(int)]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, clients.Get(msgCopy["client"].(int)))
					if err != nil {
						for r, _ := range acquiredResources["clients"] {
							distsys.AbortResources(clients.Get(r))
						}
						for r, _ := range acquiredResources["kv"] {
							distsys.AbortResources(kv.Get(r))
						}
						if shouldRetry(err) {
							goto respondStablePut
						} else {
							return err
						}
					}
					acquiredResources["clients"][msgCopy["client"].(int)] = true
				}
				var resourceWrite0 interface{}
				resourceWrite0 = map[string]interface{}{
					"result": okCopy,
					"type":   PUT_RESPONSE,
				}
				err = clients.Get(msgCopy["client"].(int)).Write(resourceWrite0)
				if err != nil {
					for r, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r))
					}
					for r, _ := range acquiredResources["kv"] {
						distsys.AbortResources(kv.Get(r))
					}
					if shouldRetry(err) {
						goto respondStablePut
					} else {
						return err
					}
				}
			}
			for r, _ := range acquiredResources["clients"] {
				err = distsys.ReleaseResources(clients.Get(r))
				if err != nil {
					for r0, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r0))
					}
					for r0, _ := range acquiredResources["kv"] {
						distsys.AbortResources(kv.Get(r0))
					}
					return err
				}
			}
			for r, _ := range acquiredResources["kv"] {
				err = distsys.ReleaseResources(kv.Get(r))
				if err != nil {
					for r0, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r0))
					}
					for r0, _ := range acquiredResources["kv"] {
						distsys.AbortResources(kv.Get(r0))
					}
					return err
				}
			}
			ok = okCopy
			key = keyCopy
			val = valCopy
			msg = msgCopy
			acquiredResources = map[string]map[interface{}]bool{}
			iCopy2 := i
			iCopy = iCopy2
			msgCopy8 := make(map[string]interface{}, len(msg))
			for k, v := range msg {
				vCopy := v
				msgCopy8[k] = vCopy
			}
			msgCopy = msgCopy8
			stableMessagesCopy2 := make([]map[string]interface{}, len(stableMessages))
			for i0, e := range stableMessages {
				eCopy := make(map[string]interface{}, len(e))
				for k, v := range e {
					vCopy := v
					eCopy[k] = vCopy
				}
				stableMessagesCopy2[i0] = eCopy
			}
			stableMessagesCopy = stableMessagesCopy2
		}
		i = iCopy
		msg = msgCopy
		stableMessages = stableMessagesCopy
		acquiredResources = map[string]map[interface{}]bool{}
		continue0Copy1 := continue0
		continueCopy = continue0Copy1
		stableMessagesCopy2 := make([]map[string]interface{}, len(stableMessages))
		for i0, e := range stableMessages {
			eCopy := make(map[string]interface{}, len(e))
			for k, v := range e {
				vCopy := v
				eCopy[k] = vCopy
			}
			stableMessagesCopy2[i0] = eCopy
		}
		stableMessagesCopy = stableMessagesCopy2
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
	var continueCopy bool
	var getReqCopy map[string]interface{}
	var getRespCopy map[string]interface{}
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// getLoop:
	acquiredResources = map[string]map[interface{}]bool{}
	continue0Copy := continue0
	continueCopy = continue0Copy
	for {
		if !continueCopy {
			continue0 = continueCopy
			break
		}

		// getRequest:
		continue0 = continueCopy
	getRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		getReqCopy0 := make(map[string]interface{}, len(getReq))
		for k, v := range getReq {
			vCopy := v
			getReqCopy0[k] = vCopy
		}
		getReqCopy = getReqCopy0
		continue0Copy0 := continue0
		continueCopy = continue0Copy0
		err = distsys.AcquireResources(distsys.READ_ACCESS, clientId, key)
		if err != nil {
			if shouldRetry(err) {
				goto getRequest
			} else {
				return err
			}
		}
		var readTemp interface{}
		readTemp, err = clientId.Read()
		if err != nil {
			distsys.AbortResources(key, clientId)
			if shouldRetry(err) {
				goto getRequest
			} else {
				return err
			}
		}
		if _, ok := acquiredResources["locked"]; !ok {
			acquiredResources["locked"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["locked"][readTemp]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, locked.Get(readTemp))
			if err != nil {
				distsys.AbortResources(key, clientId)
				for r, _ := range acquiredResources["locked"] {
					distsys.AbortResources(locked.Get(r))
				}
				if shouldRetry(err) {
					goto getRequest
				} else {
					return err
				}
			}
			acquiredResources["locked"][readTemp] = true
		}
		var readTemp0 interface{}
		readTemp0, err = locked.Get(readTemp).Read()
		if err != nil {
			distsys.AbortResources(key, clientId)
			for r, _ := range acquiredResources["locked"] {
				distsys.AbortResources(locked.Get(r))
			}
			if shouldRetry(err) {
				goto getRequest
			} else {
				return err
			}
		}
		if !readTemp0.(bool) {
			var readTemp1 interface{}
			readTemp1, err = clientId.Read()
			if err != nil {
				distsys.AbortResources(key, clientId)
				for r, _ := range acquiredResources["locked"] {
					distsys.AbortResources(locked.Get(r))
				}
				if shouldRetry(err) {
					goto getRequest
				} else {
					return err
				}
			}
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][readTemp1]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp1))
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				acquiredResources["clock"][readTemp1] = true
			}
			var readTemp2 interface{}
			readTemp2, err = clock.Get(readTemp1).Read()
			if err != nil {
				distsys.AbortResources(key, clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				for r, _ := range acquiredResources["locked"] {
					distsys.AbortResources(locked.Get(r))
				}
				if shouldRetry(err) {
					goto getRequest
				} else {
					return err
				}
			}
			if readTemp2.(int) == -1 {
				continueCopy = false
				err = distsys.ReleaseResources(key, clientId)
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					return err
				}
				for r, _ := range acquiredResources["clock"] {
					err = distsys.ReleaseResources(clock.Get(r))
					if err != nil {
						distsys.AbortResources(key, clientId)
						for r0, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				for r, _ := range acquiredResources["locked"] {
					err = distsys.ReleaseResources(locked.Get(r))
					if err != nil {
						distsys.AbortResources(key, clientId)
						for r0, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				getReq = getReqCopy
				continue0 = continueCopy
			} else {
				var readTemp3 interface{}
				readTemp3, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["locked"]; !ok {
					acquiredResources["locked"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["locked"][readTemp3]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, locked.Get(readTemp3))
					if err != nil {
						distsys.AbortResources(key, clientId)
						for r, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r))
						}
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto getRequest
						} else {
							return err
						}
					}
					acquiredResources["locked"][readTemp3] = true
				}
				var resourceWrite interface{}
				resourceWrite = true
				err = locked.Get(readTemp3).Write(resourceWrite)
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				var readTemp4 interface{}
				readTemp4, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["clock"]; !ok {
					acquiredResources["clock"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clock"][readTemp4]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp4))
					if err != nil {
						distsys.AbortResources(key, clientId)
						for r, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r))
						}
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto getRequest
						} else {
							return err
						}
					}
					acquiredResources["clock"][readTemp4] = true
				}
				var resourceWrite0 interface{}
				var readTemp5 interface{}
				readTemp5, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["clock"]; !ok {
					acquiredResources["clock"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clock"][readTemp5]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp5))
					if err != nil {
						distsys.AbortResources(key, clientId)
						for r, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r))
						}
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto getRequest
						} else {
							return err
						}
					}
					acquiredResources["clock"][readTemp5] = true
				}
				var readTemp6 interface{}
				readTemp6, err = clock.Get(readTemp5).Read()
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				resourceWrite0 = readTemp6.(int) + 1
				err = clock.Get(readTemp4).Write(resourceWrite0)
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				var readTemp7 interface{}
				readTemp7, err = key.Read()
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				var readTemp8 interface{}
				readTemp8, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				var readTemp9 interface{}
				readTemp9, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["clock"]; !ok {
					acquiredResources["clock"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clock"][readTemp9]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp9))
					if err != nil {
						distsys.AbortResources(key, clientId)
						for r, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r))
						}
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto getRequest
						} else {
							return err
						}
					}
					acquiredResources["clock"][readTemp9] = true
				}
				var readTemp10 interface{}
				readTemp10, err = clock.Get(readTemp9).Read()
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}
				getReqCopy = map[string]interface{}{
					"op":        GET_MSG,
					"client":    readTemp8,
					"timestamp": readTemp10.(int),
					"key":       readTemp7,
				}
				dst := ReplicaSet()[0]
				if _, ok := acquiredResources["replicas"]; !ok {
					acquiredResources["replicas"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["replicas"][dst]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, replicas.Get(dst))
					if err != nil {
						distsys.AbortResources(key, clientId)
						for r, _ := range acquiredResources["replicas"] {
							distsys.AbortResources(replicas.Get(r))
						}
						for r, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r))
						}
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto getRequest
						} else {
							return err
						}
					}
					acquiredResources["replicas"][dst] = true
				}
				var resourceWrite1 interface{}
				resourceWrite1 = getReqCopy
				err = replicas.Get(dst).Write(resourceWrite1)
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["replicas"] {
						distsys.AbortResources(replicas.Get(r))
					}
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getRequest
					} else {
						return err
					}
				}

				// getReply:
				err = distsys.ReleaseResources(key, clientId)
				if err != nil {
					distsys.AbortResources(key, clientId)
					for r, _ := range acquiredResources["replicas"] {
						distsys.AbortResources(replicas.Get(r))
					}
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					return err
				}
				for r, _ := range acquiredResources["replicas"] {
					err = distsys.ReleaseResources(replicas.Get(r))
					if err != nil {
						distsys.AbortResources(key, clientId)
						for r0, _ := range acquiredResources["replicas"] {
							distsys.AbortResources(replicas.Get(r0))
						}
						for r0, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				for r, _ := range acquiredResources["clock"] {
					err = distsys.ReleaseResources(clock.Get(r))
					if err != nil {
						distsys.AbortResources(key, clientId)
						for r0, _ := range acquiredResources["replicas"] {
							distsys.AbortResources(replicas.Get(r0))
						}
						for r0, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				for r, _ := range acquiredResources["locked"] {
					err = distsys.ReleaseResources(locked.Get(r))
					if err != nil {
						distsys.AbortResources(key, clientId)
						for r0, _ := range acquiredResources["replicas"] {
							distsys.AbortResources(replicas.Get(r0))
						}
						for r0, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				getReq = getReqCopy
				continue0 = continueCopy
			getReply:
				acquiredResources = map[string]map[interface{}]bool{}
				getRespCopy0 := make(map[string]interface{}, len(getResp))
				for k, v := range getResp {
					vCopy := v
					getRespCopy0[k] = vCopy
				}
				getRespCopy = getRespCopy0
				err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
				if err != nil {
					if shouldRetry(err) {
						goto getReply
					} else {
						return err
					}
				}
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, outside)
				if err != nil {
					if shouldRetry(err) {
						goto getReply
					} else {
						return err
					}
				}
				var readTemp11 interface{}
				readTemp11, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(clientId, outside)
					if shouldRetry(err) {
						goto getReply
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["clients"]; !ok {
					acquiredResources["clients"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clients"][readTemp11]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, clients.Get(readTemp11))
					if err != nil {
						distsys.AbortResources(clientId, outside)
						for r, _ := range acquiredResources["clients"] {
							distsys.AbortResources(clients.Get(r))
						}
						if shouldRetry(err) {
							goto getReply
						} else {
							return err
						}
					}
					acquiredResources["clients"][readTemp11] = true
				}
				var readTemp12 interface{}
				readTemp12, err = clients.Get(readTemp11).Read()
				if err != nil {
					distsys.AbortResources(clientId, outside)
					for r, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r))
					}
					if shouldRetry(err) {
						goto getReply
					} else {
						return err
					}
				}
				getRespCopy = readTemp12.(map[string]interface{})
				if !(getRespCopy["type"].(string) == GET_RESPONSE) {
					panic("((getResp).type) = (GET_RESPONSE)")
				}
				var readTemp13 interface{}
				readTemp13, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(clientId, outside)
					for r, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r))
					}
					if shouldRetry(err) {
						goto getReply
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["locked"]; !ok {
					acquiredResources["locked"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["locked"][readTemp13]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, locked.Get(readTemp13))
					if err != nil {
						distsys.AbortResources(clientId, outside)
						for r, _ := range acquiredResources["clients"] {
							distsys.AbortResources(clients.Get(r))
						}
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto getReply
						} else {
							return err
						}
					}
					acquiredResources["locked"][readTemp13] = true
				}
				var resourceWrite2 interface{}
				resourceWrite2 = false
				err = locked.Get(readTemp13).Write(resourceWrite2)
				if err != nil {
					distsys.AbortResources(clientId, outside)
					for r, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getReply
					} else {
						return err
					}
				}
				var resourceWrite3 interface{}
				resourceWrite3 = getRespCopy["result"]
				err = outside.Write(resourceWrite3)
				if err != nil {
					distsys.AbortResources(clientId, outside)
					for r, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto getReply
					} else {
						return err
					}
				}
				err = distsys.ReleaseResources(clientId, outside)
				if err != nil {
					distsys.AbortResources(clientId, outside)
					for r, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					return err
				}
				for r, _ := range acquiredResources["clients"] {
					err = distsys.ReleaseResources(clients.Get(r))
					if err != nil {
						distsys.AbortResources(clientId, outside)
						for r0, _ := range acquiredResources["clients"] {
							distsys.AbortResources(clients.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				for r, _ := range acquiredResources["locked"] {
					err = distsys.ReleaseResources(locked.Get(r))
					if err != nil {
						distsys.AbortResources(clientId, outside)
						for r0, _ := range acquiredResources["clients"] {
							distsys.AbortResources(clients.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				getResp = getRespCopy
			}
		} else {
			err = distsys.ReleaseResources(key, clientId)
			if err != nil {
				distsys.AbortResources(clientId, outside)
				for r, _ := range acquiredResources["clients"] {
					distsys.AbortResources(clients.Get(r))
				}
				for r, _ := range acquiredResources["locked"] {
					distsys.AbortResources(locked.Get(r))
				}
				return err
			}
			for r, _ := range acquiredResources["clients"] {
				err = distsys.ReleaseResources(clients.Get(r))
				if err != nil {
					distsys.AbortResources(clientId, outside)
					for r0, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r0))
					}
					for r0, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r0))
					}
					return err
				}
			}
			for r, _ := range acquiredResources["locked"] {
				err = distsys.ReleaseResources(locked.Get(r))
				if err != nil {
					distsys.AbortResources(clientId, outside)
					for r0, _ := range acquiredResources["clients"] {
						distsys.AbortResources(clients.Get(r0))
					}
					for r0, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r0))
					}
					return err
				}
			}
			getReq = getReqCopy
			continue0 = continueCopy
		}

		// getCheckSpin:
	getCheckSpin:
		acquiredResources = map[string]map[interface{}]bool{}
		continue0Copy1 := continue0
		continueCopy = continue0Copy1
		err = distsys.AcquireResources(distsys.READ_ACCESS, spin)
		if err != nil {
			if shouldRetry(err) {
				goto getCheckSpin
			} else {
				return err
			}
		}
		var readTemp1 interface{}
		readTemp1, err = spin.Read()
		if err != nil {
			distsys.AbortResources(spin)
			if shouldRetry(err) {
				goto getCheckSpin
			} else {
				return err
			}
		}
		if !readTemp1.(bool) {
			continueCopy = false
		}
		err = distsys.ReleaseResources(spin)
		if err != nil {
			distsys.AbortResources(spin)
			return err
		}
		continue0 = continueCopy
		acquiredResources = map[string]map[interface{}]bool{}
		continue0Copy2 := continue0
		continueCopy = continue0Copy2
	}
	return nil
}

func Put(self int, clientId distsys.ArchetypeResource, replicas distsys.ArchetypeResourceCollection, clients distsys.ArchetypeResourceCollection, key distsys.ArchetypeResource, value distsys.ArchetypeResource, locked distsys.ArchetypeResourceCollection, clock distsys.ArchetypeResourceCollection, spin distsys.ArchetypeResource, outside distsys.ArchetypeResource) error {
	continue0 := true
	var i int
	var j int
	var putReq map[string]interface{}
	var putResp map[string]interface{}
	var continueCopy bool
	var iCopy int
	var jCopy int
	var putReqCopy map[string]interface{}
	var putRespCopy map[string]interface{}
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// putLoop:
	acquiredResources = map[string]map[interface{}]bool{}
	continue0Copy := continue0
	continueCopy = continue0Copy
	for {
		if !continueCopy {
			continue0 = continueCopy
			break
		}

		// putRequest:
		continue0 = continueCopy
	putRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		iCopy0 := i
		iCopy = iCopy0
		putReqCopy0 := make(map[string]interface{}, len(putReq))
		for k, v := range putReq {
			vCopy := v
			putReqCopy0[k] = vCopy
		}
		putReqCopy = putReqCopy0
		jCopy0 := j
		jCopy = jCopy0
		continue0Copy0 := continue0
		continueCopy = continue0Copy0
		err = distsys.AcquireResources(distsys.READ_ACCESS, clientId, value, key)
		if err != nil {
			if shouldRetry(err) {
				goto putRequest
			} else {
				return err
			}
		}
		var readTemp interface{}
		readTemp, err = clientId.Read()
		if err != nil {
			distsys.AbortResources(key, value, clientId)
			if shouldRetry(err) {
				goto putRequest
			} else {
				return err
			}
		}
		if _, ok := acquiredResources["locked"]; !ok {
			acquiredResources["locked"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["locked"][readTemp]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, locked.Get(readTemp))
			if err != nil {
				distsys.AbortResources(key, value, clientId)
				for r, _ := range acquiredResources["locked"] {
					distsys.AbortResources(locked.Get(r))
				}
				if shouldRetry(err) {
					goto putRequest
				} else {
					return err
				}
			}
			acquiredResources["locked"][readTemp] = true
		}
		var readTemp0 interface{}
		readTemp0, err = locked.Get(readTemp).Read()
		if err != nil {
			distsys.AbortResources(key, value, clientId)
			for r, _ := range acquiredResources["locked"] {
				distsys.AbortResources(locked.Get(r))
			}
			if shouldRetry(err) {
				goto putRequest
			} else {
				return err
			}
		}
		if !readTemp0.(bool) {
			var readTemp1 interface{}
			readTemp1, err = clientId.Read()
			if err != nil {
				distsys.AbortResources(key, value, clientId)
				for r, _ := range acquiredResources["locked"] {
					distsys.AbortResources(locked.Get(r))
				}
				if shouldRetry(err) {
					goto putRequest
				} else {
					return err
				}
			}
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][readTemp1]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp1))
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				acquiredResources["clock"][readTemp1] = true
			}
			var readTemp2 interface{}
			readTemp2, err = clock.Get(readTemp1).Read()
			if err != nil {
				distsys.AbortResources(key, value, clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				for r, _ := range acquiredResources["locked"] {
					distsys.AbortResources(locked.Get(r))
				}
				if shouldRetry(err) {
					goto putRequest
				} else {
					return err
				}
			}
			if readTemp2.(int) == -1 {
				continueCopy = false
				err = distsys.ReleaseResources(key, value, clientId)
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					return err
				}
				for r, _ := range acquiredResources["clock"] {
					err = distsys.ReleaseResources(clock.Get(r))
					if err != nil {
						distsys.AbortResources(key, value, clientId)
						for r0, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				for r, _ := range acquiredResources["locked"] {
					err = distsys.ReleaseResources(locked.Get(r))
					if err != nil {
						distsys.AbortResources(key, value, clientId)
						for r0, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				i = iCopy
				putReq = putReqCopy
				j = jCopy
				continue0 = continueCopy
			} else {
				var readTemp3 interface{}
				readTemp3, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["clock"]; !ok {
					acquiredResources["clock"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clock"][readTemp3]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp3))
					if err != nil {
						distsys.AbortResources(key, value, clientId)
						for r, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r))
						}
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto putRequest
						} else {
							return err
						}
					}
					acquiredResources["clock"][readTemp3] = true
				}
				var resourceWrite interface{}
				var readTemp4 interface{}
				readTemp4, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["clock"]; !ok {
					acquiredResources["clock"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clock"][readTemp4]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp4))
					if err != nil {
						distsys.AbortResources(key, value, clientId)
						for r, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r))
						}
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto putRequest
						} else {
							return err
						}
					}
					acquiredResources["clock"][readTemp4] = true
				}
				var readTemp5 interface{}
				readTemp5, err = clock.Get(readTemp4).Read()
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				resourceWrite = readTemp5.(int) + 1
				err = clock.Get(readTemp3).Write(resourceWrite)
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				var readTemp6 interface{}
				readTemp6, err = key.Read()
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				var readTemp7 interface{}
				readTemp7, err = value.Read()
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				var readTemp8 interface{}
				readTemp8, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				var readTemp9 interface{}
				readTemp9, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["clock"]; !ok {
					acquiredResources["clock"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["clock"][readTemp9]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp9))
					if err != nil {
						distsys.AbortResources(key, value, clientId)
						for r, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r))
						}
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto putRequest
						} else {
							return err
						}
					}
					acquiredResources["clock"][readTemp9] = true
				}
				var readTemp10 interface{}
				readTemp10, err = clock.Get(readTemp9).Read()
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				putReqCopy = map[string]interface{}{
					"op":        PUT_MSG,
					"client":    readTemp8,
					"value":     readTemp7,
					"timestamp": readTemp10.(int),
					"key":       readTemp6,
				}
				var readTemp11 interface{}
				readTemp11, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["locked"]; !ok {
					acquiredResources["locked"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["locked"][readTemp11]; !acquired {
					err = distsys.AcquireResources(distsys.READ_ACCESS, locked.Get(readTemp11))
					if err != nil {
						distsys.AbortResources(key, value, clientId)
						for r, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r))
						}
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto putRequest
						} else {
							return err
						}
					}
					acquiredResources["locked"][readTemp11] = true
				}
				var resourceWrite0 interface{}
				resourceWrite0 = true
				err = locked.Get(readTemp11).Write(resourceWrite0)
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putRequest
					} else {
						return err
					}
				}
				iCopy = 0
				jCopy = 0

				// putBroadcast:
				err = distsys.ReleaseResources(key, value, clientId)
				if err != nil {
					distsys.AbortResources(key, value, clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					return err
				}
				for r, _ := range acquiredResources["clock"] {
					err = distsys.ReleaseResources(clock.Get(r))
					if err != nil {
						distsys.AbortResources(key, value, clientId)
						for r0, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				for r, _ := range acquiredResources["locked"] {
					err = distsys.ReleaseResources(locked.Get(r))
					if err != nil {
						distsys.AbortResources(key, value, clientId)
						for r0, _ := range acquiredResources["clock"] {
							distsys.AbortResources(clock.Get(r0))
						}
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				i = iCopy
				putReq = putReqCopy
				j = jCopy
				continue0 = continueCopy
			putBroadcast:
				acquiredResources = map[string]map[interface{}]bool{}
				putReqCopy1 := make(map[string]interface{}, len(putReq))
				for k, v := range putReq {
					vCopy := v
					putReqCopy1[k] = vCopy
				}
				putReqCopy = putReqCopy1
				jCopy1 := j
				jCopy = jCopy1
				for {
					if !(jCopy <= NUM_REPLICAS-1) {
						break
					}
					if _, ok := acquiredResources["replicas"]; !ok {
						acquiredResources["replicas"] = map[interface{}]bool{}
					}
					if _, acquired := acquiredResources["replicas"][jCopy]; !acquired {
						err = distsys.AcquireResources(distsys.WRITE_ACCESS, replicas.Get(jCopy))
						if err != nil {
							for r, _ := range acquiredResources["replicas"] {
								distsys.AbortResources(replicas.Get(r))
							}
							if shouldRetry(err) {
								goto putBroadcast
							} else {
								return err
							}
						}
						acquiredResources["replicas"][jCopy] = true
					}
					var resourceWrite1 interface{}
					resourceWrite1 = putReqCopy
					err = replicas.Get(jCopy).Write(resourceWrite1)
					if err != nil {
						for r, _ := range acquiredResources["replicas"] {
							distsys.AbortResources(replicas.Get(r))
						}
						if shouldRetry(err) {
							goto putBroadcast
						} else {
							return err
						}
					}
					jCopy = jCopy + 1
					for r, _ := range acquiredResources["replicas"] {
						err = distsys.ReleaseResources(replicas.Get(r))
						if err != nil {
							for r0, _ := range acquiredResources["replicas"] {
								distsys.AbortResources(replicas.Get(r0))
							}
							return err
						}
					}
					putReq = putReqCopy
					j = jCopy
					acquiredResources = map[string]map[interface{}]bool{}
					putReqCopy2 := make(map[string]interface{}, len(putReq))
					for k, v := range putReq {
						vCopy := v
						putReqCopy2[k] = vCopy
					}
					putReqCopy = putReqCopy2
					jCopy2 := j
					jCopy = jCopy2
				}
				putReq = putReqCopy
				j = jCopy

				// putResponse:
			putResponse:
				acquiredResources = map[string]map[interface{}]bool{}
				iCopy1 := i
				iCopy = iCopy1
				putRespCopy0 := make(map[string]interface{}, len(putResp))
				for k, v := range putResp {
					vCopy := v
					putRespCopy0[k] = vCopy
				}
				putRespCopy = putRespCopy0
				err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
				if err != nil {
					if shouldRetry(err) {
						goto putResponse
					} else {
						return err
					}
				}
				for {
					if !(iCopy < len(ReplicaSet())) {
						break
					}
					var readTemp12 interface{}
					readTemp12, err = clientId.Read()
					if err != nil {
						distsys.AbortResources(clientId)
						if shouldRetry(err) {
							goto putResponse
						} else {
							return err
						}
					}
					if _, ok := acquiredResources["clients"]; !ok {
						acquiredResources["clients"] = map[interface{}]bool{}
					}
					if _, acquired := acquiredResources["clients"][readTemp12]; !acquired {
						err = distsys.AcquireResources(distsys.READ_ACCESS, clients.Get(readTemp12))
						if err != nil {
							distsys.AbortResources(clientId)
							for r, _ := range acquiredResources["clients"] {
								distsys.AbortResources(clients.Get(r))
							}
							if shouldRetry(err) {
								goto putResponse
							} else {
								return err
							}
						}
						acquiredResources["clients"][readTemp12] = true
					}
					var readTemp13 interface{}
					readTemp13, err = clients.Get(readTemp12).Read()
					if err != nil {
						distsys.AbortResources(clientId)
						for r, _ := range acquiredResources["clients"] {
							distsys.AbortResources(clients.Get(r))
						}
						if shouldRetry(err) {
							goto putResponse
						} else {
							return err
						}
					}
					putRespCopy = readTemp13.(map[string]interface{})
					if !(putRespCopy["type"].(string) == PUT_RESPONSE) {
						panic("((putResp).type) = (PUT_RESPONSE)")
					}
					iCopy = iCopy + 1
					err = distsys.ReleaseResources(clientId)
					if err != nil {
						distsys.AbortResources(clientId)
						for r, _ := range acquiredResources["clients"] {
							distsys.AbortResources(clients.Get(r))
						}
						return err
					}
					for r, _ := range acquiredResources["clients"] {
						err = distsys.ReleaseResources(clients.Get(r))
						if err != nil {
							distsys.AbortResources(clientId)
							for r0, _ := range acquiredResources["clients"] {
								distsys.AbortResources(clients.Get(r0))
							}
							return err
						}
					}
					i = iCopy
					putResp = putRespCopy
					acquiredResources = map[string]map[interface{}]bool{}
					iCopy2 := i
					iCopy = iCopy2
					putRespCopy1 := make(map[string]interface{}, len(putResp))
					for k, v := range putResp {
						vCopy := v
						putRespCopy1[k] = vCopy
					}
					putRespCopy = putRespCopy1
					err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
					if err != nil {
						if shouldRetry(err) {
							goto putResponse
						} else {
							return err
						}
					}
				}
				var readTemp12 interface{}
				readTemp12, err = clientId.Read()
				if err != nil {
					distsys.AbortResources(clientId)
					if shouldRetry(err) {
						goto putResponse
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["locked"]; !ok {
					acquiredResources["locked"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["locked"][readTemp12]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, locked.Get(readTemp12))
					if err != nil {
						distsys.AbortResources(clientId)
						for r, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r))
						}
						if shouldRetry(err) {
							goto putResponse
						} else {
							return err
						}
					}
					acquiredResources["locked"][readTemp12] = true
				}
				var resourceWrite1 interface{}
				resourceWrite1 = false
				err = locked.Get(readTemp12).Write(resourceWrite1)
				if err != nil {
					distsys.AbortResources(clientId)
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					if shouldRetry(err) {
						goto putResponse
					} else {
						return err
					}
				}
				err = distsys.ReleaseResources(clientId)
				if err != nil {
					distsys.AbortResources(clientId)
					for r, _ := range acquiredResources["locked"] {
						distsys.AbortResources(locked.Get(r))
					}
					return err
				}
				for r, _ := range acquiredResources["locked"] {
					err = distsys.ReleaseResources(locked.Get(r))
					if err != nil {
						distsys.AbortResources(clientId)
						for r0, _ := range acquiredResources["locked"] {
							distsys.AbortResources(locked.Get(r0))
						}
						return err
					}
				}
				i = iCopy
				putResp = putRespCopy

				// putComplete:
			putComplete:
				acquiredResources = map[string]map[interface{}]bool{}
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, outside)
				if err != nil {
					if shouldRetry(err) {
						goto putComplete
					} else {
						return err
					}
				}
				var resourceWrite2 interface{}
				resourceWrite2 = PUT_RESPONSE
				err = outside.Write(resourceWrite2)
				if err != nil {
					distsys.AbortResources(outside)
					if shouldRetry(err) {
						goto putComplete
					} else {
						return err
					}
				}
				err = distsys.ReleaseResources(outside)
				if err != nil {
					distsys.AbortResources(outside)
					return err
				}
			}
		} else {
			err = distsys.ReleaseResources(key, value, clientId)
			if err != nil {
				distsys.AbortResources(outside)
				return err
			}
			i = iCopy
			putReq = putReqCopy
			j = jCopy
			continue0 = continueCopy
		}

		// putCheckSpin:
	putCheckSpin:
		acquiredResources = map[string]map[interface{}]bool{}
		continue0Copy1 := continue0
		continueCopy = continue0Copy1
		err = distsys.AcquireResources(distsys.READ_ACCESS, spin)
		if err != nil {
			if shouldRetry(err) {
				goto putCheckSpin
			} else {
				return err
			}
		}
		var readTemp1 interface{}
		readTemp1, err = spin.Read()
		if err != nil {
			distsys.AbortResources(spin)
			if shouldRetry(err) {
				goto putCheckSpin
			} else {
				return err
			}
		}
		if !readTemp1.(bool) {
			continueCopy = false
		}
		err = distsys.ReleaseResources(spin)
		if err != nil {
			distsys.AbortResources(spin)
			return err
		}
		continue0 = continueCopy
		acquiredResources = map[string]map[interface{}]bool{}
		continue0Copy2 := continue0
		continueCopy = continue0Copy2
	}
	return nil
}

func Disconnect(self int, clientId distsys.ArchetypeResource, replicas distsys.ArchetypeResourceCollection, locked distsys.ArchetypeResourceCollection, clock distsys.ArchetypeResourceCollection) error {
	var msg map[string]interface{}
	var j int
	var msgCopy map[string]interface{}
	var jCopy int
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// sendDisconnectRequest:
sendDisconnectRequest:
	acquiredResources = map[string]map[interface{}]bool{}
	msgCopy0 := make(map[string]interface{}, len(msg))
	for k, v := range msg {
		vCopy := v
		msgCopy0[k] = vCopy
	}
	msgCopy = msgCopy0
	jCopy0 := j
	jCopy = jCopy0
	err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
	if err != nil {
		if shouldRetry(err) {
			goto sendDisconnectRequest
		} else {
			return err
		}
	}
	var readTemp interface{}
	readTemp, err = clientId.Read()
	if err != nil {
		distsys.AbortResources(clientId)
		if shouldRetry(err) {
			goto sendDisconnectRequest
		} else {
			return err
		}
	}
	if _, ok := acquiredResources["locked"]; !ok {
		acquiredResources["locked"] = map[interface{}]bool{}
	}
	if _, acquired := acquiredResources["locked"][readTemp]; !acquired {
		err = distsys.AcquireResources(distsys.READ_ACCESS, locked.Get(readTemp))
		if err != nil {
			distsys.AbortResources(clientId)
			for r, _ := range acquiredResources["locked"] {
				distsys.AbortResources(locked.Get(r))
			}
			if shouldRetry(err) {
				goto sendDisconnectRequest
			} else {
				return err
			}
		}
		acquiredResources["locked"][readTemp] = true
	}
	var readTemp0 interface{}
	readTemp0, err = locked.Get(readTemp).Read()
	if err != nil {
		distsys.AbortResources(clientId)
		for r, _ := range acquiredResources["locked"] {
			distsys.AbortResources(locked.Get(r))
		}
		if shouldRetry(err) {
			goto sendDisconnectRequest
		} else {
			return err
		}
	}
	if !readTemp0.(bool) {
		var readTemp1 interface{}
		readTemp1, err = clientId.Read()
		if err != nil {
			distsys.AbortResources(clientId)
			for r, _ := range acquiredResources["locked"] {
				distsys.AbortResources(locked.Get(r))
			}
			if shouldRetry(err) {
				goto sendDisconnectRequest
			} else {
				return err
			}
		}
		msgCopy = map[string]interface{}{
			"op":     DISCONNECT_MSG,
			"client": readTemp1,
		}
		var readTemp2 interface{}
		readTemp2, err = clientId.Read()
		if err != nil {
			distsys.AbortResources(clientId)
			for r, _ := range acquiredResources["locked"] {
				distsys.AbortResources(locked.Get(r))
			}
			if shouldRetry(err) {
				goto sendDisconnectRequest
			} else {
				return err
			}
		}
		if _, ok := acquiredResources["clock"]; !ok {
			acquiredResources["clock"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["clock"][readTemp2]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, clock.Get(readTemp2))
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				for r, _ := range acquiredResources["locked"] {
					distsys.AbortResources(locked.Get(r))
				}
				if shouldRetry(err) {
					goto sendDisconnectRequest
				} else {
					return err
				}
			}
			acquiredResources["clock"][readTemp2] = true
		}
		var resourceWrite interface{}
		resourceWrite = -1
		err = clock.Get(readTemp2).Write(resourceWrite)
		if err != nil {
			distsys.AbortResources(clientId)
			for r, _ := range acquiredResources["clock"] {
				distsys.AbortResources(clock.Get(r))
			}
			for r, _ := range acquiredResources["locked"] {
				distsys.AbortResources(locked.Get(r))
			}
			if shouldRetry(err) {
				goto sendDisconnectRequest
			} else {
				return err
			}
		}
		jCopy = 0
	}
	err = distsys.ReleaseResources(clientId)
	if err != nil {
		distsys.AbortResources(clientId)
		for r, _ := range acquiredResources["clock"] {
			distsys.AbortResources(clock.Get(r))
		}
		for r, _ := range acquiredResources["locked"] {
			distsys.AbortResources(locked.Get(r))
		}
		return err
	}
	for r, _ := range acquiredResources["clock"] {
		err = distsys.ReleaseResources(clock.Get(r))
		if err != nil {
			distsys.AbortResources(clientId)
			for r0, _ := range acquiredResources["clock"] {
				distsys.AbortResources(clock.Get(r0))
			}
			for r0, _ := range acquiredResources["locked"] {
				distsys.AbortResources(locked.Get(r0))
			}
			return err
		}
	}
	for r, _ := range acquiredResources["locked"] {
		err = distsys.ReleaseResources(locked.Get(r))
		if err != nil {
			distsys.AbortResources(clientId)
			for r0, _ := range acquiredResources["clock"] {
				distsys.AbortResources(clock.Get(r0))
			}
			for r0, _ := range acquiredResources["locked"] {
				distsys.AbortResources(locked.Get(r0))
			}
			return err
		}
	}
	msg = msgCopy
	j = jCopy

	// disconnectBroadcast:
disconnectBroadcast:
	acquiredResources = map[string]map[interface{}]bool{}
	msgCopy1 := make(map[string]interface{}, len(msg))
	for k, v := range msg {
		vCopy := v
		msgCopy1[k] = vCopy
	}
	msgCopy = msgCopy1
	jCopy1 := j
	jCopy = jCopy1
	for {
		if !(jCopy <= NUM_REPLICAS-1) {
			break
		}
		if _, ok := acquiredResources["replicas"]; !ok {
			acquiredResources["replicas"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["replicas"][jCopy]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, replicas.Get(jCopy))
			if err != nil {
				for r, _ := range acquiredResources["replicas"] {
					distsys.AbortResources(replicas.Get(r))
				}
				if shouldRetry(err) {
					goto disconnectBroadcast
				} else {
					return err
				}
			}
			acquiredResources["replicas"][jCopy] = true
		}
		var resourceWrite interface{}
		resourceWrite = msgCopy
		err = replicas.Get(jCopy).Write(resourceWrite)
		if err != nil {
			for r, _ := range acquiredResources["replicas"] {
				distsys.AbortResources(replicas.Get(r))
			}
			if shouldRetry(err) {
				goto disconnectBroadcast
			} else {
				return err
			}
		}
		jCopy = jCopy + 1
		for r, _ := range acquiredResources["replicas"] {
			err = distsys.ReleaseResources(replicas.Get(r))
			if err != nil {
				for r0, _ := range acquiredResources["replicas"] {
					distsys.AbortResources(replicas.Get(r0))
				}
				return err
			}
		}
		msg = msgCopy
		j = jCopy
		acquiredResources = map[string]map[interface{}]bool{}
		msgCopy2 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy2[k] = vCopy
		}
		msgCopy = msgCopy2
		jCopy2 := j
		jCopy = jCopy2
	}
	msg = msgCopy
	j = jCopy
	return nil
}

func ClockUpdate(self int, clientId distsys.ArchetypeResource, replicas distsys.ArchetypeResourceCollection, clock distsys.ArchetypeResourceCollection, spin distsys.ArchetypeResource) error {
	continue0 := true
	var j int
	var msg map[string]interface{}
	var continueCopy bool
	var jCopy int
	var msgCopy map[string]interface{}
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// clockUpdateLoop:
clockUpdateLoop:
	acquiredResources = map[string]map[interface{}]bool{}
	msgCopy0 := make(map[string]interface{}, len(msg))
	for k, v := range msg {
		vCopy := v
		msgCopy0[k] = vCopy
	}
	msgCopy = msgCopy0
	continue0Copy := continue0
	continueCopy = continue0Copy
	jCopy0 := j
	jCopy = jCopy0
	err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
	if err != nil {
		if shouldRetry(err) {
			goto clockUpdateLoop
		} else {
			return err
		}
	}
	for {
		if !continueCopy {
			err = distsys.ReleaseResources(clientId)
			if err != nil {
				distsys.AbortResources(clientId)
				return err
			}
			msg = msgCopy
			continue0 = continueCopy
			j = jCopy
			break
		}
		var readTemp interface{}
		readTemp, err = clientId.Read()
		if err != nil {
			distsys.AbortResources(clientId)
			if shouldRetry(err) {
				goto clockUpdateLoop
			} else {
				return err
			}
		}
		if _, ok := acquiredResources["clock"]; !ok {
			acquiredResources["clock"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["clock"][readTemp]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp))
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				if shouldRetry(err) {
					goto clockUpdateLoop
				} else {
					return err
				}
			}
			acquiredResources["clock"][readTemp] = true
		}
		var readTemp0 interface{}
		readTemp0, err = clock.Get(readTemp).Read()
		if err != nil {
			distsys.AbortResources(clientId)
			for r, _ := range acquiredResources["clock"] {
				distsys.AbortResources(clock.Get(r))
			}
			if shouldRetry(err) {
				goto clockUpdateLoop
			} else {
				return err
			}
		}
		if readTemp0.(int) == -1 {
			continueCopy = false
			err = distsys.ReleaseResources(clientId)
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				return err
			}
			for r, _ := range acquiredResources["clock"] {
				err = distsys.ReleaseResources(clock.Get(r))
				if err != nil {
					distsys.AbortResources(clientId)
					for r0, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r0))
					}
					return err
				}
			}
			msg = msgCopy
			continue0 = continueCopy
			j = jCopy
		} else {
			var readTemp1 interface{}
			readTemp1, err = clientId.Read()
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				if shouldRetry(err) {
					goto clockUpdateLoop
				} else {
					return err
				}
			}
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][readTemp1]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp1))
				if err != nil {
					distsys.AbortResources(clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					if shouldRetry(err) {
						goto clockUpdateLoop
					} else {
						return err
					}
				}
				acquiredResources["clock"][readTemp1] = true
			}
			var resourceWrite interface{}
			var readTemp2 interface{}
			readTemp2, err = clientId.Read()
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				if shouldRetry(err) {
					goto clockUpdateLoop
				} else {
					return err
				}
			}
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][readTemp2]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp2))
				if err != nil {
					distsys.AbortResources(clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					if shouldRetry(err) {
						goto clockUpdateLoop
					} else {
						return err
					}
				}
				acquiredResources["clock"][readTemp2] = true
			}
			var readTemp3 interface{}
			readTemp3, err = clock.Get(readTemp2).Read()
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				if shouldRetry(err) {
					goto clockUpdateLoop
				} else {
					return err
				}
			}
			resourceWrite = readTemp3.(int) + 1
			err = clock.Get(readTemp1).Write(resourceWrite)
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				if shouldRetry(err) {
					goto clockUpdateLoop
				} else {
					return err
				}
			}
			var readTemp4 interface{}
			readTemp4, err = clientId.Read()
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				if shouldRetry(err) {
					goto clockUpdateLoop
				} else {
					return err
				}
			}
			var readTemp5 interface{}
			readTemp5, err = clientId.Read()
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				if shouldRetry(err) {
					goto clockUpdateLoop
				} else {
					return err
				}
			}
			if _, ok := acquiredResources["clock"]; !ok {
				acquiredResources["clock"] = map[interface{}]bool{}
			}
			if _, acquired := acquiredResources["clock"][readTemp5]; !acquired {
				err = distsys.AcquireResources(distsys.READ_ACCESS, clock.Get(readTemp5))
				if err != nil {
					distsys.AbortResources(clientId)
					for r, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r))
					}
					if shouldRetry(err) {
						goto clockUpdateLoop
					} else {
						return err
					}
				}
				acquiredResources["clock"][readTemp5] = true
			}
			var readTemp6 interface{}
			readTemp6, err = clock.Get(readTemp5).Read()
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				if shouldRetry(err) {
					goto clockUpdateLoop
				} else {
					return err
				}
			}
			msgCopy = map[string]interface{}{
				"op":        NULL_MSG,
				"client":    readTemp4,
				"timestamp": readTemp6.(int),
			}
			jCopy = 0

			// nullBroadcast:
			err = distsys.ReleaseResources(clientId)
			if err != nil {
				distsys.AbortResources(clientId)
				for r, _ := range acquiredResources["clock"] {
					distsys.AbortResources(clock.Get(r))
				}
				return err
			}
			for r, _ := range acquiredResources["clock"] {
				err = distsys.ReleaseResources(clock.Get(r))
				if err != nil {
					distsys.AbortResources(clientId)
					for r0, _ := range acquiredResources["clock"] {
						distsys.AbortResources(clock.Get(r0))
					}
					return err
				}
			}
			msg = msgCopy
			continue0 = continueCopy
			j = jCopy
		nullBroadcast:
			acquiredResources = map[string]map[interface{}]bool{}
			msgCopy1 := make(map[string]interface{}, len(msg))
			for k, v := range msg {
				vCopy := v
				msgCopy1[k] = vCopy
			}
			msgCopy = msgCopy1
			jCopy1 := j
			jCopy = jCopy1
			for {
				if !(jCopy <= NUM_REPLICAS-1) {
					break
				}
				if _, ok := acquiredResources["replicas"]; !ok {
					acquiredResources["replicas"] = map[interface{}]bool{}
				}
				if _, acquired := acquiredResources["replicas"][jCopy]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, replicas.Get(jCopy))
					if err != nil {
						for r, _ := range acquiredResources["replicas"] {
							distsys.AbortResources(replicas.Get(r))
						}
						if shouldRetry(err) {
							goto nullBroadcast
						} else {
							return err
						}
					}
					acquiredResources["replicas"][jCopy] = true
				}
				var resourceWrite0 interface{}
				resourceWrite0 = msgCopy
				err = replicas.Get(jCopy).Write(resourceWrite0)
				if err != nil {
					for r, _ := range acquiredResources["replicas"] {
						distsys.AbortResources(replicas.Get(r))
					}
					if shouldRetry(err) {
						goto nullBroadcast
					} else {
						return err
					}
				}
				jCopy = jCopy + 1
				for r, _ := range acquiredResources["replicas"] {
					err = distsys.ReleaseResources(replicas.Get(r))
					if err != nil {
						for r0, _ := range acquiredResources["replicas"] {
							distsys.AbortResources(replicas.Get(r0))
						}
						return err
					}
				}
				msg = msgCopy
				j = jCopy
				acquiredResources = map[string]map[interface{}]bool{}
				msgCopy2 := make(map[string]interface{}, len(msg))
				for k, v := range msg {
					vCopy := v
					msgCopy2[k] = vCopy
				}
				msgCopy = msgCopy2
				jCopy2 := j
				jCopy = jCopy2
			}
			msg = msgCopy
			j = jCopy
		}

		// nullCheckSpin:
	nullCheckSpin:
		acquiredResources = map[string]map[interface{}]bool{}
		continue0Copy0 := continue0
		continueCopy = continue0Copy0
		err = distsys.AcquireResources(distsys.READ_ACCESS, spin)
		if err != nil {
			if shouldRetry(err) {
				goto nullCheckSpin
			} else {
				return err
			}
		}
		var readTemp1 interface{}
		readTemp1, err = spin.Read()
		if err != nil {
			distsys.AbortResources(spin)
			if shouldRetry(err) {
				goto nullCheckSpin
			} else {
				return err
			}
		}
		if !readTemp1.(bool) {
			continueCopy = false
		}
		err = distsys.ReleaseResources(spin)
		if err != nil {
			distsys.AbortResources(spin)
			return err
		}
		continue0 = continueCopy
		acquiredResources = map[string]map[interface{}]bool{}
		msgCopy1 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy1[k] = vCopy
		}
		msgCopy = msgCopy1
		continue0Copy1 := continue0
		continueCopy = continue0Copy1
		jCopy1 := j
		jCopy = jCopy1
		err = distsys.AcquireResources(distsys.READ_ACCESS, clientId)
		if err != nil {
			if shouldRetry(err) {
				goto clockUpdateLoop
			} else {
				return err
			}
		}
	}
	return nil
}
