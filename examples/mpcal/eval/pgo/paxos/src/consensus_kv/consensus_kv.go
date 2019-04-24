package consensus_kv

import (
	"fmt"
	"math/rand"
	"pgo/distsys"
	"reflect"
	"time"
)

var sleepMin = 100

var sleepMax = 300

var NUM_NODES int

func init() {
	NUM_NODES = 3
	distsys.DefineCustomType(map[string]interface{}{})
	distsys.DefineCustomType([]map[string]interface{}{})
	rand.Seed(time.Now().UnixNano())
}

func shouldRetry(err error) bool {
	t := rand.Intn(sleepMax-sleepMin) + sleepMin
	switch err.(type) {
	case *distsys.AbortRetryError:
		time.Sleep(time.Duration(t) * time.Millisecond)
		return true
	case *distsys.ResourceInternalError:
		return false
	default:
		panic(fmt.Sprintf("Invalid error returned by Archetype Resource: %v", err))
	}
}

func GET_MSG() string {
	return "get_msg"
}

func PUT_MSG() string {
	return "put_msg"
}

func GET() string {
	return "get"
}

func PUT() string {
	return "put"
}

func OK_MSG() string {
	return "ok_msg"
}

func NOT_LEADER_MSG() string {
	return "not_leader_msg"
}

func KeyValueRequests(self int, requests distsys.ArchetypeResource, upstream distsys.ArchetypeResource, iAmTheLeader distsys.ArchetypeResourceCollection, proposerChan distsys.ArchetypeResourceCollection, paxosChan distsys.ArchetypeResourceCollection) error {
	var msg map[string]interface{}
	var null interface{}
	var heartbeatId int
	var proposerId int
	counter := 0
	var requestId []int
	var proposal map[string]interface{}
	var result interface{}
	var msgCopy map[string]interface{}
	var nullCopy interface{}
	var heartbeatIdCopy int
	var proposerIdCopy int
	var counterCopy int
	var requestIdCopy []int
	var proposalCopy map[string]interface{}
	var resultCopy interface{}
	var err error
	var acquiredResources map[string]map[uint64]interface{}

	// kvInit:
	acquiredResources = map[string]map[uint64]interface{}{}
	heartbeatIdCopy0 := heartbeatId
	heartbeatIdCopy = heartbeatIdCopy0
	proposerIdCopy0 := proposerId
	proposerIdCopy = proposerIdCopy0
	heartbeatIdCopy = self - 2*NUM_NODES
	proposerIdCopy = self - 5*NUM_NODES
	heartbeatId = heartbeatIdCopy
	proposerId = proposerIdCopy

	// kvLoop:
kvLoop:
	acquiredResources = map[string]map[uint64]interface{}{}
	counterCopy0 := counter
	counterCopy = counterCopy0
	msgCopy0 := make(map[string]interface{}, len(msg))
	for k, v := range msg {
		vCopy := v
		msgCopy0[k] = vCopy
	}
	msgCopy = msgCopy0
	proposalCopy0 := make(map[string]interface{}, len(proposal))
	for k, v := range proposal {
		vCopy := v
		proposalCopy0[k] = vCopy
	}
	proposalCopy = proposalCopy0
	heartbeatIdCopy1 := heartbeatId
	heartbeatIdCopy = heartbeatIdCopy1
	requestIdCopy0 := make([]int, len(requestId))
	for i, e := range requestId {
		eCopy := e
		requestIdCopy0[i] = eCopy
	}
	requestIdCopy = requestIdCopy0
	proposerIdCopy1 := proposerId
	proposerIdCopy = proposerIdCopy1
	err = distsys.AcquireResources(distsys.READ_ACCESS, requests)
	if err != nil {
		if shouldRetry(err) {
			goto kvLoop
		} else {
			return err
		}
	}
	for {
		if !true {
			err = distsys.ReleaseResources(requests)
			if err != nil {
				distsys.AbortResources(requests)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["proposerChan"] {
					distsys.AbortResources(proposerChan.Get(r))
				}
				return err
			}
			for _, r := range acquiredResources["iAmTheLeader"] {
				err = distsys.ReleaseResources(iAmTheLeader.Get(r))
				if err != nil {
					distsys.AbortResources(requests)
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["proposerChan"] {
						distsys.AbortResources(proposerChan.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["proposerChan"] {
				err = distsys.ReleaseResources(proposerChan.Get(r))
				if err != nil {
					distsys.AbortResources(requests)
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["proposerChan"] {
						distsys.AbortResources(proposerChan.Get(r0))
					}
					return err
				}
			}
			counter = counterCopy
			msg = msgCopy
			proposal = proposalCopy
			heartbeatId = heartbeatIdCopy
			requestId = requestIdCopy
			proposerId = proposerIdCopy
			break
		}
		var readTemp interface{}
		readTemp, err = requests.Read()
		if err != nil {
			distsys.AbortResources(requests)
			for _, r := range acquiredResources["iAmTheLeader"] {
				distsys.AbortResources(iAmTheLeader.Get(r))
			}
			for _, r := range acquiredResources["proposerChan"] {
				distsys.AbortResources(proposerChan.Get(r))
			}
			if shouldRetry(err) {
				goto kvLoop
			} else {
				return err
			}
		}
		msgCopy = readTemp.(map[string]interface{})
		if !(reflect.DeepEqual(msgCopy["type"], GET_MSG()) || reflect.DeepEqual(msgCopy["type"], PUT_MSG())) {
			panic("(((msg).type) = (GET_MSG)) \\/ (((msg).type) = (PUT_MSG))")
		}
		if _, ok := acquiredResources["iAmTheLeader"]; !ok {
			acquiredResources["iAmTheLeader"] = map[uint64]interface{}{}
		}
		resourceHash := distsys.Hash(heartbeatIdCopy)
		if _, acquired := acquiredResources["iAmTheLeader"][resourceHash]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, iAmTheLeader.Get(heartbeatIdCopy))
			if err != nil {
				distsys.AbortResources(requests)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["proposerChan"] {
					distsys.AbortResources(proposerChan.Get(r))
				}
				if shouldRetry(err) {
					goto kvLoop
				} else {
					return err
				}
			}
			acquiredResources["iAmTheLeader"][resourceHash] = heartbeatIdCopy
		}
		var readTemp0 interface{}
		readTemp0, err = iAmTheLeader.Get(heartbeatIdCopy).Read()
		if err != nil {
			distsys.AbortResources(requests)
			for _, r := range acquiredResources["iAmTheLeader"] {
				distsys.AbortResources(iAmTheLeader.Get(r))
			}
			for _, r := range acquiredResources["proposerChan"] {
				distsys.AbortResources(proposerChan.Get(r))
			}
			if shouldRetry(err) {
				goto kvLoop
			} else {
				return err
			}
		}
		if readTemp0.(bool) {
			requestIdCopy = []int{self, counterCopy}
			if reflect.DeepEqual(msgCopy["type"], GET_MSG()) {
				proposalCopy = map[string]interface{}{
					"id":        requestIdCopy,
					"operation": GET(),
					"value":     msgCopy["key"],
					"key":       msgCopy["key"],
				}
			} else {
				proposalCopy = map[string]interface{}{
					"id":        requestIdCopy,
					"operation": PUT(),
					"value":     msgCopy["value"],
					"key":       msgCopy["key"],
				}
			}
			if _, ok := acquiredResources["proposerChan"]; !ok {
				acquiredResources["proposerChan"] = map[uint64]interface{}{}
			}
			resourceHash0 := distsys.Hash(proposerIdCopy)
			if _, acquired := acquiredResources["proposerChan"][resourceHash0]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, proposerChan.Get(proposerIdCopy))
				if err != nil {
					distsys.AbortResources(requests)
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["proposerChan"] {
						distsys.AbortResources(proposerChan.Get(r))
					}
					if shouldRetry(err) {
						goto kvLoop
					} else {
						return err
					}
				}
				acquiredResources["proposerChan"][resourceHash0] = proposerIdCopy
			}
			var resourceWrite interface{}
			resourceWrite = proposalCopy
			err = proposerChan.Get(proposerIdCopy).Write(resourceWrite)
			if err != nil {
				distsys.AbortResources(requests)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["proposerChan"] {
					distsys.AbortResources(proposerChan.Get(r))
				}
				if shouldRetry(err) {
					goto kvLoop
				} else {
					return err
				}
			}

			// requestConfirm:
			err = distsys.ReleaseResources(requests)
			if err != nil {
				distsys.AbortResources(requests)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["proposerChan"] {
					distsys.AbortResources(proposerChan.Get(r))
				}
				return err
			}
			for _, r := range acquiredResources["iAmTheLeader"] {
				err = distsys.ReleaseResources(iAmTheLeader.Get(r))
				if err != nil {
					distsys.AbortResources(requests)
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["proposerChan"] {
						distsys.AbortResources(proposerChan.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["proposerChan"] {
				err = distsys.ReleaseResources(proposerChan.Get(r))
				if err != nil {
					distsys.AbortResources(requests)
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["proposerChan"] {
						distsys.AbortResources(proposerChan.Get(r0))
					}
					return err
				}
			}
			counter = counterCopy
			msg = msgCopy
			proposal = proposalCopy
			heartbeatId = heartbeatIdCopy
			requestId = requestIdCopy
			proposerId = proposerIdCopy
		requestConfirm:
			acquiredResources = map[string]map[uint64]interface{}{}
			counterCopy1 := counter
			counterCopy = counterCopy1
			resultCopy0 := result
			resultCopy = resultCopy0
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, upstream)
			if err != nil {
				if shouldRetry(err) {
					goto requestConfirm
				} else {
					return err
				}
			}
			if _, ok := acquiredResources["paxosChan"]; !ok {
				acquiredResources["paxosChan"] = map[uint64]interface{}{}
			}
			resourceHash1 := distsys.Hash(self)
			if _, acquired := acquiredResources["paxosChan"][resourceHash1]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, paxosChan.Get(self))
				if err != nil {
					distsys.AbortResources(upstream)
					for _, r := range acquiredResources["paxosChan"] {
						distsys.AbortResources(paxosChan.Get(r))
					}
					if shouldRetry(err) {
						goto requestConfirm
					} else {
						return err
					}
				}
				acquiredResources["paxosChan"][resourceHash1] = self
			}
			var readTemp1 interface{}
			readTemp1, err = paxosChan.Get(self).Read()
			if err != nil {
				distsys.AbortResources(upstream)
				for _, r := range acquiredResources["paxosChan"] {
					distsys.AbortResources(paxosChan.Get(r))
				}
				if shouldRetry(err) {
					goto requestConfirm
				} else {
					return err
				}
			}
			resultCopy = readTemp1
			var resourceWrite0 interface{}
			resourceWrite0 = map[string]interface{}{
				"result": resultCopy,
				"type":   OK_MSG(),
			}
			err = upstream.Write(resourceWrite0)
			if err != nil {
				distsys.AbortResources(upstream)
				for _, r := range acquiredResources["paxosChan"] {
					distsys.AbortResources(paxosChan.Get(r))
				}
				if shouldRetry(err) {
					goto requestConfirm
				} else {
					return err
				}
			}
			counterCopy = counterCopy + 1
			err = distsys.ReleaseResources(upstream)
			if err != nil {
				distsys.AbortResources(upstream)
				for _, r := range acquiredResources["paxosChan"] {
					distsys.AbortResources(paxosChan.Get(r))
				}
				return err
			}
			for _, r := range acquiredResources["paxosChan"] {
				err = distsys.ReleaseResources(paxosChan.Get(r))
				if err != nil {
					distsys.AbortResources(upstream)
					for _, r0 := range acquiredResources["paxosChan"] {
						distsys.AbortResources(paxosChan.Get(r0))
					}
					return err
				}
			}
			counter = counterCopy
			result = resultCopy
		} else {

			// notLeader:
			err = distsys.ReleaseResources(requests)
			if err != nil {
				distsys.AbortResources(upstream)
				for _, r := range acquiredResources["paxosChan"] {
					distsys.AbortResources(paxosChan.Get(r))
				}
				return err
			}
			for _, r := range acquiredResources["iAmTheLeader"] {
				err = distsys.ReleaseResources(iAmTheLeader.Get(r))
				if err != nil {
					distsys.AbortResources(upstream)
					for _, r0 := range acquiredResources["paxosChan"] {
						distsys.AbortResources(paxosChan.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["proposerChan"] {
				err = distsys.ReleaseResources(proposerChan.Get(r))
				if err != nil {
					distsys.AbortResources(upstream)
					for _, r0 := range acquiredResources["paxosChan"] {
						distsys.AbortResources(paxosChan.Get(r0))
					}
					return err
				}
			}
			counter = counterCopy
			msg = msgCopy
			proposal = proposalCopy
			heartbeatId = heartbeatIdCopy
			requestId = requestIdCopy
			proposerId = proposerIdCopy
		notLeader:
			acquiredResources = map[string]map[uint64]interface{}{}
			nullCopy0 := null
			nullCopy = nullCopy0
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, upstream)
			if err != nil {
				if shouldRetry(err) {
					goto notLeader
				} else {
					return err
				}
			}
			var resourceWrite interface{}
			resourceWrite = map[string]interface{}{
				"result": nullCopy,
				"type":   NOT_LEADER_MSG(),
			}
			err = upstream.Write(resourceWrite)
			if err != nil {
				distsys.AbortResources(upstream)
				if shouldRetry(err) {
					goto notLeader
				} else {
					return err
				}
			}
			err = distsys.ReleaseResources(upstream)
			if err != nil {
				distsys.AbortResources(upstream)
				return err
			}
			null = nullCopy
		}
		acquiredResources = map[string]map[uint64]interface{}{}
		counterCopy1 := counter
		counterCopy = counterCopy1
		msgCopy1 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy1[k] = vCopy
		}
		msgCopy = msgCopy1
		proposalCopy1 := make(map[string]interface{}, len(proposal))
		for k, v := range proposal {
			vCopy := v
			proposalCopy1[k] = vCopy
		}
		proposalCopy = proposalCopy1
		heartbeatIdCopy2 := heartbeatId
		heartbeatIdCopy = heartbeatIdCopy2
		requestIdCopy1 := make([]int, len(requestId))
		for i, e := range requestId {
			eCopy := e
			requestIdCopy1[i] = eCopy
		}
		requestIdCopy = requestIdCopy1
		proposerIdCopy2 := proposerId
		proposerIdCopy = proposerIdCopy2
		err = distsys.AcquireResources(distsys.READ_ACCESS, requests)
		if err != nil {
			if shouldRetry(err) {
				goto kvLoop
			} else {
				return err
			}
		}
	}
	return nil
}

func KeyValuePaxosManager(self int, requestService distsys.ArchetypeResourceCollection, learnerChan distsys.ArchetypeResourceCollection, db distsys.ArchetypeResourceCollection) error {
	var result interface{}
	var learnerId int
	var decided map[string]interface{}
	var kvId int
	var resultCopy interface{}
	var learnerIdCopy int
	var decidedCopy map[string]interface{}
	var kvIdCopy int
	var err error
	var acquiredResources map[string]map[uint64]interface{}

	// findId:
	acquiredResources = map[string]map[uint64]interface{}{}
	learnerIdCopy0 := learnerId
	learnerIdCopy = learnerIdCopy0
	kvIdCopy0 := kvId
	kvIdCopy = kvIdCopy0
	learnerIdCopy = self - 4*NUM_NODES
	kvIdCopy = self - NUM_NODES
	learnerId = learnerIdCopy
	kvId = kvIdCopy

	// kvManagerLoop:
kvManagerLoop:
	acquiredResources = map[string]map[uint64]interface{}{}
	decidedCopy0 := make(map[string]interface{}, len(decided))
	for k, v := range decided {
		vCopy := v
		decidedCopy0[k] = vCopy
	}
	decidedCopy = decidedCopy0
	learnerIdCopy1 := learnerId
	learnerIdCopy = learnerIdCopy1
	resultCopy0 := result
	resultCopy = resultCopy0
	kvIdCopy1 := kvId
	kvIdCopy = kvIdCopy1
	for {
		if !true {
			break
		}
		if _, ok := acquiredResources["learnerChan"]; !ok {
			acquiredResources["learnerChan"] = map[uint64]interface{}{}
		}
		resourceHash := distsys.Hash(learnerIdCopy)
		if _, acquired := acquiredResources["learnerChan"][resourceHash]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, learnerChan.Get(learnerIdCopy))
			if err != nil {
				for _, r := range acquiredResources["learnerChan"] {
					distsys.AbortResources(learnerChan.Get(r))
				}
				for _, r := range acquiredResources["requestService"] {
					distsys.AbortResources(requestService.Get(r))
				}
				for _, r := range acquiredResources["db"] {
					distsys.AbortResources(db.Get(r))
				}
				if shouldRetry(err) {
					goto kvManagerLoop
				} else {
					return err
				}
			}
			acquiredResources["learnerChan"][resourceHash] = learnerIdCopy
		}
		var readTemp interface{}
		readTemp, err = learnerChan.Get(learnerIdCopy).Read()
		if err != nil {
			for _, r := range acquiredResources["learnerChan"] {
				distsys.AbortResources(learnerChan.Get(r))
			}
			for _, r := range acquiredResources["requestService"] {
				distsys.AbortResources(requestService.Get(r))
			}
			for _, r := range acquiredResources["db"] {
				distsys.AbortResources(db.Get(r))
			}
			if shouldRetry(err) {
				goto kvManagerLoop
			} else {
				return err
			}
		}
		decidedCopy = readTemp.(map[string]interface{})
		if reflect.DeepEqual(decidedCopy["operation"], PUT()) {
			if _, ok := acquiredResources["db"]; !ok {
				acquiredResources["db"] = map[uint64]interface{}{}
			}
			resourceHash0 := distsys.Hash(decidedCopy["key"])
			if _, acquired := acquiredResources["db"][resourceHash0]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, db.Get(decidedCopy["key"]))
				if err != nil {
					for _, r := range acquiredResources["learnerChan"] {
						distsys.AbortResources(learnerChan.Get(r))
					}
					for _, r := range acquiredResources["requestService"] {
						distsys.AbortResources(requestService.Get(r))
					}
					for _, r := range acquiredResources["db"] {
						distsys.AbortResources(db.Get(r))
					}
					if shouldRetry(err) {
						goto kvManagerLoop
					} else {
						return err
					}
				}
				acquiredResources["db"][resourceHash0] = decidedCopy["key"]
			}
			var resourceWrite interface{}
			resourceWrite = decidedCopy["value"]
			err = db.Get(decidedCopy["key"]).Write(resourceWrite)
			if err != nil {
				for _, r := range acquiredResources["learnerChan"] {
					distsys.AbortResources(learnerChan.Get(r))
				}
				for _, r := range acquiredResources["requestService"] {
					distsys.AbortResources(requestService.Get(r))
				}
				for _, r := range acquiredResources["db"] {
					distsys.AbortResources(db.Get(r))
				}
				if shouldRetry(err) {
					goto kvManagerLoop
				} else {
					return err
				}
			}
		}
		if decidedCopy["id"].([]int)[1-1] == kvIdCopy {
			if reflect.DeepEqual(decidedCopy["operation"], GET()) {
				if _, ok := acquiredResources["db"]; !ok {
					acquiredResources["db"] = map[uint64]interface{}{}
				}
				resourceHash0 := distsys.Hash(decidedCopy["key"])
				if _, acquired := acquiredResources["db"][resourceHash0]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, db.Get(decidedCopy["key"]))
					if err != nil {
						for _, r := range acquiredResources["learnerChan"] {
							distsys.AbortResources(learnerChan.Get(r))
						}
						for _, r := range acquiredResources["requestService"] {
							distsys.AbortResources(requestService.Get(r))
						}
						for _, r := range acquiredResources["db"] {
							distsys.AbortResources(db.Get(r))
						}
						if shouldRetry(err) {
							goto kvManagerLoop
						} else {
							return err
						}
					}
					acquiredResources["db"][resourceHash0] = decidedCopy["key"]
				}
				var readTemp0 interface{}
				readTemp0, err = db.Get(decidedCopy["key"]).Read()
				if err != nil {
					for _, r := range acquiredResources["learnerChan"] {
						distsys.AbortResources(learnerChan.Get(r))
					}
					for _, r := range acquiredResources["requestService"] {
						distsys.AbortResources(requestService.Get(r))
					}
					for _, r := range acquiredResources["db"] {
						distsys.AbortResources(db.Get(r))
					}
					if shouldRetry(err) {
						goto kvManagerLoop
					} else {
						return err
					}
				}
				resultCopy = readTemp0
			} else {
				resultCopy = decidedCopy["value"]
			}
			if _, ok := acquiredResources["requestService"]; !ok {
				acquiredResources["requestService"] = map[uint64]interface{}{}
			}
			resourceHash0 := distsys.Hash(kvIdCopy)
			if _, acquired := acquiredResources["requestService"][resourceHash0]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, requestService.Get(kvIdCopy))
				if err != nil {
					for _, r := range acquiredResources["learnerChan"] {
						distsys.AbortResources(learnerChan.Get(r))
					}
					for _, r := range acquiredResources["requestService"] {
						distsys.AbortResources(requestService.Get(r))
					}
					for _, r := range acquiredResources["db"] {
						distsys.AbortResources(db.Get(r))
					}
					if shouldRetry(err) {
						goto kvManagerLoop
					} else {
						return err
					}
				}
				acquiredResources["requestService"][resourceHash0] = kvIdCopy
			}
			var resourceWrite interface{}
			resourceWrite = resultCopy
			err = requestService.Get(kvIdCopy).Write(resourceWrite)
			if err != nil {
				for _, r := range acquiredResources["learnerChan"] {
					distsys.AbortResources(learnerChan.Get(r))
				}
				for _, r := range acquiredResources["requestService"] {
					distsys.AbortResources(requestService.Get(r))
				}
				for _, r := range acquiredResources["db"] {
					distsys.AbortResources(db.Get(r))
				}
				if shouldRetry(err) {
					goto kvManagerLoop
				} else {
					return err
				}
			}
		}
		for _, r := range acquiredResources["learnerChan"] {
			err = distsys.ReleaseResources(learnerChan.Get(r))
			if err != nil {
				for _, r0 := range acquiredResources["learnerChan"] {
					distsys.AbortResources(learnerChan.Get(r0))
				}
				for _, r0 := range acquiredResources["requestService"] {
					distsys.AbortResources(requestService.Get(r0))
				}
				for _, r0 := range acquiredResources["db"] {
					distsys.AbortResources(db.Get(r0))
				}
				return err
			}
		}
		for _, r := range acquiredResources["requestService"] {
			err = distsys.ReleaseResources(requestService.Get(r))
			if err != nil {
				for _, r0 := range acquiredResources["learnerChan"] {
					distsys.AbortResources(learnerChan.Get(r0))
				}
				for _, r0 := range acquiredResources["requestService"] {
					distsys.AbortResources(requestService.Get(r0))
				}
				for _, r0 := range acquiredResources["db"] {
					distsys.AbortResources(db.Get(r0))
				}
				return err
			}
		}
		for _, r := range acquiredResources["db"] {
			err = distsys.ReleaseResources(db.Get(r))
			if err != nil {
				for _, r0 := range acquiredResources["learnerChan"] {
					distsys.AbortResources(learnerChan.Get(r0))
				}
				for _, r0 := range acquiredResources["requestService"] {
					distsys.AbortResources(requestService.Get(r0))
				}
				for _, r0 := range acquiredResources["db"] {
					distsys.AbortResources(db.Get(r0))
				}
				return err
			}
		}
		decided = decidedCopy
		learnerId = learnerIdCopy
		result = resultCopy
		kvId = kvIdCopy
		acquiredResources = map[string]map[uint64]interface{}{}
		decidedCopy1 := make(map[string]interface{}, len(decided))
		for k, v := range decided {
			vCopy := v
			decidedCopy1[k] = vCopy
		}
		decidedCopy = decidedCopy1
		learnerIdCopy2 := learnerId
		learnerIdCopy = learnerIdCopy2
		resultCopy1 := result
		resultCopy = resultCopy1
		kvIdCopy2 := kvId
		kvIdCopy = kvIdCopy2
	}
	for _, r := range acquiredResources["learnerChan"] {
		err = distsys.ReleaseResources(learnerChan.Get(r))
		if err != nil {
			for _, r0 := range acquiredResources["learnerChan"] {
				distsys.AbortResources(learnerChan.Get(r0))
			}
			for _, r0 := range acquiredResources["requestService"] {
				distsys.AbortResources(requestService.Get(r0))
			}
			for _, r0 := range acquiredResources["db"] {
				distsys.AbortResources(db.Get(r0))
			}
			return err
		}
	}
	for _, r := range acquiredResources["requestService"] {
		err = distsys.ReleaseResources(requestService.Get(r))
		if err != nil {
			for _, r0 := range acquiredResources["learnerChan"] {
				distsys.AbortResources(learnerChan.Get(r0))
			}
			for _, r0 := range acquiredResources["requestService"] {
				distsys.AbortResources(requestService.Get(r0))
			}
			for _, r0 := range acquiredResources["db"] {
				distsys.AbortResources(db.Get(r0))
			}
			return err
		}
	}
	for _, r := range acquiredResources["db"] {
		err = distsys.ReleaseResources(db.Get(r))
		if err != nil {
			for _, r0 := range acquiredResources["learnerChan"] {
				distsys.AbortResources(learnerChan.Get(r0))
			}
			for _, r0 := range acquiredResources["requestService"] {
				distsys.AbortResources(requestService.Get(r0))
			}
			for _, r0 := range acquiredResources["db"] {
				distsys.AbortResources(db.Get(r0))
			}
			return err
		}
	}
	decided = decidedCopy
	learnerId = learnerIdCopy
	result = resultCopy
	kvId = kvIdCopy
	return nil
}
