package paxos

import (
	"fmt"
	"math/rand"
	"pgo/distsys"
	"reflect"
	"time"
)

var sleepMin = 100

var sleepMax = 300

var NULL int

var NUM_NODES int

func init() {
	NULL = -1
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

func ACCEPT_MSG() string {
	return "accept_msg"
}

func Acceptor() []int {
	tmpRange := make([]int, 2*NUM_NODES-1-NUM_NODES+1)
	for i := NUM_NODES; i <= 2*NUM_NODES-1; i++ {
		tmpRange[i-NUM_NODES] = i
	}
	return tmpRange
}

func ALearner(self int, mailboxes distsys.ArchetypeResourceCollection, decided distsys.ArchetypeResourceCollection) error {
	accepts := []map[string]interface{}{}
	var newAccepts []map[string]interface{}
	var numAccepted int
	var iterator int
	var entry map[string]interface{}
	var msg map[string]interface{}
	var acceptsCopy []map[string]interface{}
	var newAcceptsCopy []map[string]interface{}
	var numAcceptedCopy int
	var iteratorCopy int
	var entryCopy map[string]interface{}
	var msgCopy map[string]interface{}
	var err error
	var acquiredResources map[string]map[uint64]interface{}

	// L:
L:
	acquiredResources = map[string]map[uint64]interface{}{}
	msgCopy0 := make(map[string]interface{}, len(msg))
	for k, v := range msg {
		vCopy := v
		msgCopy0[k] = vCopy
	}
	msgCopy = msgCopy0
	for {
		if !true {
			for _, r := range acquiredResources["mailboxes"] {
				err = distsys.ReleaseResources(mailboxes.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			msg = msgCopy
			break
		}
		if _, ok := acquiredResources["mailboxes"]; !ok {
			acquiredResources["mailboxes"] = map[uint64]interface{}{}
		}
		resourceHash := distsys.Hash(self)
		if _, acquired := acquiredResources["mailboxes"][resourceHash]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(self))
			if err != nil {
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto L
				} else {
					return err
				}
			}
			acquiredResources["mailboxes"][resourceHash] = self
		}
		var readTemp interface{}
		readTemp, err = mailboxes.Get(self).Read()
		if err != nil {
			for _, r := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			if shouldRetry(err) {
				goto L
			} else {
				return err
			}
		}
		msgCopy = readTemp.(map[string]interface{})

		// LGotAcc:
		for _, r := range acquiredResources["mailboxes"] {
			err = distsys.ReleaseResources(mailboxes.Get(r))
			if err != nil {
				for _, r0 := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		msg = msgCopy
		acquiredResources = map[string]map[uint64]interface{}{}
		acceptsCopy0 := make([]map[string]interface{}, len(accepts))
		for i, e := range accepts {
			eCopy := make(map[string]interface{}, len(e))
			for k, v := range e {
				vCopy := v
				eCopy[k] = vCopy
			}
			acceptsCopy0[i] = eCopy
		}
		acceptsCopy = acceptsCopy0
		iteratorCopy0 := iterator
		iteratorCopy = iteratorCopy0
		numAcceptedCopy0 := numAccepted
		numAcceptedCopy = numAcceptedCopy0
		msgCopy1 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy1[k] = vCopy
		}
		msgCopy = msgCopy1
		if reflect.DeepEqual(msgCopy["type"], ACCEPT_MSG()) {
			tmpSlice := make([]map[string]interface{}, len(acceptsCopy), len(acceptsCopy)+1)
			copy(tmpSlice, acceptsCopy)
			tmpSlice = append(tmpSlice, msgCopy)
			acceptsCopy = tmpSlice
			iteratorCopy = 1
			numAcceptedCopy = 0

			// LCheckMajority:
			accepts = acceptsCopy
			iterator = iteratorCopy
			numAccepted = numAcceptedCopy
			msg = msgCopy
		LCheckMajority:
			acquiredResources = map[string]map[uint64]interface{}{}
			entryCopy0 := make(map[string]interface{}, len(entry))
			for k, v := range entry {
				vCopy := v
				entryCopy0[k] = vCopy
			}
			entryCopy = entryCopy0
			acceptsCopy1 := make([]map[string]interface{}, len(accepts))
			for i, e := range accepts {
				eCopy := make(map[string]interface{}, len(e))
				for k, v := range e {
					vCopy := v
					eCopy[k] = vCopy
				}
				acceptsCopy1[i] = eCopy
			}
			acceptsCopy = acceptsCopy1
			iteratorCopy1 := iterator
			iteratorCopy = iteratorCopy1
			newAcceptsCopy0 := make([]map[string]interface{}, len(newAccepts))
			for i, e := range newAccepts {
				eCopy := make(map[string]interface{}, len(e))
				for k, v := range e {
					vCopy := v
					eCopy[k] = vCopy
				}
				newAcceptsCopy0[i] = eCopy
			}
			newAcceptsCopy = newAcceptsCopy0
			numAcceptedCopy1 := numAccepted
			numAcceptedCopy = numAcceptedCopy1
			msgCopy2 := make(map[string]interface{}, len(msg))
			for k, v := range msg {
				vCopy := v
				msgCopy2[k] = vCopy
			}
			msgCopy = msgCopy2
			for {
				if !(iteratorCopy <= len(acceptsCopy)) {
					break
				}
				entryCopy = acceptsCopy[iteratorCopy-1]
				if reflect.DeepEqual(entryCopy["slot"], msgCopy["slot"]) && reflect.DeepEqual(entryCopy["bal"], msgCopy["bal"]) && reflect.DeepEqual(entryCopy["val"], msgCopy["val"]) {
					numAcceptedCopy = numAcceptedCopy + 1
				}
				iteratorCopy = iteratorCopy + 1
				for _, r := range acquiredResources["decided"] {
					err = distsys.ReleaseResources(decided.Get(r))
					if err != nil {
						for _, r0 := range acquiredResources["decided"] {
							distsys.AbortResources(decided.Get(r0))
						}
						return err
					}
				}
				entry = entryCopy
				accepts = acceptsCopy
				iterator = iteratorCopy
				newAccepts = newAcceptsCopy
				numAccepted = numAcceptedCopy
				msg = msgCopy
				acquiredResources = map[string]map[uint64]interface{}{}
				entryCopy1 := make(map[string]interface{}, len(entry))
				for k, v := range entry {
					vCopy := v
					entryCopy1[k] = vCopy
				}
				entryCopy = entryCopy1
				acceptsCopy2 := make([]map[string]interface{}, len(accepts))
				for i, e := range accepts {
					eCopy := make(map[string]interface{}, len(e))
					for k, v := range e {
						vCopy := v
						eCopy[k] = vCopy
					}
					acceptsCopy2[i] = eCopy
				}
				acceptsCopy = acceptsCopy2
				iteratorCopy2 := iterator
				iteratorCopy = iteratorCopy2
				newAcceptsCopy1 := make([]map[string]interface{}, len(newAccepts))
				for i, e := range newAccepts {
					eCopy := make(map[string]interface{}, len(e))
					for k, v := range e {
						vCopy := v
						eCopy[k] = vCopy
					}
					newAcceptsCopy1[i] = eCopy
				}
				newAcceptsCopy = newAcceptsCopy1
				numAcceptedCopy2 := numAccepted
				numAcceptedCopy = numAcceptedCopy2
				msgCopy3 := make(map[string]interface{}, len(msg))
				for k, v := range msg {
					vCopy := v
					msgCopy3[k] = vCopy
				}
				msgCopy = msgCopy3
			}
			if numAcceptedCopy*2 > len(Acceptor()) {
				if _, ok := acquiredResources["decided"]; !ok {
					acquiredResources["decided"] = map[uint64]interface{}{}
				}
				resourceHash0 := distsys.Hash(self)
				if _, acquired := acquiredResources["decided"][resourceHash0]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, decided.Get(self))
					if err != nil {
						for _, r := range acquiredResources["decided"] {
							distsys.AbortResources(decided.Get(r))
						}
						if shouldRetry(err) {
							goto LCheckMajority
						} else {
							return err
						}
					}
					acquiredResources["decided"][resourceHash0] = self
				}
				var resourceWrite interface{}
				resourceWrite = msgCopy["val"]
				err = decided.Get(self).Write(resourceWrite)
				if err != nil {
					for _, r := range acquiredResources["decided"] {
						distsys.AbortResources(decided.Get(r))
					}
					if shouldRetry(err) {
						goto LCheckMajority
					} else {
						return err
					}
				}
				newAcceptsCopy = []map[string]interface{}{}
				iteratorCopy = 1

				// garbageCollection:
				for _, r := range acquiredResources["decided"] {
					err = distsys.ReleaseResources(decided.Get(r))
					if err != nil {
						for _, r0 := range acquiredResources["decided"] {
							distsys.AbortResources(decided.Get(r0))
						}
						return err
					}
				}
				entry = entryCopy
				accepts = acceptsCopy
				iterator = iteratorCopy
				newAccepts = newAcceptsCopy
				numAccepted = numAcceptedCopy
				msg = msgCopy
				acquiredResources = map[string]map[uint64]interface{}{}
				entryCopy1 := make(map[string]interface{}, len(entry))
				for k, v := range entry {
					vCopy := v
					entryCopy1[k] = vCopy
				}
				entryCopy = entryCopy1
				acceptsCopy2 := make([]map[string]interface{}, len(accepts))
				for i, e := range accepts {
					eCopy := make(map[string]interface{}, len(e))
					for k, v := range e {
						vCopy := v
						eCopy[k] = vCopy
					}
					acceptsCopy2[i] = eCopy
				}
				acceptsCopy = acceptsCopy2
				iteratorCopy2 := iterator
				iteratorCopy = iteratorCopy2
				newAcceptsCopy1 := make([]map[string]interface{}, len(newAccepts))
				for i, e := range newAccepts {
					eCopy := make(map[string]interface{}, len(e))
					for k, v := range e {
						vCopy := v
						eCopy[k] = vCopy
					}
					newAcceptsCopy1[i] = eCopy
				}
				newAcceptsCopy = newAcceptsCopy1
				msgCopy3 := make(map[string]interface{}, len(msg))
				for k, v := range msg {
					vCopy := v
					msgCopy3[k] = vCopy
				}
				msgCopy = msgCopy3
				for {
					if !(iteratorCopy <= len(acceptsCopy)) {
						break
					}
					entryCopy = acceptsCopy[iteratorCopy-1]
					if !reflect.DeepEqual(entryCopy["slot"], msgCopy["slot"]) {
						tmpSlice0 := make([]map[string]interface{}, len(newAcceptsCopy), len(newAcceptsCopy)+1)
						copy(tmpSlice0, newAcceptsCopy)
						tmpSlice0 = append(tmpSlice0, entryCopy)
						newAcceptsCopy = tmpSlice0
					}
					iteratorCopy = iteratorCopy + 1
					entry = entryCopy
					accepts = acceptsCopy
					iterator = iteratorCopy
					newAccepts = newAcceptsCopy
					msg = msgCopy
					acquiredResources = map[string]map[uint64]interface{}{}
					entryCopy2 := make(map[string]interface{}, len(entry))
					for k, v := range entry {
						vCopy := v
						entryCopy2[k] = vCopy
					}
					entryCopy = entryCopy2
					acceptsCopy3 := make([]map[string]interface{}, len(accepts))
					for i, e := range accepts {
						eCopy := make(map[string]interface{}, len(e))
						for k, v := range e {
							vCopy := v
							eCopy[k] = vCopy
						}
						acceptsCopy3[i] = eCopy
					}
					acceptsCopy = acceptsCopy3
					iteratorCopy3 := iterator
					iteratorCopy = iteratorCopy3
					newAcceptsCopy2 := make([]map[string]interface{}, len(newAccepts))
					for i, e := range newAccepts {
						eCopy := make(map[string]interface{}, len(e))
						for k, v := range e {
							vCopy := v
							eCopy[k] = vCopy
						}
						newAcceptsCopy2[i] = eCopy
					}
					newAcceptsCopy = newAcceptsCopy2
					msgCopy4 := make(map[string]interface{}, len(msg))
					for k, v := range msg {
						vCopy := v
						msgCopy4[k] = vCopy
					}
					msgCopy = msgCopy4
				}
				acceptsCopy = newAcceptsCopy
				entry = entryCopy
				accepts = acceptsCopy
				iterator = iteratorCopy
				newAccepts = newAcceptsCopy
				msg = msgCopy
			} else {
				for _, r := range acquiredResources["decided"] {
					err = distsys.ReleaseResources(decided.Get(r))
					if err != nil {
						return err
					}
				}
				entry = entryCopy
				accepts = acceptsCopy
				iterator = iteratorCopy
				newAccepts = newAcceptsCopy
				numAccepted = numAcceptedCopy
				msg = msgCopy
			}
		} else {
			accepts = acceptsCopy
			iterator = iteratorCopy
			numAccepted = numAcceptedCopy
			msg = msgCopy
		}
		acquiredResources = map[string]map[uint64]interface{}{}
		msgCopy2 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy2[k] = vCopy
		}
		msgCopy = msgCopy2
	}
	return nil
}

func PREPARE_MSG() string {
	return "prepare_msg"
}

func PROMISE_MSG() string {
	return "promise_msg"
}

func REJECT_MSG() string {
	return "reject_msg"
}

func PROPOSE_MSG() string {
	return "propose_msg"
}

func AAcceptor(self int, mailboxes distsys.ArchetypeResourceCollection) error {
	maxBal := -1
	var loopIndex int
	acceptedValues := []map[string]interface{}{}
	var payload map[string]interface{}
	var msg map[string]interface{}
	var maxBalCopy int
	var loopIndexCopy int
	var acceptedValuesCopy []map[string]interface{}
	var payloadCopy map[string]interface{}
	var msgCopy map[string]interface{}
	var err error
	var acquiredResources map[string]map[uint64]interface{}

	// A:
A:
	acquiredResources = map[string]map[uint64]interface{}{}
	msgCopy0 := make(map[string]interface{}, len(msg))
	for k, v := range msg {
		vCopy := v
		msgCopy0[k] = vCopy
	}
	msgCopy = msgCopy0
	for {
		if !true {
			for _, r := range acquiredResources["mailboxes"] {
				err = distsys.ReleaseResources(mailboxes.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			msg = msgCopy
			break
		}
		if _, ok := acquiredResources["mailboxes"]; !ok {
			acquiredResources["mailboxes"] = map[uint64]interface{}{}
		}
		resourceHash := distsys.Hash(self)
		if _, acquired := acquiredResources["mailboxes"][resourceHash]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(self))
			if err != nil {
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto A
				} else {
					return err
				}
			}
			acquiredResources["mailboxes"][resourceHash] = self
		}
		var readTemp interface{}
		readTemp, err = mailboxes.Get(self).Read()
		if err != nil {
			for _, r := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			if shouldRetry(err) {
				goto A
			} else {
				return err
			}
		}
		msgCopy = readTemp.(map[string]interface{})

		// AMsgSwitch:
		for _, r := range acquiredResources["mailboxes"] {
			err = distsys.ReleaseResources(mailboxes.Get(r))
			if err != nil {
				for _, r0 := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		msg = msgCopy
		acquiredResources = map[string]map[uint64]interface{}{}
		msgCopy1 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy1[k] = vCopy
		}
		msgCopy = msgCopy1
		maxBalCopy0 := maxBal
		maxBalCopy = maxBalCopy0
		if reflect.DeepEqual(msgCopy["type"], PREPARE_MSG()) && msgCopy["bal"].(int) > maxBalCopy {

			// APrepare:
			msg = msgCopy
			maxBal = maxBalCopy
		APrepare:
			acquiredResources = map[string]map[uint64]interface{}{}
			msgCopy2 := make(map[string]interface{}, len(msg))
			for k, v := range msg {
				vCopy := v
				msgCopy2[k] = vCopy
			}
			msgCopy = msgCopy2
			maxBalCopy1 := maxBal
			maxBalCopy = maxBalCopy1
			acceptedValuesCopy0 := make([]map[string]interface{}, len(acceptedValues))
			for i, e := range acceptedValues {
				eCopy := make(map[string]interface{}, len(e))
				for k, v := range e {
					vCopy := v
					eCopy[k] = vCopy
				}
				acceptedValuesCopy0[i] = eCopy
			}
			acceptedValuesCopy = acceptedValuesCopy0
			maxBalCopy = msgCopy["bal"].(int)
			if _, ok := acquiredResources["mailboxes"]; !ok {
				acquiredResources["mailboxes"] = map[uint64]interface{}{}
			}
			resourceHash0 := distsys.Hash(msgCopy["sender"].(int))
			if _, acquired := acquiredResources["mailboxes"][resourceHash0]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(msgCopy["sender"].(int)))
				if err != nil {
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto APrepare
					} else {
						return err
					}
				}
				acquiredResources["mailboxes"][resourceHash0] = msgCopy["sender"].(int)
			}
			var resourceWrite interface{}
			resourceWrite = map[string]interface{}{
				"val":      msgCopy["val"],
				"sender":   self,
				"slot":     NULL,
				"accepted": acceptedValuesCopy,
				"bal":      maxBalCopy,
				"type":     PROMISE_MSG(),
			}
			err = mailboxes.Get(msgCopy["sender"].(int)).Write(resourceWrite)
			if err != nil {
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto APrepare
				} else {
					return err
				}
			}
			for _, r := range acquiredResources["mailboxes"] {
				err = distsys.ReleaseResources(mailboxes.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			msg = msgCopy
			maxBal = maxBalCopy
			acceptedValues = acceptedValuesCopy
		} else {
			if reflect.DeepEqual(msgCopy["type"], PREPARE_MSG()) && msgCopy["bal"].(int) <= maxBalCopy {

				// ABadPrepare:
				msg = msgCopy
				maxBal = maxBalCopy
			ABadPrepare:
				acquiredResources = map[string]map[uint64]interface{}{}
				msgCopy2 := make(map[string]interface{}, len(msg))
				for k, v := range msg {
					vCopy := v
					msgCopy2[k] = vCopy
				}
				msgCopy = msgCopy2
				maxBalCopy1 := maxBal
				maxBalCopy = maxBalCopy1
				if _, ok := acquiredResources["mailboxes"]; !ok {
					acquiredResources["mailboxes"] = map[uint64]interface{}{}
				}
				resourceHash0 := distsys.Hash(msgCopy["sender"].(int))
				if _, acquired := acquiredResources["mailboxes"][resourceHash0]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(msgCopy["sender"].(int)))
					if err != nil {
						for _, r := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r))
						}
						if shouldRetry(err) {
							goto ABadPrepare
						} else {
							return err
						}
					}
					acquiredResources["mailboxes"][resourceHash0] = msgCopy["sender"].(int)
				}
				var resourceWrite interface{}
				resourceWrite = map[string]interface{}{
					"val":      msgCopy["val"],
					"sender":   self,
					"slot":     NULL,
					"accepted": []map[string]interface{}{},
					"bal":      maxBalCopy,
					"type":     REJECT_MSG(),
				}
				err = mailboxes.Get(msgCopy["sender"].(int)).Write(resourceWrite)
				if err != nil {
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto ABadPrepare
					} else {
						return err
					}
				}
				for _, r := range acquiredResources["mailboxes"] {
					err = distsys.ReleaseResources(mailboxes.Get(r))
					if err != nil {
						for _, r0 := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r0))
						}
						return err
					}
				}
				msg = msgCopy
				maxBal = maxBalCopy
			} else {
				if reflect.DeepEqual(msgCopy["type"], PROPOSE_MSG()) && msgCopy["bal"].(int) >= maxBalCopy {

					// APropose:
					msg = msgCopy
					maxBal = maxBalCopy
				APropose:
					acquiredResources = map[string]map[uint64]interface{}{}
					payloadCopy0 := make(map[string]interface{}, len(payload))
					for k, v := range payload {
						vCopy := v
						payloadCopy0[k] = vCopy
					}
					payloadCopy = payloadCopy0
					loopIndexCopy0 := loopIndex
					loopIndexCopy = loopIndexCopy0
					msgCopy2 := make(map[string]interface{}, len(msg))
					for k, v := range msg {
						vCopy := v
						msgCopy2[k] = vCopy
					}
					msgCopy = msgCopy2
					maxBalCopy1 := maxBal
					maxBalCopy = maxBalCopy1
					acceptedValuesCopy0 := make([]map[string]interface{}, len(acceptedValues))
					for i, e := range acceptedValues {
						eCopy := make(map[string]interface{}, len(e))
						for k, v := range e {
							vCopy := v
							eCopy[k] = vCopy
						}
						acceptedValuesCopy0[i] = eCopy
					}
					acceptedValuesCopy = acceptedValuesCopy0
					maxBalCopy = msgCopy["bal"].(int)
					payloadCopy = map[string]interface{}{
						"val":      msgCopy["val"],
						"sender":   self,
						"slot":     msgCopy["slot"].(int),
						"accepted": []map[string]interface{}{},
						"bal":      maxBalCopy,
						"type":     ACCEPT_MSG(),
					}
					tmpSlice := make([]map[string]interface{}, len(acceptedValuesCopy), len(acceptedValuesCopy)+1)
					copy(tmpSlice, acceptedValuesCopy)
					tmpSlice = append(tmpSlice, map[string]interface{}{
						"val":  msgCopy["val"],
						"slot": msgCopy["slot"].(int),
						"bal":  msgCopy["bal"].(int),
					})
					acceptedValuesCopy = tmpSlice
					if _, ok := acquiredResources["mailboxes"]; !ok {
						acquiredResources["mailboxes"] = map[uint64]interface{}{}
					}
					resourceHash0 := distsys.Hash(msgCopy["sender"].(int))
					if _, acquired := acquiredResources["mailboxes"][resourceHash0]; !acquired {
						err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(msgCopy["sender"].(int)))
						if err != nil {
							for _, r := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r))
							}
							if shouldRetry(err) {
								goto APropose
							} else {
								return err
							}
						}
						acquiredResources["mailboxes"][resourceHash0] = msgCopy["sender"].(int)
					}
					var resourceWrite interface{}
					resourceWrite = payloadCopy
					err = mailboxes.Get(msgCopy["sender"].(int)).Write(resourceWrite)
					if err != nil {
						for _, r := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r))
						}
						if shouldRetry(err) {
							goto APropose
						} else {
							return err
						}
					}
					loopIndexCopy = 2 * NUM_NODES
					for _, r := range acquiredResources["mailboxes"] {
						err = distsys.ReleaseResources(mailboxes.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					payload = payloadCopy
					loopIndex = loopIndexCopy
					msg = msgCopy
					maxBal = maxBalCopy
					acceptedValues = acceptedValuesCopy

					// ANotifyLearners:
				ANotifyLearners:
					acquiredResources = map[string]map[uint64]interface{}{}
					payloadCopy1 := make(map[string]interface{}, len(payload))
					for k, v := range payload {
						vCopy := v
						payloadCopy1[k] = vCopy
					}
					payloadCopy = payloadCopy1
					loopIndexCopy1 := loopIndex
					loopIndexCopy = loopIndexCopy1
					for {
						if !(loopIndexCopy <= 3*NUM_NODES-1) {
							break
						}
						if _, ok := acquiredResources["mailboxes"]; !ok {
							acquiredResources["mailboxes"] = map[uint64]interface{}{}
						}
						resourceHash1 := distsys.Hash(loopIndexCopy)
						if _, acquired := acquiredResources["mailboxes"][resourceHash1]; !acquired {
							err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(loopIndexCopy))
							if err != nil {
								for _, r := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r))
								}
								if shouldRetry(err) {
									goto ANotifyLearners
								} else {
									return err
								}
							}
							acquiredResources["mailboxes"][resourceHash1] = loopIndexCopy
						}
						var resourceWrite0 interface{}
						resourceWrite0 = payloadCopy
						err = mailboxes.Get(loopIndexCopy).Write(resourceWrite0)
						if err != nil {
							for _, r := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r))
							}
							if shouldRetry(err) {
								goto ANotifyLearners
							} else {
								return err
							}
						}
						loopIndexCopy = loopIndexCopy + 1
						for _, r := range acquiredResources["mailboxes"] {
							err = distsys.ReleaseResources(mailboxes.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						payload = payloadCopy
						loopIndex = loopIndexCopy
						acquiredResources = map[string]map[uint64]interface{}{}
						payloadCopy2 := make(map[string]interface{}, len(payload))
						for k, v := range payload {
							vCopy := v
							payloadCopy2[k] = vCopy
						}
						payloadCopy = payloadCopy2
						loopIndexCopy2 := loopIndex
						loopIndexCopy = loopIndexCopy2
					}
					for _, r := range acquiredResources["mailboxes"] {
						err = distsys.ReleaseResources(mailboxes.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					payload = payloadCopy
					loopIndex = loopIndexCopy
				} else {
					if reflect.DeepEqual(msgCopy["type"], PROPOSE_MSG()) && msgCopy["bal"].(int) < maxBalCopy {

						// ABadPropose:
						msg = msgCopy
						maxBal = maxBalCopy
					ABadPropose:
						acquiredResources = map[string]map[uint64]interface{}{}
						msgCopy2 := make(map[string]interface{}, len(msg))
						for k, v := range msg {
							vCopy := v
							msgCopy2[k] = vCopy
						}
						msgCopy = msgCopy2
						maxBalCopy1 := maxBal
						maxBalCopy = maxBalCopy1
						if _, ok := acquiredResources["mailboxes"]; !ok {
							acquiredResources["mailboxes"] = map[uint64]interface{}{}
						}
						resourceHash0 := distsys.Hash(msgCopy["sender"].(int))
						if _, acquired := acquiredResources["mailboxes"][resourceHash0]; !acquired {
							err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(msgCopy["sender"].(int)))
							if err != nil {
								for _, r := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r))
								}
								if shouldRetry(err) {
									goto ABadPropose
								} else {
									return err
								}
							}
							acquiredResources["mailboxes"][resourceHash0] = msgCopy["sender"].(int)
						}
						var resourceWrite interface{}
						resourceWrite = map[string]interface{}{
							"val":      msgCopy["val"],
							"sender":   self,
							"slot":     msgCopy["slot"].(int),
							"accepted": []map[string]interface{}{},
							"bal":      maxBalCopy,
							"type":     REJECT_MSG(),
						}
						err = mailboxes.Get(msgCopy["sender"].(int)).Write(resourceWrite)
						if err != nil {
							for _, r := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r))
							}
							if shouldRetry(err) {
								goto ABadPropose
							} else {
								return err
							}
						}
						for _, r := range acquiredResources["mailboxes"] {
							err = distsys.ReleaseResources(mailboxes.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						msg = msgCopy
						maxBal = maxBalCopy
					} else {
						msg = msgCopy
						maxBal = maxBalCopy
					}
				}
			}
		}
		acquiredResources = map[string]map[uint64]interface{}{}
		msgCopy2 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy2[k] = vCopy
		}
		msgCopy = msgCopy2
	}
	return nil
}

func AProposer(self int, mailboxes distsys.ArchetypeResourceCollection, valueStream distsys.ArchetypeResourceCollection, leaderFailure distsys.ArchetypeResourceCollection, electionInProgress distsys.ArchetypeResourceCollection, iAmTheLeader distsys.ArchetypeResourceCollection) error {
	var b int
	s := 1
	elected := false
	acceptedValues := []map[string]interface{}{}
	maxBal := -1
	var index int
	var entry map[string]interface{}
	var promises int
	var heartbeatMonitorId int
	accepts := 0
	var value interface{}
	var repropose bool
	var resp map[string]interface{}
	var bCopy int
	var sCopy int
	var electedCopy bool
	var acceptedValuesCopy []map[string]interface{}
	var maxBalCopy int
	var indexCopy int
	var entryCopy map[string]interface{}
	var promisesCopy int
	var heartbeatMonitorIdCopy int
	var acceptsCopy int
	var valueCopy interface{}
	var reproposeCopy bool
	var respCopy map[string]interface{}
	var err error
	var acquiredResources map[string]map[uint64]interface{}

	// Pre:
	acquiredResources = map[string]map[uint64]interface{}{}
	bCopy0 := b
	bCopy = bCopy0
	heartbeatMonitorIdCopy0 := heartbeatMonitorId
	heartbeatMonitorIdCopy = heartbeatMonitorIdCopy0
	bCopy = self
	heartbeatMonitorIdCopy = self + 3*NUM_NODES
	b = bCopy
	heartbeatMonitorId = heartbeatMonitorIdCopy

	// P:
	acquiredResources = map[string]map[uint64]interface{}{}
	for {
		if !true {
			break
		}

		// PLeaderCheck:
		acquiredResources = map[string]map[uint64]interface{}{}
		electedCopy0 := elected
		electedCopy = electedCopy0
		indexCopy0 := index
		indexCopy = indexCopy0
		acceptsCopy0 := accepts
		acceptsCopy = acceptsCopy0
		reproposeCopy0 := repropose
		reproposeCopy = reproposeCopy0
		if electedCopy {
			acceptsCopy = 0
			reproposeCopy = false
			indexCopy = 1

			// PFindMaxVal:
			elected = electedCopy
			index = indexCopy
			accepts = acceptsCopy
			repropose = reproposeCopy
		PFindMaxVal:
			acquiredResources = map[string]map[uint64]interface{}{}
			indexCopy1 := index
			indexCopy = indexCopy1
			valueCopy0 := value
			valueCopy = valueCopy0
			entryCopy0 := make(map[string]interface{}, len(entry))
			for k, v := range entry {
				vCopy := v
				entryCopy0[k] = vCopy
			}
			entryCopy = entryCopy0
			sCopy0 := s
			sCopy = sCopy0
			acceptedValuesCopy0 := make([]map[string]interface{}, len(acceptedValues))
			for i, e := range acceptedValues {
				eCopy := make(map[string]interface{}, len(e))
				for k, v := range e {
					vCopy := v
					eCopy[k] = vCopy
				}
				acceptedValuesCopy0[i] = eCopy
			}
			acceptedValuesCopy = acceptedValuesCopy0
			maxBalCopy0 := maxBal
			maxBalCopy = maxBalCopy0
			reproposeCopy1 := repropose
			reproposeCopy = reproposeCopy1
			for {
				if !(indexCopy <= len(acceptedValuesCopy)) {
					break
				}
				entryCopy = acceptedValuesCopy[indexCopy-1]
				if entryCopy["slot"].(int) == sCopy && entryCopy["bal"].(int) >= maxBalCopy {
					reproposeCopy = true
					valueCopy = entryCopy["val"]
					maxBalCopy = entryCopy["bal"].(int)
				}
				indexCopy = indexCopy + 1
				for _, r := range acquiredResources["valueStream"] {
					err = distsys.ReleaseResources(valueStream.Get(r))
					if err != nil {
						for _, r0 := range acquiredResources["valueStream"] {
							distsys.AbortResources(valueStream.Get(r0))
						}
						return err
					}
				}
				index = indexCopy
				value = valueCopy
				entry = entryCopy
				s = sCopy
				acceptedValues = acceptedValuesCopy
				maxBal = maxBalCopy
				repropose = reproposeCopy
				acquiredResources = map[string]map[uint64]interface{}{}
				indexCopy2 := index
				indexCopy = indexCopy2
				valueCopy1 := value
				valueCopy = valueCopy1
				entryCopy1 := make(map[string]interface{}, len(entry))
				for k, v := range entry {
					vCopy := v
					entryCopy1[k] = vCopy
				}
				entryCopy = entryCopy1
				sCopy1 := s
				sCopy = sCopy1
				acceptedValuesCopy1 := make([]map[string]interface{}, len(acceptedValues))
				for i, e := range acceptedValues {
					eCopy := make(map[string]interface{}, len(e))
					for k, v := range e {
						vCopy := v
						eCopy[k] = vCopy
					}
					acceptedValuesCopy1[i] = eCopy
				}
				acceptedValuesCopy = acceptedValuesCopy1
				maxBalCopy1 := maxBal
				maxBalCopy = maxBalCopy1
				reproposeCopy2 := repropose
				reproposeCopy = reproposeCopy2
			}
			if !reproposeCopy {
				if _, ok := acquiredResources["valueStream"]; !ok {
					acquiredResources["valueStream"] = map[uint64]interface{}{}
				}
				resourceHash := distsys.Hash(self)
				if _, acquired := acquiredResources["valueStream"][resourceHash]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, valueStream.Get(self))
					if err != nil {
						for _, r := range acquiredResources["valueStream"] {
							distsys.AbortResources(valueStream.Get(r))
						}
						if shouldRetry(err) {
							goto PFindMaxVal
						} else {
							return err
						}
					}
					acquiredResources["valueStream"][resourceHash] = self
				}
				var readTemp interface{}
				readTemp, err = valueStream.Get(self).Read()
				if err != nil {
					for _, r := range acquiredResources["valueStream"] {
						distsys.AbortResources(valueStream.Get(r))
					}
					if shouldRetry(err) {
						goto PFindMaxVal
					} else {
						return err
					}
				}
				valueCopy = readTemp
			}
			indexCopy = NUM_NODES
			for _, r := range acquiredResources["valueStream"] {
				err = distsys.ReleaseResources(valueStream.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["valueStream"] {
						distsys.AbortResources(valueStream.Get(r0))
					}
					return err
				}
			}
			index = indexCopy
			value = valueCopy
			entry = entryCopy
			s = sCopy
			acceptedValues = acceptedValuesCopy
			maxBal = maxBalCopy
			repropose = reproposeCopy

			// PSendProposes:
		PSendProposes:
			acquiredResources = map[string]map[uint64]interface{}{}
			indexCopy2 := index
			indexCopy = indexCopy2
			valueCopy1 := value
			valueCopy = valueCopy1
			bCopy1 := b
			bCopy = bCopy1
			sCopy1 := s
			sCopy = sCopy1
			for {
				if !(indexCopy <= 2*NUM_NODES-1) {
					break
				}
				if _, ok := acquiredResources["mailboxes"]; !ok {
					acquiredResources["mailboxes"] = map[uint64]interface{}{}
				}
				resourceHash := distsys.Hash(indexCopy)
				if _, acquired := acquiredResources["mailboxes"][resourceHash]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(indexCopy))
					if err != nil {
						for _, r := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r))
						}
						if shouldRetry(err) {
							goto PSendProposes
						} else {
							return err
						}
					}
					acquiredResources["mailboxes"][resourceHash] = indexCopy
				}
				var resourceWrite interface{}
				resourceWrite = map[string]interface{}{
					"val":    valueCopy,
					"sender": self,
					"slot":   sCopy,
					"bal":    bCopy,
					"type":   PROPOSE_MSG(),
				}
				err = mailboxes.Get(indexCopy).Write(resourceWrite)
				if err != nil {
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto PSendProposes
					} else {
						return err
					}
				}
				indexCopy = indexCopy + 1
				for _, r := range acquiredResources["mailboxes"] {
					err = distsys.ReleaseResources(mailboxes.Get(r))
					if err != nil {
						for _, r0 := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r0))
						}
						return err
					}
				}
				index = indexCopy
				value = valueCopy
				b = bCopy
				s = sCopy
				acquiredResources = map[string]map[uint64]interface{}{}
				indexCopy3 := index
				indexCopy = indexCopy3
				valueCopy2 := value
				valueCopy = valueCopy2
				bCopy2 := b
				bCopy = bCopy2
				sCopy2 := s
				sCopy = sCopy2
			}
			for _, r := range acquiredResources["mailboxes"] {
				err = distsys.ReleaseResources(mailboxes.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			index = indexCopy
			value = valueCopy
			b = bCopy
			s = sCopy

			// PSearchAccs:
		PSearchAccs:
			acquiredResources = map[string]map[uint64]interface{}{}
			electedCopy1 := elected
			electedCopy = electedCopy1
			valueCopy2 := value
			valueCopy = valueCopy2
			bCopy2 := b
			bCopy = bCopy2
			respCopy0 := make(map[string]interface{}, len(resp))
			for k, v := range resp {
				vCopy := v
				respCopy0[k] = vCopy
			}
			respCopy = respCopy0
			heartbeatMonitorIdCopy1 := heartbeatMonitorId
			heartbeatMonitorIdCopy = heartbeatMonitorIdCopy1
			sCopy2 := s
			sCopy = sCopy2
			acceptsCopy1 := accepts
			acceptsCopy = acceptsCopy1
			for {
				if !(acceptsCopy*2 < len(Acceptor()) && electedCopy) {
					for _, r := range acquiredResources["iAmTheLeader"] {
						err = distsys.ReleaseResources(iAmTheLeader.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					for _, r := range acquiredResources["electionInProgress"] {
						err = distsys.ReleaseResources(electionInProgress.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					for _, r := range acquiredResources["mailboxes"] {
						err = distsys.ReleaseResources(mailboxes.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					elected = electedCopy
					value = valueCopy
					b = bCopy
					resp = respCopy
					heartbeatMonitorId = heartbeatMonitorIdCopy
					s = sCopy
					accepts = acceptsCopy
					break
				}
				if _, ok := acquiredResources["mailboxes"]; !ok {
					acquiredResources["mailboxes"] = map[uint64]interface{}{}
				}
				resourceHash := distsys.Hash(self)
				if _, acquired := acquiredResources["mailboxes"][resourceHash]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(self))
					if err != nil {
						for _, r := range acquiredResources["iAmTheLeader"] {
							distsys.AbortResources(iAmTheLeader.Get(r))
						}
						for _, r := range acquiredResources["electionInProgress"] {
							distsys.AbortResources(electionInProgress.Get(r))
						}
						for _, r := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r))
						}
						if shouldRetry(err) {
							goto PSearchAccs
						} else {
							return err
						}
					}
					acquiredResources["mailboxes"][resourceHash] = self
				}
				var readTemp interface{}
				readTemp, err = mailboxes.Get(self).Read()
				if err != nil {
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto PSearchAccs
					} else {
						return err
					}
				}
				respCopy = readTemp.(map[string]interface{})
				if reflect.DeepEqual(respCopy["type"], ACCEPT_MSG()) {
					if respCopy["bal"].(int) == bCopy && respCopy["slot"].(int) == sCopy && reflect.DeepEqual(respCopy["val"], valueCopy) {
						acceptsCopy = acceptsCopy + 1
					}
					for _, r := range acquiredResources["iAmTheLeader"] {
						err = distsys.ReleaseResources(iAmTheLeader.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					for _, r := range acquiredResources["electionInProgress"] {
						err = distsys.ReleaseResources(electionInProgress.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					for _, r := range acquiredResources["mailboxes"] {
						err = distsys.ReleaseResources(mailboxes.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					elected = electedCopy
					value = valueCopy
					b = bCopy
					resp = respCopy
					heartbeatMonitorId = heartbeatMonitorIdCopy
					s = sCopy
					accepts = acceptsCopy
				} else {
					if reflect.DeepEqual(respCopy["type"], REJECT_MSG()) {
						electedCopy = false
						if _, ok := acquiredResources["iAmTheLeader"]; !ok {
							acquiredResources["iAmTheLeader"] = map[uint64]interface{}{}
						}
						resourceHash0 := distsys.Hash(heartbeatMonitorIdCopy)
						if _, acquired := acquiredResources["iAmTheLeader"][resourceHash0]; !acquired {
							err = distsys.AcquireResources(distsys.WRITE_ACCESS, iAmTheLeader.Get(heartbeatMonitorIdCopy))
							if err != nil {
								for _, r := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r))
								}
								for _, r := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r))
								}
								for _, r := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r))
								}
								if shouldRetry(err) {
									goto PSearchAccs
								} else {
									return err
								}
							}
							acquiredResources["iAmTheLeader"][resourceHash0] = heartbeatMonitorIdCopy
						}
						var resourceWrite interface{}
						resourceWrite = false
						err = iAmTheLeader.Get(heartbeatMonitorIdCopy).Write(resourceWrite)
						if err != nil {
							for _, r := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r))
							}
							for _, r := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r))
							}
							for _, r := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r))
							}
							if shouldRetry(err) {
								goto PSearchAccs
							} else {
								return err
							}
						}
						if _, ok := acquiredResources["electionInProgress"]; !ok {
							acquiredResources["electionInProgress"] = map[uint64]interface{}{}
						}
						resourceHash1 := distsys.Hash(heartbeatMonitorIdCopy)
						if _, acquired := acquiredResources["electionInProgress"][resourceHash1]; !acquired {
							err = distsys.AcquireResources(distsys.WRITE_ACCESS, electionInProgress.Get(heartbeatMonitorIdCopy))
							if err != nil {
								for _, r := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r))
								}
								for _, r := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r))
								}
								for _, r := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r))
								}
								if shouldRetry(err) {
									goto PSearchAccs
								} else {
									return err
								}
							}
							acquiredResources["electionInProgress"][resourceHash1] = heartbeatMonitorIdCopy
						}
						var resourceWrite0 interface{}
						resourceWrite0 = false
						err = electionInProgress.Get(heartbeatMonitorIdCopy).Write(resourceWrite0)
						if err != nil {
							for _, r := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r))
							}
							for _, r := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r))
							}
							for _, r := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r))
							}
							if shouldRetry(err) {
								goto PSearchAccs
							} else {
								return err
							}
						}

						// PWaitFailure:
						for _, r := range acquiredResources["iAmTheLeader"] {
							err = distsys.ReleaseResources(iAmTheLeader.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r0))
								}
								for _, r0 := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r0))
								}
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						for _, r := range acquiredResources["electionInProgress"] {
							err = distsys.ReleaseResources(electionInProgress.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r0))
								}
								for _, r0 := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r0))
								}
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						for _, r := range acquiredResources["mailboxes"] {
							err = distsys.ReleaseResources(mailboxes.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r0))
								}
								for _, r0 := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r0))
								}
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						elected = electedCopy
						value = valueCopy
						b = bCopy
						resp = respCopy
						heartbeatMonitorId = heartbeatMonitorIdCopy
						s = sCopy
						accepts = acceptsCopy
					PWaitFailure:
						acquiredResources = map[string]map[uint64]interface{}{}
						heartbeatMonitorIdCopy2 := heartbeatMonitorId
						heartbeatMonitorIdCopy = heartbeatMonitorIdCopy2
						if _, ok := acquiredResources["leaderFailure"]; !ok {
							acquiredResources["leaderFailure"] = map[uint64]interface{}{}
						}
						resourceHash2 := distsys.Hash(heartbeatMonitorIdCopy)
						if _, acquired := acquiredResources["leaderFailure"][resourceHash2]; !acquired {
							err = distsys.AcquireResources(distsys.WRITE_ACCESS, leaderFailure.Get(heartbeatMonitorIdCopy))
							if err != nil {
								for _, r := range acquiredResources["leaderFailure"] {
									distsys.AbortResources(leaderFailure.Get(r))
								}
								if shouldRetry(err) {
									goto PWaitFailure
								} else {
									return err
								}
							}
							acquiredResources["leaderFailure"][resourceHash2] = heartbeatMonitorIdCopy
						}
						var readTemp0 interface{}
						readTemp0, err = leaderFailure.Get(heartbeatMonitorIdCopy).Read()
						if err != nil {
							for _, r := range acquiredResources["leaderFailure"] {
								distsys.AbortResources(leaderFailure.Get(r))
							}
							if shouldRetry(err) {
								goto PWaitFailure
							} else {
								return err
							}
						}
						if !(readTemp0.(bool) == true) {
							panic("(leaderFailure[heartbeatMonitorId]) = (TRUE)")
						}
						for _, r := range acquiredResources["leaderFailure"] {
							err = distsys.ReleaseResources(leaderFailure.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["leaderFailure"] {
									distsys.AbortResources(leaderFailure.Get(r0))
								}
								return err
							}
						}
						heartbeatMonitorId = heartbeatMonitorIdCopy
					} else {
						for _, r := range acquiredResources["iAmTheLeader"] {
							err = distsys.ReleaseResources(iAmTheLeader.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["leaderFailure"] {
									distsys.AbortResources(leaderFailure.Get(r0))
								}
								return err
							}
						}
						for _, r := range acquiredResources["electionInProgress"] {
							err = distsys.ReleaseResources(electionInProgress.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["leaderFailure"] {
									distsys.AbortResources(leaderFailure.Get(r0))
								}
								return err
							}
						}
						for _, r := range acquiredResources["mailboxes"] {
							err = distsys.ReleaseResources(mailboxes.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["leaderFailure"] {
									distsys.AbortResources(leaderFailure.Get(r0))
								}
								return err
							}
						}
						elected = electedCopy
						value = valueCopy
						b = bCopy
						resp = respCopy
						heartbeatMonitorId = heartbeatMonitorIdCopy
						s = sCopy
						accepts = acceptsCopy
					}
				}
				acquiredResources = map[string]map[uint64]interface{}{}
				electedCopy2 := elected
				electedCopy = electedCopy2
				valueCopy3 := value
				valueCopy = valueCopy3
				bCopy3 := b
				bCopy = bCopy3
				respCopy1 := make(map[string]interface{}, len(resp))
				for k, v := range resp {
					vCopy := v
					respCopy1[k] = vCopy
				}
				respCopy = respCopy1
				heartbeatMonitorIdCopy2 := heartbeatMonitorId
				heartbeatMonitorIdCopy = heartbeatMonitorIdCopy2
				sCopy3 := s
				sCopy = sCopy3
				acceptsCopy2 := accepts
				acceptsCopy = acceptsCopy2
			}

			// PIncSlot:
			for _, r := range acquiredResources["iAmTheLeader"] {
				err = distsys.ReleaseResources(iAmTheLeader.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["electionInProgress"] {
				err = distsys.ReleaseResources(electionInProgress.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["mailboxes"] {
				err = distsys.ReleaseResources(mailboxes.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			elected = electedCopy
			value = valueCopy
			b = bCopy
			resp = respCopy
			heartbeatMonitorId = heartbeatMonitorIdCopy
			s = sCopy
			accepts = acceptsCopy
			acquiredResources = map[string]map[uint64]interface{}{}
			electedCopy2 := elected
			electedCopy = electedCopy2
			sCopy3 := s
			sCopy = sCopy3
			if electedCopy {
				sCopy = sCopy + 1
			}
			elected = electedCopy
			s = sCopy
		} else {
			indexCopy = NUM_NODES

			// PReqVotes:
			elected = electedCopy
			index = indexCopy
			accepts = acceptsCopy
			repropose = reproposeCopy
		PReqVotes:
			acquiredResources = map[string]map[uint64]interface{}{}
			indexCopy1 := index
			indexCopy = indexCopy1
			valueCopy0 := value
			valueCopy = valueCopy0
			promisesCopy0 := promises
			promisesCopy = promisesCopy0
			bCopy1 := b
			bCopy = bCopy1
			heartbeatMonitorIdCopy1 := heartbeatMonitorId
			heartbeatMonitorIdCopy = heartbeatMonitorIdCopy1
			for {
				if !(indexCopy <= 2*NUM_NODES-1) {
					break
				}
				if _, ok := acquiredResources["mailboxes"]; !ok {
					acquiredResources["mailboxes"] = map[uint64]interface{}{}
				}
				resourceHash := distsys.Hash(indexCopy)
				if _, acquired := acquiredResources["mailboxes"][resourceHash]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(indexCopy))
					if err != nil {
						for _, r := range acquiredResources["iAmTheLeader"] {
							distsys.AbortResources(iAmTheLeader.Get(r))
						}
						for _, r := range acquiredResources["electionInProgress"] {
							distsys.AbortResources(electionInProgress.Get(r))
						}
						for _, r := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r))
						}
						if shouldRetry(err) {
							goto PReqVotes
						} else {
							return err
						}
					}
					acquiredResources["mailboxes"][resourceHash] = indexCopy
				}
				var resourceWrite interface{}
				resourceWrite = map[string]interface{}{
					"val":    valueCopy,
					"sender": self,
					"slot":   NULL,
					"bal":    bCopy,
					"type":   PREPARE_MSG(),
				}
				err = mailboxes.Get(indexCopy).Write(resourceWrite)
				if err != nil {
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto PReqVotes
					} else {
						return err
					}
				}
				indexCopy = indexCopy + 1
				for _, r := range acquiredResources["iAmTheLeader"] {
					err = distsys.ReleaseResources(iAmTheLeader.Get(r))
					if err != nil {
						for _, r0 := range acquiredResources["iAmTheLeader"] {
							distsys.AbortResources(iAmTheLeader.Get(r0))
						}
						for _, r0 := range acquiredResources["electionInProgress"] {
							distsys.AbortResources(electionInProgress.Get(r0))
						}
						for _, r0 := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r0))
						}
						return err
					}
				}
				for _, r := range acquiredResources["electionInProgress"] {
					err = distsys.ReleaseResources(electionInProgress.Get(r))
					if err != nil {
						for _, r0 := range acquiredResources["iAmTheLeader"] {
							distsys.AbortResources(iAmTheLeader.Get(r0))
						}
						for _, r0 := range acquiredResources["electionInProgress"] {
							distsys.AbortResources(electionInProgress.Get(r0))
						}
						for _, r0 := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r0))
						}
						return err
					}
				}
				for _, r := range acquiredResources["mailboxes"] {
					err = distsys.ReleaseResources(mailboxes.Get(r))
					if err != nil {
						for _, r0 := range acquiredResources["iAmTheLeader"] {
							distsys.AbortResources(iAmTheLeader.Get(r0))
						}
						for _, r0 := range acquiredResources["electionInProgress"] {
							distsys.AbortResources(electionInProgress.Get(r0))
						}
						for _, r0 := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r0))
						}
						return err
					}
				}
				index = indexCopy
				value = valueCopy
				promises = promisesCopy
				b = bCopy
				heartbeatMonitorId = heartbeatMonitorIdCopy
				acquiredResources = map[string]map[uint64]interface{}{}
				indexCopy2 := index
				indexCopy = indexCopy2
				valueCopy1 := value
				valueCopy = valueCopy1
				promisesCopy1 := promises
				promisesCopy = promisesCopy1
				bCopy2 := b
				bCopy = bCopy2
				heartbeatMonitorIdCopy2 := heartbeatMonitorId
				heartbeatMonitorIdCopy = heartbeatMonitorIdCopy2
			}
			promisesCopy = 0
			if _, ok := acquiredResources["iAmTheLeader"]; !ok {
				acquiredResources["iAmTheLeader"] = map[uint64]interface{}{}
			}
			resourceHash := distsys.Hash(heartbeatMonitorIdCopy)
			if _, acquired := acquiredResources["iAmTheLeader"][resourceHash]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, iAmTheLeader.Get(heartbeatMonitorIdCopy))
				if err != nil {
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto PReqVotes
					} else {
						return err
					}
				}
				acquiredResources["iAmTheLeader"][resourceHash] = heartbeatMonitorIdCopy
			}
			var resourceWrite interface{}
			resourceWrite = false
			err = iAmTheLeader.Get(heartbeatMonitorIdCopy).Write(resourceWrite)
			if err != nil {
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto PReqVotes
				} else {
					return err
				}
			}
			if _, ok := acquiredResources["electionInProgress"]; !ok {
				acquiredResources["electionInProgress"] = map[uint64]interface{}{}
			}
			resourceHash0 := distsys.Hash(heartbeatMonitorIdCopy)
			if _, acquired := acquiredResources["electionInProgress"][resourceHash0]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, electionInProgress.Get(heartbeatMonitorIdCopy))
				if err != nil {
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto PReqVotes
					} else {
						return err
					}
				}
				acquiredResources["electionInProgress"][resourceHash0] = heartbeatMonitorIdCopy
			}
			var resourceWrite0 interface{}
			resourceWrite0 = true
			err = electionInProgress.Get(heartbeatMonitorIdCopy).Write(resourceWrite0)
			if err != nil {
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto PReqVotes
				} else {
					return err
				}
			}
			for _, r := range acquiredResources["iAmTheLeader"] {
				err = distsys.ReleaseResources(iAmTheLeader.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["electionInProgress"] {
				err = distsys.ReleaseResources(electionInProgress.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["mailboxes"] {
				err = distsys.ReleaseResources(mailboxes.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			index = indexCopy
			value = valueCopy
			promises = promisesCopy
			b = bCopy
			heartbeatMonitorId = heartbeatMonitorIdCopy

			// PCandidate:
		PCandidate:
			acquiredResources = map[string]map[uint64]interface{}{}
			electedCopy1 := elected
			electedCopy = electedCopy1
			promisesCopy1 := promises
			promisesCopy = promisesCopy1
			bCopy2 := b
			bCopy = bCopy2
			respCopy0 := make(map[string]interface{}, len(resp))
			for k, v := range resp {
				vCopy := v
				respCopy0[k] = vCopy
			}
			respCopy = respCopy0
			heartbeatMonitorIdCopy2 := heartbeatMonitorId
			heartbeatMonitorIdCopy = heartbeatMonitorIdCopy2
			acceptedValuesCopy0 := make([]map[string]interface{}, len(acceptedValues))
			for i, e := range acceptedValues {
				eCopy := make(map[string]interface{}, len(e))
				for k, v := range e {
					vCopy := v
					eCopy[k] = vCopy
				}
				acceptedValuesCopy0[i] = eCopy
			}
			acceptedValuesCopy = acceptedValuesCopy0
			for {
				if !!electedCopy {
					for _, r := range acquiredResources["iAmTheLeader"] {
						err = distsys.ReleaseResources(iAmTheLeader.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					for _, r := range acquiredResources["electionInProgress"] {
						err = distsys.ReleaseResources(electionInProgress.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					for _, r := range acquiredResources["mailboxes"] {
						err = distsys.ReleaseResources(mailboxes.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					elected = electedCopy
					promises = promisesCopy
					b = bCopy
					resp = respCopy
					heartbeatMonitorId = heartbeatMonitorIdCopy
					acceptedValues = acceptedValuesCopy
					break
				}
				if _, ok := acquiredResources["mailboxes"]; !ok {
					acquiredResources["mailboxes"] = map[uint64]interface{}{}
				}
				resourceHash1 := distsys.Hash(self)
				if _, acquired := acquiredResources["mailboxes"][resourceHash1]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(self))
					if err != nil {
						for _, r := range acquiredResources["iAmTheLeader"] {
							distsys.AbortResources(iAmTheLeader.Get(r))
						}
						for _, r := range acquiredResources["electionInProgress"] {
							distsys.AbortResources(electionInProgress.Get(r))
						}
						for _, r := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r))
						}
						if shouldRetry(err) {
							goto PCandidate
						} else {
							return err
						}
					}
					acquiredResources["mailboxes"][resourceHash1] = self
				}
				var readTemp interface{}
				readTemp, err = mailboxes.Get(self).Read()
				if err != nil {
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto PCandidate
					} else {
						return err
					}
				}
				respCopy = readTemp.(map[string]interface{})
				if reflect.DeepEqual(respCopy["type"], PROMISE_MSG()) && respCopy["bal"].(int) == bCopy {
					sequence := acceptedValuesCopy
					sequence = append(sequence, respCopy["accepted"].([]map[string]interface{})...)
					acceptedValuesCopy = sequence
					promisesCopy = promisesCopy + 1
					if promisesCopy*2 > len(Acceptor()) {
						electedCopy = true
						if _, ok := acquiredResources["iAmTheLeader"]; !ok {
							acquiredResources["iAmTheLeader"] = map[uint64]interface{}{}
						}
						resourceHash2 := distsys.Hash(heartbeatMonitorIdCopy)
						if _, acquired := acquiredResources["iAmTheLeader"][resourceHash2]; !acquired {
							err = distsys.AcquireResources(distsys.WRITE_ACCESS, iAmTheLeader.Get(heartbeatMonitorIdCopy))
							if err != nil {
								for _, r := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r))
								}
								for _, r := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r))
								}
								for _, r := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r))
								}
								if shouldRetry(err) {
									goto PCandidate
								} else {
									return err
								}
							}
							acquiredResources["iAmTheLeader"][resourceHash2] = heartbeatMonitorIdCopy
						}
						var resourceWrite1 interface{}
						resourceWrite1 = true
						err = iAmTheLeader.Get(heartbeatMonitorIdCopy).Write(resourceWrite1)
						if err != nil {
							for _, r := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r))
							}
							for _, r := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r))
							}
							for _, r := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r))
							}
							if shouldRetry(err) {
								goto PCandidate
							} else {
								return err
							}
						}
						if _, ok := acquiredResources["electionInProgress"]; !ok {
							acquiredResources["electionInProgress"] = map[uint64]interface{}{}
						}
						resourceHash3 := distsys.Hash(heartbeatMonitorIdCopy)
						if _, acquired := acquiredResources["electionInProgress"][resourceHash3]; !acquired {
							err = distsys.AcquireResources(distsys.WRITE_ACCESS, electionInProgress.Get(heartbeatMonitorIdCopy))
							if err != nil {
								for _, r := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r))
								}
								for _, r := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r))
								}
								for _, r := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r))
								}
								if shouldRetry(err) {
									goto PCandidate
								} else {
									return err
								}
							}
							acquiredResources["electionInProgress"][resourceHash3] = heartbeatMonitorIdCopy
						}
						var resourceWrite2 interface{}
						resourceWrite2 = false
						err = electionInProgress.Get(heartbeatMonitorIdCopy).Write(resourceWrite2)
						if err != nil {
							for _, r := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r))
							}
							for _, r := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r))
							}
							for _, r := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r))
							}
							if shouldRetry(err) {
								goto PCandidate
							} else {
								return err
							}
						}
					}
					for _, r := range acquiredResources["iAmTheLeader"] {
						err = distsys.ReleaseResources(iAmTheLeader.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					for _, r := range acquiredResources["electionInProgress"] {
						err = distsys.ReleaseResources(electionInProgress.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					for _, r := range acquiredResources["mailboxes"] {
						err = distsys.ReleaseResources(mailboxes.Get(r))
						if err != nil {
							for _, r0 := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r0))
							}
							for _, r0 := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r0))
							}
							for _, r0 := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r0))
							}
							return err
						}
					}
					elected = electedCopy
					promises = promisesCopy
					b = bCopy
					resp = respCopy
					heartbeatMonitorId = heartbeatMonitorIdCopy
					acceptedValues = acceptedValuesCopy
				} else {
					if reflect.DeepEqual(respCopy["type"], REJECT_MSG()) || respCopy["bal"].(int) > bCopy {
						if _, ok := acquiredResources["electionInProgress"]; !ok {
							acquiredResources["electionInProgress"] = map[uint64]interface{}{}
						}
						resourceHash2 := distsys.Hash(heartbeatMonitorIdCopy)
						if _, acquired := acquiredResources["electionInProgress"][resourceHash2]; !acquired {
							err = distsys.AcquireResources(distsys.WRITE_ACCESS, electionInProgress.Get(heartbeatMonitorIdCopy))
							if err != nil {
								for _, r := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r))
								}
								for _, r := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r))
								}
								for _, r := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r))
								}
								if shouldRetry(err) {
									goto PCandidate
								} else {
									return err
								}
							}
							acquiredResources["electionInProgress"][resourceHash2] = heartbeatMonitorIdCopy
						}
						var resourceWrite1 interface{}
						resourceWrite1 = false
						err = electionInProgress.Get(heartbeatMonitorIdCopy).Write(resourceWrite1)
						if err != nil {
							for _, r := range acquiredResources["iAmTheLeader"] {
								distsys.AbortResources(iAmTheLeader.Get(r))
							}
							for _, r := range acquiredResources["electionInProgress"] {
								distsys.AbortResources(electionInProgress.Get(r))
							}
							for _, r := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r))
							}
							if shouldRetry(err) {
								goto PCandidate
							} else {
								return err
							}
						}

						// PWaitLeaderFailure:
						for _, r := range acquiredResources["iAmTheLeader"] {
							err = distsys.ReleaseResources(iAmTheLeader.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r0))
								}
								for _, r0 := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r0))
								}
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						for _, r := range acquiredResources["electionInProgress"] {
							err = distsys.ReleaseResources(electionInProgress.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r0))
								}
								for _, r0 := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r0))
								}
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						for _, r := range acquiredResources["mailboxes"] {
							err = distsys.ReleaseResources(mailboxes.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["iAmTheLeader"] {
									distsys.AbortResources(iAmTheLeader.Get(r0))
								}
								for _, r0 := range acquiredResources["electionInProgress"] {
									distsys.AbortResources(electionInProgress.Get(r0))
								}
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						elected = electedCopy
						promises = promisesCopy
						b = bCopy
						resp = respCopy
						heartbeatMonitorId = heartbeatMonitorIdCopy
						acceptedValues = acceptedValuesCopy
					PWaitLeaderFailure:
						acquiredResources = map[string]map[uint64]interface{}{}
						indexCopy2 := index
						indexCopy = indexCopy2
						bCopy3 := b
						bCopy = bCopy3
						heartbeatMonitorIdCopy3 := heartbeatMonitorId
						heartbeatMonitorIdCopy = heartbeatMonitorIdCopy3
						if _, ok := acquiredResources["leaderFailure"]; !ok {
							acquiredResources["leaderFailure"] = map[uint64]interface{}{}
						}
						resourceHash3 := distsys.Hash(heartbeatMonitorIdCopy)
						if _, acquired := acquiredResources["leaderFailure"][resourceHash3]; !acquired {
							err = distsys.AcquireResources(distsys.WRITE_ACCESS, leaderFailure.Get(heartbeatMonitorIdCopy))
							if err != nil {
								for _, r := range acquiredResources["leaderFailure"] {
									distsys.AbortResources(leaderFailure.Get(r))
								}
								if shouldRetry(err) {
									goto PWaitLeaderFailure
								} else {
									return err
								}
							}
							acquiredResources["leaderFailure"][resourceHash3] = heartbeatMonitorIdCopy
						}
						var readTemp0 interface{}
						readTemp0, err = leaderFailure.Get(heartbeatMonitorIdCopy).Read()
						if err != nil {
							for _, r := range acquiredResources["leaderFailure"] {
								distsys.AbortResources(leaderFailure.Get(r))
							}
							if shouldRetry(err) {
								goto PWaitLeaderFailure
							} else {
								return err
							}
						}
						if !(readTemp0.(bool) == true) {
							panic("(leaderFailure[heartbeatMonitorId]) = (TRUE)")
						}
						bCopy = bCopy + NUM_NODES
						indexCopy = NUM_NODES
						for _, r := range acquiredResources["leaderFailure"] {
							err = distsys.ReleaseResources(leaderFailure.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["leaderFailure"] {
									distsys.AbortResources(leaderFailure.Get(r0))
								}
								return err
							}
						}
						index = indexCopy
						b = bCopy
						heartbeatMonitorId = heartbeatMonitorIdCopy

						// PReSendReqVotes:
					PReSendReqVotes:
						acquiredResources = map[string]map[uint64]interface{}{}
						indexCopy3 := index
						indexCopy = indexCopy3
						valueCopy1 := value
						valueCopy = valueCopy1
						bCopy4 := b
						bCopy = bCopy4
						for {
							if !(indexCopy <= 2*NUM_NODES-1) {
								break
							}
							if _, ok := acquiredResources["mailboxes"]; !ok {
								acquiredResources["mailboxes"] = map[uint64]interface{}{}
							}
							resourceHash4 := distsys.Hash(indexCopy)
							if _, acquired := acquiredResources["mailboxes"][resourceHash4]; !acquired {
								err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(indexCopy))
								if err != nil {
									for _, r := range acquiredResources["mailboxes"] {
										distsys.AbortResources(mailboxes.Get(r))
									}
									if shouldRetry(err) {
										goto PReSendReqVotes
									} else {
										return err
									}
								}
								acquiredResources["mailboxes"][resourceHash4] = indexCopy
							}
							var resourceWrite2 interface{}
							resourceWrite2 = map[string]interface{}{
								"val":    valueCopy,
								"sender": self,
								"slot":   NULL,
								"bal":    bCopy,
								"type":   PREPARE_MSG(),
							}
							err = mailboxes.Get(indexCopy).Write(resourceWrite2)
							if err != nil {
								for _, r := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r))
								}
								if shouldRetry(err) {
									goto PReSendReqVotes
								} else {
									return err
								}
							}
							indexCopy = indexCopy + 1
							for _, r := range acquiredResources["mailboxes"] {
								err = distsys.ReleaseResources(mailboxes.Get(r))
								if err != nil {
									for _, r0 := range acquiredResources["mailboxes"] {
										distsys.AbortResources(mailboxes.Get(r0))
									}
									return err
								}
							}
							index = indexCopy
							value = valueCopy
							b = bCopy
							acquiredResources = map[string]map[uint64]interface{}{}
							indexCopy4 := index
							indexCopy = indexCopy4
							valueCopy2 := value
							valueCopy = valueCopy2
							bCopy5 := b
							bCopy = bCopy5
						}
						for _, r := range acquiredResources["mailboxes"] {
							err = distsys.ReleaseResources(mailboxes.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						index = indexCopy
						value = valueCopy
						b = bCopy
					} else {
						for _, r := range acquiredResources["iAmTheLeader"] {
							err = distsys.ReleaseResources(iAmTheLeader.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						for _, r := range acquiredResources["electionInProgress"] {
							err = distsys.ReleaseResources(electionInProgress.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						for _, r := range acquiredResources["mailboxes"] {
							err = distsys.ReleaseResources(mailboxes.Get(r))
							if err != nil {
								for _, r0 := range acquiredResources["mailboxes"] {
									distsys.AbortResources(mailboxes.Get(r0))
								}
								return err
							}
						}
						elected = electedCopy
						promises = promisesCopy
						b = bCopy
						resp = respCopy
						heartbeatMonitorId = heartbeatMonitorIdCopy
						acceptedValues = acceptedValuesCopy
					}
				}
				acquiredResources = map[string]map[uint64]interface{}{}
				electedCopy2 := elected
				electedCopy = electedCopy2
				promisesCopy2 := promises
				promisesCopy = promisesCopy2
				bCopy3 := b
				bCopy = bCopy3
				respCopy1 := make(map[string]interface{}, len(resp))
				for k, v := range resp {
					vCopy := v
					respCopy1[k] = vCopy
				}
				respCopy = respCopy1
				heartbeatMonitorIdCopy3 := heartbeatMonitorId
				heartbeatMonitorIdCopy = heartbeatMonitorIdCopy3
				acceptedValuesCopy1 := make([]map[string]interface{}, len(acceptedValues))
				for i, e := range acceptedValues {
					eCopy := make(map[string]interface{}, len(e))
					for k, v := range e {
						vCopy := v
						eCopy[k] = vCopy
					}
					acceptedValuesCopy1[i] = eCopy
				}
				acceptedValuesCopy = acceptedValuesCopy1
			}
			for _, r := range acquiredResources["iAmTheLeader"] {
				err = distsys.ReleaseResources(iAmTheLeader.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["electionInProgress"] {
				err = distsys.ReleaseResources(electionInProgress.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["mailboxes"] {
				err = distsys.ReleaseResources(mailboxes.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			elected = electedCopy
			promises = promisesCopy
			b = bCopy
			resp = respCopy
			heartbeatMonitorId = heartbeatMonitorIdCopy
			acceptedValues = acceptedValuesCopy
		}
		acquiredResources = map[string]map[uint64]interface{}{}
	}
	return nil
}

func HEARTBEAT_MSG() string {
	return "heartbeat_msg"
}

func HeartbeatAction(self int, mailboxes distsys.ArchetypeResourceCollection, lastSeen distsys.ArchetypeResource, sleeper distsys.ArchetypeResource, electionInProgress distsys.ArchetypeResourceCollection, iAmTheLeader distsys.ArchetypeResourceCollection, heartbeatFrequency distsys.ArchetypeResource) error {
	var msg map[string]interface{}
	var index int
	var msgCopy map[string]interface{}
	var indexCopy int
	var err error
	var acquiredResources map[string]map[uint64]interface{}

	// mainLoop:
	acquiredResources = map[string]map[uint64]interface{}{}
	for {
		if !true {
			break
		}

		// leaderLoop:
	leaderLoop:
		acquiredResources = map[string]map[uint64]interface{}{}
		indexCopy0 := index
		indexCopy = indexCopy0
		for {
			if _, ok := acquiredResources["electionInProgress"]; !ok {
				acquiredResources["electionInProgress"] = map[uint64]interface{}{}
			}
			resourceHash := distsys.Hash(self)
			if _, acquired := acquiredResources["electionInProgress"][resourceHash]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, electionInProgress.Get(self))
				if err != nil {
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					if shouldRetry(err) {
						goto leaderLoop
					} else {
						return err
					}
				}
				acquiredResources["electionInProgress"][resourceHash] = self
			}
			var readTemp interface{}
			readTemp, err = electionInProgress.Get(self).Read()
			if err != nil {
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				if shouldRetry(err) {
					goto leaderLoop
				} else {
					return err
				}
			}
			if _, ok := acquiredResources["iAmTheLeader"]; !ok {
				acquiredResources["iAmTheLeader"] = map[uint64]interface{}{}
			}
			resourceHash0 := distsys.Hash(self)
			if _, acquired := acquiredResources["iAmTheLeader"][resourceHash0]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, iAmTheLeader.Get(self))
				if err != nil {
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					if shouldRetry(err) {
						goto leaderLoop
					} else {
						return err
					}
				}
				acquiredResources["iAmTheLeader"][resourceHash0] = self
			}
			var readTemp0 interface{}
			readTemp0, err = iAmTheLeader.Get(self).Read()
			if err != nil {
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				if shouldRetry(err) {
					goto leaderLoop
				} else {
					return err
				}
			}
			if !(!readTemp.(bool) && readTemp0.(bool)) {
				for _, r := range acquiredResources["iAmTheLeader"] {
					err = distsys.ReleaseResources(iAmTheLeader.Get(r))
					if err != nil {
						for _, r0 := range acquiredResources["iAmTheLeader"] {
							distsys.AbortResources(iAmTheLeader.Get(r0))
						}
						for _, r0 := range acquiredResources["electionInProgress"] {
							distsys.AbortResources(electionInProgress.Get(r0))
						}
						return err
					}
				}
				for _, r := range acquiredResources["electionInProgress"] {
					err = distsys.ReleaseResources(electionInProgress.Get(r))
					if err != nil {
						for _, r0 := range acquiredResources["iAmTheLeader"] {
							distsys.AbortResources(iAmTheLeader.Get(r0))
						}
						for _, r0 := range acquiredResources["electionInProgress"] {
							distsys.AbortResources(electionInProgress.Get(r0))
						}
						return err
					}
				}
				index = indexCopy
				break
			}
			indexCopy = 3 * NUM_NODES

			// heartbeatBroadcast:
			for _, r := range acquiredResources["iAmTheLeader"] {
				err = distsys.ReleaseResources(iAmTheLeader.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["electionInProgress"] {
				err = distsys.ReleaseResources(electionInProgress.Get(r))
				if err != nil {
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					return err
				}
			}
			index = indexCopy
		heartbeatBroadcast:
			acquiredResources = map[string]map[uint64]interface{}{}
			indexCopy1 := index
			indexCopy = indexCopy1
			err = distsys.AcquireResources(distsys.READ_ACCESS, heartbeatFrequency)
			if err != nil {
				if shouldRetry(err) {
					goto heartbeatBroadcast
				} else {
					return err
				}
			}
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, sleeper)
			if err != nil {
				if shouldRetry(err) {
					goto heartbeatBroadcast
				} else {
					return err
				}
			}
			for {
				if !(indexCopy <= 4*NUM_NODES-1) {
					break
				}
				if indexCopy != self {
					if _, ok := acquiredResources["mailboxes"]; !ok {
						acquiredResources["mailboxes"] = map[uint64]interface{}{}
					}
					resourceHash1 := distsys.Hash(indexCopy)
					if _, acquired := acquiredResources["mailboxes"][resourceHash1]; !acquired {
						err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(indexCopy))
						if err != nil {
							distsys.AbortResources(sleeper, heartbeatFrequency)
							for _, r := range acquiredResources["mailboxes"] {
								distsys.AbortResources(mailboxes.Get(r))
							}
							if shouldRetry(err) {
								goto heartbeatBroadcast
							} else {
								return err
							}
						}
						acquiredResources["mailboxes"][resourceHash1] = indexCopy
					}
					var resourceWrite interface{}
					resourceWrite = map[string]interface{}{
						"leader": self - 3*NUM_NODES,
						"type":   HEARTBEAT_MSG(),
					}
					err = mailboxes.Get(indexCopy).Write(resourceWrite)
					if err != nil {
						distsys.AbortResources(sleeper, heartbeatFrequency)
						for _, r := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r))
						}
						if shouldRetry(err) {
							goto heartbeatBroadcast
						} else {
							return err
						}
					}
				}
				indexCopy = indexCopy + 1
				err = distsys.ReleaseResources(sleeper, heartbeatFrequency)
				if err != nil {
					distsys.AbortResources(sleeper, heartbeatFrequency)
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					return err
				}
				for _, r := range acquiredResources["mailboxes"] {
					err = distsys.ReleaseResources(mailboxes.Get(r))
					if err != nil {
						distsys.AbortResources(sleeper, heartbeatFrequency)
						for _, r0 := range acquiredResources["mailboxes"] {
							distsys.AbortResources(mailboxes.Get(r0))
						}
						return err
					}
				}
				index = indexCopy
				acquiredResources = map[string]map[uint64]interface{}{}
				indexCopy2 := index
				indexCopy = indexCopy2
				err = distsys.AcquireResources(distsys.READ_ACCESS, heartbeatFrequency)
				if err != nil {
					if shouldRetry(err) {
						goto heartbeatBroadcast
					} else {
						return err
					}
				}
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, sleeper)
				if err != nil {
					if shouldRetry(err) {
						goto heartbeatBroadcast
					} else {
						return err
					}
				}
			}
			var resourceWrite interface{}
			var readTemp1 interface{}
			readTemp1, err = heartbeatFrequency.Read()
			if err != nil {
				distsys.AbortResources(sleeper, heartbeatFrequency)
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto heartbeatBroadcast
				} else {
					return err
				}
			}
			resourceWrite = readTemp1
			err = sleeper.Write(resourceWrite)
			if err != nil {
				distsys.AbortResources(sleeper, heartbeatFrequency)
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto heartbeatBroadcast
				} else {
					return err
				}
			}
			err = distsys.ReleaseResources(sleeper, heartbeatFrequency)
			if err != nil {
				distsys.AbortResources(sleeper, heartbeatFrequency)
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				return err
			}
			for _, r := range acquiredResources["mailboxes"] {
				err = distsys.ReleaseResources(mailboxes.Get(r))
				if err != nil {
					distsys.AbortResources(sleeper, heartbeatFrequency)
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			index = indexCopy
			acquiredResources = map[string]map[uint64]interface{}{}
			indexCopy2 := index
			indexCopy = indexCopy2
		}

		// followerLoop:
		for _, r := range acquiredResources["iAmTheLeader"] {
			err = distsys.ReleaseResources(iAmTheLeader.Get(r))
			if err != nil {
				for _, r0 := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r0))
				}
				for _, r0 := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r0))
				}
				return err
			}
		}
		for _, r := range acquiredResources["electionInProgress"] {
			err = distsys.ReleaseResources(electionInProgress.Get(r))
			if err != nil {
				for _, r0 := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r0))
				}
				for _, r0 := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r0))
				}
				return err
			}
		}
		index = indexCopy
	followerLoop:
		acquiredResources = map[string]map[uint64]interface{}{}
		msgCopy0 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy0[k] = vCopy
		}
		msgCopy = msgCopy0
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, lastSeen)
		if err != nil {
			if shouldRetry(err) {
				goto followerLoop
			} else {
				return err
			}
		}
		for {
			if _, ok := acquiredResources["electionInProgress"]; !ok {
				acquiredResources["electionInProgress"] = map[uint64]interface{}{}
			}
			resourceHash := distsys.Hash(self)
			if _, acquired := acquiredResources["electionInProgress"][resourceHash]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, electionInProgress.Get(self))
				if err != nil {
					distsys.AbortResources(lastSeen)
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto followerLoop
					} else {
						return err
					}
				}
				acquiredResources["electionInProgress"][resourceHash] = self
			}
			var readTemp interface{}
			readTemp, err = electionInProgress.Get(self).Read()
			if err != nil {
				distsys.AbortResources(lastSeen)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto followerLoop
				} else {
					return err
				}
			}
			if _, ok := acquiredResources["iAmTheLeader"]; !ok {
				acquiredResources["iAmTheLeader"] = map[uint64]interface{}{}
			}
			resourceHash0 := distsys.Hash(self)
			if _, acquired := acquiredResources["iAmTheLeader"][resourceHash0]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, iAmTheLeader.Get(self))
				if err != nil {
					distsys.AbortResources(lastSeen)
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto followerLoop
					} else {
						return err
					}
				}
				acquiredResources["iAmTheLeader"][resourceHash0] = self
			}
			var readTemp0 interface{}
			readTemp0, err = iAmTheLeader.Get(self).Read()
			if err != nil {
				distsys.AbortResources(lastSeen)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto followerLoop
				} else {
					return err
				}
			}
			if !(!readTemp.(bool) && !readTemp0.(bool)) {
				break
			}
			if _, ok := acquiredResources["mailboxes"]; !ok {
				acquiredResources["mailboxes"] = map[uint64]interface{}{}
			}
			resourceHash1 := distsys.Hash(self)
			if _, acquired := acquiredResources["mailboxes"][resourceHash1]; !acquired {
				err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(self))
				if err != nil {
					distsys.AbortResources(lastSeen)
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					for _, r := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r))
					}
					if shouldRetry(err) {
						goto followerLoop
					} else {
						return err
					}
				}
				acquiredResources["mailboxes"][resourceHash1] = self
			}
			var readTemp1 interface{}
			readTemp1, err = mailboxes.Get(self).Read()
			if err != nil {
				distsys.AbortResources(lastSeen)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto followerLoop
				} else {
					return err
				}
			}
			msgCopy = readTemp1.(map[string]interface{})
			if !reflect.DeepEqual(msgCopy["type"], HEARTBEAT_MSG()) {
				panic("((msg).type) = (HEARTBEAT_MSG)")
			}
			var resourceWrite interface{}
			resourceWrite = msgCopy
			err = lastSeen.Write(resourceWrite)
			if err != nil {
				distsys.AbortResources(lastSeen)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto followerLoop
				} else {
					return err
				}
			}
			err = distsys.ReleaseResources(lastSeen)
			if err != nil {
				distsys.AbortResources(lastSeen)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				return err
			}
			for _, r := range acquiredResources["iAmTheLeader"] {
				err = distsys.ReleaseResources(iAmTheLeader.Get(r))
				if err != nil {
					distsys.AbortResources(lastSeen)
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["electionInProgress"] {
				err = distsys.ReleaseResources(electionInProgress.Get(r))
				if err != nil {
					distsys.AbortResources(lastSeen)
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["mailboxes"] {
				err = distsys.ReleaseResources(mailboxes.Get(r))
				if err != nil {
					distsys.AbortResources(lastSeen)
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["mailboxes"] {
						distsys.AbortResources(mailboxes.Get(r0))
					}
					return err
				}
			}
			msg = msgCopy
			acquiredResources = map[string]map[uint64]interface{}{}
			msgCopy1 := make(map[string]interface{}, len(msg))
			for k, v := range msg {
				vCopy := v
				msgCopy1[k] = vCopy
			}
			msgCopy = msgCopy1
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, lastSeen)
			if err != nil {
				if shouldRetry(err) {
					goto followerLoop
				} else {
					return err
				}
			}
		}
		err = distsys.ReleaseResources(lastSeen)
		if err != nil {
			distsys.AbortResources(lastSeen)
			for _, r := range acquiredResources["iAmTheLeader"] {
				distsys.AbortResources(iAmTheLeader.Get(r))
			}
			for _, r := range acquiredResources["electionInProgress"] {
				distsys.AbortResources(electionInProgress.Get(r))
			}
			for _, r := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			return err
		}
		for _, r := range acquiredResources["iAmTheLeader"] {
			err = distsys.ReleaseResources(iAmTheLeader.Get(r))
			if err != nil {
				distsys.AbortResources(lastSeen)
				for _, r0 := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r0))
				}
				for _, r0 := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r0))
				}
				for _, r0 := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		for _, r := range acquiredResources["electionInProgress"] {
			err = distsys.ReleaseResources(electionInProgress.Get(r))
			if err != nil {
				distsys.AbortResources(lastSeen)
				for _, r0 := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r0))
				}
				for _, r0 := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r0))
				}
				for _, r0 := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		for _, r := range acquiredResources["mailboxes"] {
			err = distsys.ReleaseResources(mailboxes.Get(r))
			if err != nil {
				distsys.AbortResources(lastSeen)
				for _, r0 := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r0))
				}
				for _, r0 := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r0))
				}
				for _, r0 := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		msg = msgCopy
		acquiredResources = map[string]map[uint64]interface{}{}
	}
	return nil
}

func LeaderStatusMonitor(self int, timeoutChecker distsys.ArchetypeResource, leaderFailure distsys.ArchetypeResourceCollection, electionInProgress distsys.ArchetypeResourceCollection, iAmTheLeader distsys.ArchetypeResourceCollection, sleeper distsys.ArchetypeResource, monitorFrequency distsys.ArchetypeResource) error {
	var heartbeatId int
	var heartbeatIdCopy int
	var err error
	var acquiredResources map[string]map[uint64]interface{}

	// findId:
	acquiredResources = map[string]map[uint64]interface{}{}
	heartbeatIdCopy0 := heartbeatId
	heartbeatIdCopy = heartbeatIdCopy0
	heartbeatIdCopy = self - NUM_NODES
	heartbeatId = heartbeatIdCopy

	// monitorLoop:
monitorLoop:
	acquiredResources = map[string]map[uint64]interface{}{}
	heartbeatIdCopy1 := heartbeatId
	heartbeatIdCopy = heartbeatIdCopy1
	err = distsys.AcquireResources(distsys.READ_ACCESS, timeoutChecker)
	if err != nil {
		if shouldRetry(err) {
			goto monitorLoop
		} else {
			return err
		}
	}
	for {
		if !true {
			err = distsys.ReleaseResources(timeoutChecker)
			if err != nil {
				distsys.AbortResources(timeoutChecker)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["leaderFailure"] {
					distsys.AbortResources(leaderFailure.Get(r))
				}
				return err
			}
			for _, r := range acquiredResources["iAmTheLeader"] {
				err = distsys.ReleaseResources(iAmTheLeader.Get(r))
				if err != nil {
					distsys.AbortResources(timeoutChecker)
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["leaderFailure"] {
						distsys.AbortResources(leaderFailure.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["electionInProgress"] {
				err = distsys.ReleaseResources(electionInProgress.Get(r))
				if err != nil {
					distsys.AbortResources(timeoutChecker)
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["leaderFailure"] {
						distsys.AbortResources(leaderFailure.Get(r0))
					}
					return err
				}
			}
			for _, r := range acquiredResources["leaderFailure"] {
				err = distsys.ReleaseResources(leaderFailure.Get(r))
				if err != nil {
					distsys.AbortResources(timeoutChecker)
					for _, r0 := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r0))
					}
					for _, r0 := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r0))
					}
					for _, r0 := range acquiredResources["leaderFailure"] {
						distsys.AbortResources(leaderFailure.Get(r0))
					}
					return err
				}
			}
			heartbeatId = heartbeatIdCopy
			break
		}
		if _, ok := acquiredResources["electionInProgress"]; !ok {
			acquiredResources["electionInProgress"] = map[uint64]interface{}{}
		}
		resourceHash := distsys.Hash(heartbeatIdCopy)
		if _, acquired := acquiredResources["electionInProgress"][resourceHash]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, electionInProgress.Get(heartbeatIdCopy))
			if err != nil {
				distsys.AbortResources(timeoutChecker)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["leaderFailure"] {
					distsys.AbortResources(leaderFailure.Get(r))
				}
				if shouldRetry(err) {
					goto monitorLoop
				} else {
					return err
				}
			}
			acquiredResources["electionInProgress"][resourceHash] = heartbeatIdCopy
		}
		var readTemp interface{}
		readTemp, err = electionInProgress.Get(heartbeatIdCopy).Read()
		if err != nil {
			distsys.AbortResources(timeoutChecker)
			for _, r := range acquiredResources["iAmTheLeader"] {
				distsys.AbortResources(iAmTheLeader.Get(r))
			}
			for _, r := range acquiredResources["electionInProgress"] {
				distsys.AbortResources(electionInProgress.Get(r))
			}
			for _, r := range acquiredResources["leaderFailure"] {
				distsys.AbortResources(leaderFailure.Get(r))
			}
			if shouldRetry(err) {
				goto monitorLoop
			} else {
				return err
			}
		}
		if _, ok := acquiredResources["iAmTheLeader"]; !ok {
			acquiredResources["iAmTheLeader"] = map[uint64]interface{}{}
		}
		resourceHash0 := distsys.Hash(heartbeatIdCopy)
		if _, acquired := acquiredResources["iAmTheLeader"][resourceHash0]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, iAmTheLeader.Get(heartbeatIdCopy))
			if err != nil {
				distsys.AbortResources(timeoutChecker)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["leaderFailure"] {
					distsys.AbortResources(leaderFailure.Get(r))
				}
				if shouldRetry(err) {
					goto monitorLoop
				} else {
					return err
				}
			}
			acquiredResources["iAmTheLeader"][resourceHash0] = heartbeatIdCopy
		}
		var readTemp0 interface{}
		readTemp0, err = iAmTheLeader.Get(heartbeatIdCopy).Read()
		if err != nil {
			distsys.AbortResources(timeoutChecker)
			for _, r := range acquiredResources["iAmTheLeader"] {
				distsys.AbortResources(iAmTheLeader.Get(r))
			}
			for _, r := range acquiredResources["electionInProgress"] {
				distsys.AbortResources(electionInProgress.Get(r))
			}
			for _, r := range acquiredResources["leaderFailure"] {
				distsys.AbortResources(leaderFailure.Get(r))
			}
			if shouldRetry(err) {
				goto monitorLoop
			} else {
				return err
			}
		}
		if !readTemp.(bool) && !readTemp0.(bool) {
			var readTemp1 interface{}
			readTemp1, err = timeoutChecker.Read()
			if err != nil {
				distsys.AbortResources(timeoutChecker)
				for _, r := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r))
				}
				for _, r := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r))
				}
				for _, r := range acquiredResources["leaderFailure"] {
					distsys.AbortResources(leaderFailure.Get(r))
				}
				if shouldRetry(err) {
					goto monitorLoop
				} else {
					return err
				}
			}
			if readTemp1.(bool) {
				if _, ok := acquiredResources["leaderFailure"]; !ok {
					acquiredResources["leaderFailure"] = map[uint64]interface{}{}
				}
				resourceHash1 := distsys.Hash(heartbeatIdCopy)
				if _, acquired := acquiredResources["leaderFailure"][resourceHash1]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, leaderFailure.Get(heartbeatIdCopy))
					if err != nil {
						distsys.AbortResources(timeoutChecker)
						for _, r := range acquiredResources["iAmTheLeader"] {
							distsys.AbortResources(iAmTheLeader.Get(r))
						}
						for _, r := range acquiredResources["electionInProgress"] {
							distsys.AbortResources(electionInProgress.Get(r))
						}
						for _, r := range acquiredResources["leaderFailure"] {
							distsys.AbortResources(leaderFailure.Get(r))
						}
						if shouldRetry(err) {
							goto monitorLoop
						} else {
							return err
						}
					}
					acquiredResources["leaderFailure"][resourceHash1] = heartbeatIdCopy
				}
				var resourceWrite interface{}
				resourceWrite = true
				err = leaderFailure.Get(heartbeatIdCopy).Write(resourceWrite)
				if err != nil {
					distsys.AbortResources(timeoutChecker)
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					for _, r := range acquiredResources["leaderFailure"] {
						distsys.AbortResources(leaderFailure.Get(r))
					}
					if shouldRetry(err) {
						goto monitorLoop
					} else {
						return err
					}
				}
				if _, ok := acquiredResources["electionInProgress"]; !ok {
					acquiredResources["electionInProgress"] = map[uint64]interface{}{}
				}
				resourceHash2 := distsys.Hash(heartbeatIdCopy)
				if _, acquired := acquiredResources["electionInProgress"][resourceHash2]; !acquired {
					err = distsys.AcquireResources(distsys.WRITE_ACCESS, electionInProgress.Get(heartbeatIdCopy))
					if err != nil {
						distsys.AbortResources(timeoutChecker)
						for _, r := range acquiredResources["iAmTheLeader"] {
							distsys.AbortResources(iAmTheLeader.Get(r))
						}
						for _, r := range acquiredResources["electionInProgress"] {
							distsys.AbortResources(electionInProgress.Get(r))
						}
						for _, r := range acquiredResources["leaderFailure"] {
							distsys.AbortResources(leaderFailure.Get(r))
						}
						if shouldRetry(err) {
							goto monitorLoop
						} else {
							return err
						}
					}
					acquiredResources["electionInProgress"][resourceHash2] = heartbeatIdCopy
				}
				var resourceWrite0 interface{}
				resourceWrite0 = true
				err = electionInProgress.Get(heartbeatIdCopy).Write(resourceWrite0)
				if err != nil {
					distsys.AbortResources(timeoutChecker)
					for _, r := range acquiredResources["iAmTheLeader"] {
						distsys.AbortResources(iAmTheLeader.Get(r))
					}
					for _, r := range acquiredResources["electionInProgress"] {
						distsys.AbortResources(electionInProgress.Get(r))
					}
					for _, r := range acquiredResources["leaderFailure"] {
						distsys.AbortResources(leaderFailure.Get(r))
					}
					if shouldRetry(err) {
						goto monitorLoop
					} else {
						return err
					}
				}
			}
		}

		// sleep:
		err = distsys.ReleaseResources(timeoutChecker)
		if err != nil {
			distsys.AbortResources(timeoutChecker)
			for _, r := range acquiredResources["iAmTheLeader"] {
				distsys.AbortResources(iAmTheLeader.Get(r))
			}
			for _, r := range acquiredResources["electionInProgress"] {
				distsys.AbortResources(electionInProgress.Get(r))
			}
			for _, r := range acquiredResources["leaderFailure"] {
				distsys.AbortResources(leaderFailure.Get(r))
			}
			return err
		}
		for _, r := range acquiredResources["iAmTheLeader"] {
			err = distsys.ReleaseResources(iAmTheLeader.Get(r))
			if err != nil {
				distsys.AbortResources(timeoutChecker)
				for _, r0 := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r0))
				}
				for _, r0 := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r0))
				}
				for _, r0 := range acquiredResources["leaderFailure"] {
					distsys.AbortResources(leaderFailure.Get(r0))
				}
				return err
			}
		}
		for _, r := range acquiredResources["electionInProgress"] {
			err = distsys.ReleaseResources(electionInProgress.Get(r))
			if err != nil {
				distsys.AbortResources(timeoutChecker)
				for _, r0 := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r0))
				}
				for _, r0 := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r0))
				}
				for _, r0 := range acquiredResources["leaderFailure"] {
					distsys.AbortResources(leaderFailure.Get(r0))
				}
				return err
			}
		}
		for _, r := range acquiredResources["leaderFailure"] {
			err = distsys.ReleaseResources(leaderFailure.Get(r))
			if err != nil {
				distsys.AbortResources(timeoutChecker)
				for _, r0 := range acquiredResources["iAmTheLeader"] {
					distsys.AbortResources(iAmTheLeader.Get(r0))
				}
				for _, r0 := range acquiredResources["electionInProgress"] {
					distsys.AbortResources(electionInProgress.Get(r0))
				}
				for _, r0 := range acquiredResources["leaderFailure"] {
					distsys.AbortResources(leaderFailure.Get(r0))
				}
				return err
			}
		}
		heartbeatId = heartbeatIdCopy
	sleep:
		acquiredResources = map[string]map[uint64]interface{}{}
		err = distsys.AcquireResources(distsys.READ_ACCESS, monitorFrequency)
		if err != nil {
			if shouldRetry(err) {
				goto sleep
			} else {
				return err
			}
		}
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, sleeper)
		if err != nil {
			if shouldRetry(err) {
				goto sleep
			} else {
				return err
			}
		}
		var resourceWrite interface{}
		var readTemp1 interface{}
		readTemp1, err = monitorFrequency.Read()
		if err != nil {
			distsys.AbortResources(sleeper, monitorFrequency)
			if shouldRetry(err) {
				goto sleep
			} else {
				return err
			}
		}
		resourceWrite = readTemp1
		err = sleeper.Write(resourceWrite)
		if err != nil {
			distsys.AbortResources(sleeper, monitorFrequency)
			if shouldRetry(err) {
				goto sleep
			} else {
				return err
			}
		}
		err = distsys.ReleaseResources(sleeper, monitorFrequency)
		if err != nil {
			distsys.AbortResources(sleeper, monitorFrequency)
			return err
		}
		acquiredResources = map[string]map[uint64]interface{}{}
		heartbeatIdCopy2 := heartbeatId
		heartbeatIdCopy = heartbeatIdCopy2
		err = distsys.AcquireResources(distsys.READ_ACCESS, timeoutChecker)
		if err != nil {
			if shouldRetry(err) {
				goto monitorLoop
			} else {
				return err
			}
		}
	}
	return nil
}
