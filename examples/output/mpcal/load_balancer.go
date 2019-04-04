package load_balancer

import (
	"fmt"
	"math/rand"
	"pgo/distsys"
	"time"
)

var sleepMin = 100

var sleepMax = 300

var GET_PAGE int

var LoadBalancerId int

var NUM_CLIENTS int

var NUM_SERVERS int

func init() {
	GET_PAGE = 200
	LoadBalancerId = 0
	NUM_CLIENTS = 1
	NUM_SERVERS = 2
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

func ALoadBalancer(self int, mailboxes distsys.ArchetypeResourceCollection) error {
	var msg map[string]interface{}
	next := 0
	var msgCopy map[string]interface{}
	var nextCopy int
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// main:
	acquiredResources = map[string]map[interface{}]bool{}
	for {
		if !true {
			break
		}

		// rcvMsg:
	rcvMsg:
		acquiredResources = map[string]map[interface{}]bool{}
		msgCopy0 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy0[k] = vCopy
		}
		msgCopy = msgCopy0
		if _, ok := acquiredResources["mailboxes"]; !ok {
			acquiredResources["mailboxes"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["mailboxes"][LoadBalancerId]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, mailboxes.Get(LoadBalancerId))
			if err != nil {
				for r, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto rcvMsg
				} else {
					return err
				}
			}
			acquiredResources["mailboxes"][LoadBalancerId] = true
		}
		var readTemp interface{}
		readTemp, err = mailboxes.Get(LoadBalancerId).Read()
		if err != nil {
			for r, _ := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			if shouldRetry(err) {
				goto rcvMsg
			} else {
				return err
			}
		}
		msgCopy = readTemp.(map[string]interface{})
		if !(msgCopy["message_type"].(int) == GET_PAGE) {
			panic("((msg).message_type) = (GET_PAGE)")
		}
		for r, _ := range acquiredResources["mailboxes"] {
			err = distsys.ReleaseResources(mailboxes.Get(r))
			if err != nil {
				for r0, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		msg = msgCopy

		// sendServer:
	sendServer:
		acquiredResources = map[string]map[interface{}]bool{}
		msgCopy1 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy1[k] = vCopy
		}
		msgCopy = msgCopy1
		nextCopy0 := next
		nextCopy = nextCopy0
		nextCopy = nextCopy%NUM_SERVERS + 1
		if _, ok := acquiredResources["mailboxes"]; !ok {
			acquiredResources["mailboxes"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["mailboxes"][nextCopy]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(nextCopy))
			if err != nil {
				for r, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto sendServer
				} else {
					return err
				}
			}
			acquiredResources["mailboxes"][nextCopy] = true
		}
		var resourceWrite interface{}
		resourceWrite = map[string]interface{}{
			"path":       msgCopy["path"],
			"message_id": nextCopy,
			"client_id":  msgCopy["client_id"],
		}
		err = mailboxes.Get(nextCopy).Write(resourceWrite)
		if err != nil {
			for r, _ := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			if shouldRetry(err) {
				goto sendServer
			} else {
				return err
			}
		}
		for r, _ := range acquiredResources["mailboxes"] {
			err = distsys.ReleaseResources(mailboxes.Get(r))
			if err != nil {
				for r0, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		msg = msgCopy
		next = nextCopy
		acquiredResources = map[string]map[interface{}]bool{}
	}
	return nil
}

func AServer(self int, mailboxes distsys.ArchetypeResourceCollection, file_system distsys.ArchetypeResourceCollection) error {
	var msg map[string]interface{}
	var msgCopy map[string]interface{}
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// serverLoop:
	acquiredResources = map[string]map[interface{}]bool{}
	for {
		if !true {
			break
		}

		// rcvReq:
	rcvReq:
		acquiredResources = map[string]map[interface{}]bool{}
		msgCopy0 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy0[k] = vCopy
		}
		msgCopy = msgCopy0
		if _, ok := acquiredResources["mailboxes"]; !ok {
			acquiredResources["mailboxes"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["mailboxes"][self]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, mailboxes.Get(self))
			if err != nil {
				for r, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto rcvReq
				} else {
					return err
				}
			}
			acquiredResources["mailboxes"][self] = true
		}
		var readTemp interface{}
		readTemp, err = mailboxes.Get(self).Read()
		if err != nil {
			for r, _ := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			if shouldRetry(err) {
				goto rcvReq
			} else {
				return err
			}
		}
		msgCopy = readTemp.(map[string]interface{})
		for r, _ := range acquiredResources["mailboxes"] {
			err = distsys.ReleaseResources(mailboxes.Get(r))
			if err != nil {
				for r0, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		msg = msgCopy

		// sendPage:
	sendPage:
		acquiredResources = map[string]map[interface{}]bool{}
		msgCopy1 := make(map[string]interface{}, len(msg))
		for k, v := range msg {
			vCopy := v
			msgCopy1[k] = vCopy
		}
		msgCopy = msgCopy1
		if _, ok := acquiredResources["mailboxes"]; !ok {
			acquiredResources["mailboxes"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["mailboxes"][msgCopy["client_id"].(int)]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(msgCopy["client_id"].(int)))
			if err != nil {
				for r, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto sendPage
				} else {
					return err
				}
			}
			acquiredResources["mailboxes"][msgCopy["client_id"].(int)] = true
		}
		var resourceWrite interface{}
		if _, ok := acquiredResources["file_system"]; !ok {
			acquiredResources["file_system"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["file_system"][msgCopy["path"]]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, file_system.Get(msgCopy["path"]))
			if err != nil {
				for r, _ := range acquiredResources["file_system"] {
					distsys.AbortResources(file_system.Get(r))
				}
				for r, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto sendPage
				} else {
					return err
				}
			}
			acquiredResources["file_system"][msgCopy["path"]] = true
		}
		var readTemp0 interface{}
		readTemp0, err = file_system.Get(msgCopy["path"]).Read()
		if err != nil {
			for r, _ := range acquiredResources["file_system"] {
				distsys.AbortResources(file_system.Get(r))
			}
			for r, _ := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			if shouldRetry(err) {
				goto sendPage
			} else {
				return err
			}
		}
		resourceWrite = readTemp0
		err = mailboxes.Get(msgCopy["client_id"].(int)).Write(resourceWrite)
		if err != nil {
			for r, _ := range acquiredResources["file_system"] {
				distsys.AbortResources(file_system.Get(r))
			}
			for r, _ := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			if shouldRetry(err) {
				goto sendPage
			} else {
				return err
			}
		}
		for r, _ := range acquiredResources["file_system"] {
			err = distsys.ReleaseResources(file_system.Get(r))
			if err != nil {
				for r0, _ := range acquiredResources["file_system"] {
					distsys.AbortResources(file_system.Get(r0))
				}
				for r0, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		for r, _ := range acquiredResources["mailboxes"] {
			err = distsys.ReleaseResources(mailboxes.Get(r))
			if err != nil {
				for r0, _ := range acquiredResources["file_system"] {
					distsys.AbortResources(file_system.Get(r0))
				}
				for r0, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		msg = msgCopy
		acquiredResources = map[string]map[interface{}]bool{}
	}
	return nil
}

func AClient(self int, mailboxes distsys.ArchetypeResourceCollection, instream distsys.ArchetypeResource, outstream distsys.ArchetypeResource) error {
	var req map[string]interface{}
	var resp interface{}
	var reqCopy map[string]interface{}
	var respCopy interface{}
	var err error
	var acquiredResources map[string]map[interface{}]bool

	// clientLoop:
	acquiredResources = map[string]map[interface{}]bool{}
	for {
		if !true {
			break
		}

		// clientRequest:
	clientRequest:
		acquiredResources = map[string]map[interface{}]bool{}
		reqCopy0 := make(map[string]interface{}, len(req))
		for k, v := range req {
			vCopy := v
			reqCopy0[k] = vCopy
		}
		reqCopy = reqCopy0
		err = distsys.AcquireResources(distsys.READ_ACCESS, instream)
		if err != nil {
			if shouldRetry(err) {
				goto clientRequest
			} else {
				return err
			}
		}
		var readTemp interface{}
		readTemp, err = instream.Read()
		if err != nil {
			distsys.AbortResources(instream)
			if shouldRetry(err) {
				goto clientRequest
			} else {
				return err
			}
		}
		reqCopy = map[string]interface{}{
			"path":         readTemp,
			"message_type": GET_PAGE,
			"client_id":    self,
		}
		if _, ok := acquiredResources["mailboxes"]; !ok {
			acquiredResources["mailboxes"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["mailboxes"][LoadBalancerId]; !acquired {
			err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(LoadBalancerId))
			if err != nil {
				distsys.AbortResources(instream)
				for r, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto clientRequest
				} else {
					return err
				}
			}
			acquiredResources["mailboxes"][LoadBalancerId] = true
		}
		var resourceWrite interface{}
		resourceWrite = reqCopy
		err = mailboxes.Get(LoadBalancerId).Write(resourceWrite)
		if err != nil {
			distsys.AbortResources(instream)
			for r, _ := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			if shouldRetry(err) {
				goto clientRequest
			} else {
				return err
			}
		}
		err = distsys.ReleaseResources(instream)
		if err != nil {
			distsys.AbortResources(instream)
			for r, _ := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			return err
		}
		for r, _ := range acquiredResources["mailboxes"] {
			err = distsys.ReleaseResources(mailboxes.Get(r))
			if err != nil {
				distsys.AbortResources(instream)
				for r0, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		req = reqCopy

		// clientReceive:
	clientReceive:
		acquiredResources = map[string]map[interface{}]bool{}
		respCopy0 := resp
		respCopy = respCopy0
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, outstream)
		if err != nil {
			if shouldRetry(err) {
				goto clientReceive
			} else {
				return err
			}
		}
		if _, ok := acquiredResources["mailboxes"]; !ok {
			acquiredResources["mailboxes"] = map[interface{}]bool{}
		}
		if _, acquired := acquiredResources["mailboxes"][self]; !acquired {
			err = distsys.AcquireResources(distsys.READ_ACCESS, mailboxes.Get(self))
			if err != nil {
				distsys.AbortResources(outstream)
				for r, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r))
				}
				if shouldRetry(err) {
					goto clientReceive
				} else {
					return err
				}
			}
			acquiredResources["mailboxes"][self] = true
		}
		var readTemp0 interface{}
		readTemp0, err = mailboxes.Get(self).Read()
		if err != nil {
			distsys.AbortResources(outstream)
			for r, _ := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			if shouldRetry(err) {
				goto clientReceive
			} else {
				return err
			}
		}
		respCopy = readTemp0
		var resourceWrite0 interface{}
		resourceWrite0 = respCopy
		err = outstream.Write(resourceWrite0)
		if err != nil {
			distsys.AbortResources(outstream)
			for r, _ := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			if shouldRetry(err) {
				goto clientReceive
			} else {
				return err
			}
		}
		err = distsys.ReleaseResources(outstream)
		if err != nil {
			distsys.AbortResources(outstream)
			for r, _ := range acquiredResources["mailboxes"] {
				distsys.AbortResources(mailboxes.Get(r))
			}
			return err
		}
		for r, _ := range acquiredResources["mailboxes"] {
			err = distsys.ReleaseResources(mailboxes.Get(r))
			if err != nil {
				distsys.AbortResources(outstream)
				for r0, _ := range acquiredResources["mailboxes"] {
					distsys.AbortResources(mailboxes.Get(r0))
				}
				return err
			}
		}
		resp = respCopy
		acquiredResources = map[string]map[interface{}]bool{}
	}
	return nil
}
