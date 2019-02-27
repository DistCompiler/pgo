package load_balancer

import (
	"pgo/distsys"
)

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
}

func ALoadBalancer(self int, mailboxes []distsys.ArchetypeResource) error {
	var msg map[string]interface{}
	next := 0
	var err error
	for {
		if !true {
			break
		}
		err = distsys.AcquireResources(distsys.READ_ACCESS, mailboxes[LoadBalancerId])
		if err != nil {
			return err
		}
		msg = mailboxes[LoadBalancerId].Read().(map[string]interface{})
		err = distsys.ReleaseResources(mailboxes[LoadBalancerId])
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes[next])
		if err != nil {
			return err
		}
		next = next%NUM_SERVERS + 1
		var resourceWrite interface{}
		resourceWrite = map[string]interface{}{
			"message_id": next,
			"client_id":  msg["client_id"],
		}
		mailboxes[next].Write(resourceWrite)
		err = distsys.ReleaseResources(mailboxes[next])
		if err != nil {
			return err
		}
	}
	return nil
}

func AServer(self int, mailboxes []distsys.ArchetypeResource, page_stream distsys.ArchetypeResource) error {
	var msg map[string]interface{}
	var err error
	for {
		if !true {
			break
		}
		err = distsys.AcquireResources(distsys.READ_ACCESS, mailboxes[self])
		if err != nil {
			return err
		}
		msg = mailboxes[self].Read().(map[string]interface{})
		err = distsys.ReleaseResources(mailboxes[self])
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.READ_ACCESS, page_stream)
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes[msg["client_id"].(int)])
		if err != nil {
			return err
		}
		var resourceWrite interface{}
		resourceWrite = page_stream.Read()
		mailboxes[msg["client_id"].(int)].Write(resourceWrite)
		err = distsys.ReleaseResources(page_stream, mailboxes[msg["client_id"].(int)])
		if err != nil {
			return err
		}
	}
	return nil
}

func AClient(self int, mailboxes []distsys.ArchetypeResource, instream distsys.ArchetypeResource, outstream distsys.ArchetypeResource) error {
	var req map[string]interface{}
	var resp interface{}
	var err error
	for {
		if !true {
			break
		}
		err = distsys.AcquireResources(distsys.READ_ACCESS, instream)
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes[LoadBalancerId])
		if err != nil {
			return err
		}
		req = map[string]interface{}{
			"message_type": GET_PAGE,
			"instream":     instream.Read(),
			"client_id":    self,
		}
		var resourceWrite interface{}
		resourceWrite = req
		mailboxes[LoadBalancerId].Write(resourceWrite)
		err = distsys.ReleaseResources(instream, mailboxes[LoadBalancerId])
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.READ_ACCESS, mailboxes[self])
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, outstream)
		if err != nil {
			return err
		}
		resp = mailboxes[self].Read()
		var resourceWrite0 interface{}
		resourceWrite0 = resp
		outstream.Write(resourceWrite0)
		err = distsys.ReleaseResources(mailboxes[self], outstream)
		if err != nil {
			return err
		}
	}
	return nil
}
