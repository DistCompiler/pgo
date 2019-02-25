package load_balancer

import (
	"pgo/distsys"
)

var BUFFER_SIZE int

var GET_PAGE int

var LoadBalancerId int

var NUM_CLIENTS int

var NUM_SERVERS int

var WEB_PAGE int

func init() {
	BUFFER_SIZE = 3
	GET_PAGE = 200
	LoadBalancerId = 0
	NUM_CLIENTS = 1
	NUM_SERVERS = 2
	WEB_PAGE = 42
}

func ALoadBalancer(self int, mailboxes []distsys.ArchetypeResource) error {
	var msg []int
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
		msg = mailboxes[LoadBalancerId].Read().([]int)
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
		resourceWrite = []int{next, msg[2-1]}
		mailboxes[next].Write(resourceWrite)
		err = distsys.ReleaseResources(mailboxes[next])
		if err != nil {
			return err
		}
	}
	return nil
}

func AServer(self int, mailboxes []distsys.ArchetypeResource, page_stream distsys.ArchetypeResource) error {
	var msg []int
	var err error
	for {
		if !true {
			break
		}
		err = distsys.AcquireResources(distsys.READ_ACCESS, mailboxes[self])
		if err != nil {
			return err
		}
		msg = mailboxes[self].Read().([]int)
		err = distsys.ReleaseResources(mailboxes[self])
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.READ_ACCESS, page_stream)
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes[msg[2-1]])
		if err != nil {
			return err
		}
		var resourceWrite interface{}
		resourceWrite = page_stream.Read()
		mailboxes[msg[2-1]].Write(resourceWrite)
		err = distsys.ReleaseResources(page_stream, mailboxes[msg[2-1]])
		if err != nil {
			return err
		}
	}
	return nil
}

func AClient(self int, mailboxes []distsys.ArchetypeResource, instream distsys.ArchetypeResource, outstream distsys.ArchetypeResource) error {
	var req []int
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
		req = []int{GET_PAGE, self, instream.Read().(int)}
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
