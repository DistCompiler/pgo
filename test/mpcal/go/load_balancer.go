package load_balancer

import (
	"pgo/distsys"
	"sort"
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
}

func ALoadBalancer(self int, mailboxes distsys.ArchetypeResourceCollection) error {
	var msg []struct {
		key   int
		value int
	}
	next := 0
	var err error
	for {
		if !true {
			break
		}
		err = distsys.AcquireResources(distsys.READ_ACCESS, mailboxes.Get(LoadBalancerId))
		if err != nil {
			return err
		}
		msg = mailboxes.Get(LoadBalancerId).Read().([]struct {
			key   int
			value int
		})
		err = distsys.ReleaseResources(mailboxes.Get(LoadBalancerId))
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(next))
		if err != nil {
			return err
		}
		next = next%NUM_SERVERS + 1
		var resourceWrite interface{}
		key := 2
		index := sort.Search(len(msg), func(i int) bool {
			return !(msg[i].key < key)
		})
		resourceWrite = []int{next, msg[index].value}
		mailboxes.Get(next).Write(resourceWrite)
		err = distsys.ReleaseResources(mailboxes.Get(next))
		if err != nil {
			return err
		}
	}
	return nil
}

func AServer(self int, mailboxes distsys.ArchetypeResourceCollection, page_stream distsys.ArchetypeResource) error {
	var msg []struct {
		key   int
		value interface{}
	}
	var err error
	for {
		if !true {
			break
		}
		err = distsys.AcquireResources(distsys.READ_ACCESS, mailboxes.Get(self))
		if err != nil {
			return err
		}
		msg = mailboxes.Get(self).Read().([]struct {
			key   int
			value interface{}
		})
		err = distsys.ReleaseResources(mailboxes.Get(self))
		if err != nil {
			return err
		}
		key := 2
		index := sort.Search(len(msg), func(i int) bool {
			return !(msg[i].key < key)
		})
		err = distsys.AcquireResources(distsys.READ_ACCESS, page_stream)
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(msg[index].value))
		if err != nil {
			return err
		}
		var resourceWrite interface{}
		resourceWrite = page_stream.Read()
		mailboxes.Get(msg[index].value).Write(resourceWrite)
		err = distsys.ReleaseResources(page_stream, mailboxes.Get(msg[index].value))
		if err != nil {
			return err
		}
	}
	return nil
}

func AClient(self int, mailboxes distsys.ArchetypeResourceCollection, instream distsys.ArchetypeResource, outstream distsys.ArchetypeResource) error {
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
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, mailboxes.Get(LoadBalancerId))
		if err != nil {
			return err
		}
		req = []int{GET_PAGE, self, instream.Read().(int)}
		var resourceWrite interface{}
		resourceWrite = req
		mailboxes.Get(LoadBalancerId).Write(resourceWrite)
		err = distsys.ReleaseResources(instream, mailboxes.Get(LoadBalancerId))
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.READ_ACCESS, mailboxes.Get(self))
		if err != nil {
			return err
		}
		err = distsys.AcquireResources(distsys.WRITE_ACCESS, outstream)
		if err != nil {
			return err
		}
		resp = mailboxes.Get(self).Read()
		var resourceWrite0 interface{}
		resourceWrite0 = resp
		outstream.Write(resourceWrite0)
		err = distsys.ReleaseResources(mailboxes.Get(self), outstream)
		if err != nil {
			return err
		}
	}
	return nil
}