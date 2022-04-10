package branchtest_tla_gotests

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"testing"
)

func TestLOCALARCHETYPERESOURCE(t *testing.T) {
	resource1 := distsys.LocalArchetypeResourceMaker(tla.MakeTLANumber(22)).Make()

	val1, err := resource1.ReadValue()
	if err != nil {
		t.Errorf("Error: %v", err)
	} else if val1 != tla.MakeTLANumber(22) {
		t.Errorf("expected to read value 22, got %v", val1)
	}

	resource1.WriteValue(tla.MakeTLAString("hello world"))
	val2, err := resource1.ReadValue()
	if err != nil {
		t.Errorf("Error: %v", err)
	} else if val2 != tla.MakeTLAString("hello world") {
		t.Errorf("expected to read value 22, got %v", val2)
	}

	resource2, err := resource1.ForkState()
	val3, err := resource2.ReadValue()
	if err != nil {
		t.Errorf("expected to read value, got %v", err)
	} else if val3 != tla.MakeTLAString("hello world") {
		t.Errorf("expected to read value 22, got %v", val3)
	}

	resource2.WriteValue(tla.MakeTLAString("goodbye world"))
	val4, err := resource2.ReadValue()
	val5, err := resource1.ReadValue()
	if err != nil {
		t.Errorf("expected to read value, got %v", err)
	} else if val4 != tla.MakeTLAString("goodbye world") {
		t.Errorf("expected to read value goodbye world, got %v", val4)
	} else if val5 != tla.MakeTLAString("hello world") {
		t.Errorf("expected to read value hello world, got %v", val5)
	}

	fmt.Println(resource1)
	fmt.Println(resource2)

	err = resource2.LinkState()
	if err != nil {
		fmt.Println(err)
	}

	fmt.Println(resource1)
	fmt.Println(resource2)

	resource2.Commit()
}

func TestTCPMAILBOXES(t *testing.T) {
	mailbox1 := resources.TCPMailboxesMaker(func(index tla.TLAValue) (resources.MailboxKind, string) {
		switch index.AsNumber() {
		case 1:
			return resources.MailboxesLocal, "localhost:8001"
		case 2:
			return resources.MailboxesRemote, "localhost:8002"
		default:
			panic(fmt.Errorf("unknown mailbox index %v", index))
		}
	}).Make()

	fmt.Println(mailbox1)

	//val, err := mailbox1.ReadValue()
	//if err != nil {
	//	fmt.Println(err)
	//}
	//fmt.Println(val)

	//time.Sleep(5000)
}

//
//func TestSTART(t *testing.T) {
//	mailbox := resources.TCPMailboxesMaker(func(index tla.TLAValue) (resources.MailboxKind, string) {
//		switch index.AsNumber() {
//		case 1:
//			return resources.MailboxesLocal, "localhost:8001"
//		case 2:
//			return resources.MailboxesRemote, "localhost:8002"
//		default:
//			panic(fmt.Errorf("unknown mailbox index %v", index))
//		}
//	}).Make()
//
//	mailbox.WriteValue(tla.MakeTLANumber(22))
//	val, err := mailbox.ReadValue()
//	if err != nil {
//		t.Errorf("expected to read value, got %v", err)
//	}
//	fmt.Println(val)
//
//}
