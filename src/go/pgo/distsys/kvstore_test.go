package distsys

import (
	"testing"
)

func TestKVGet(t *testing.T) {
	var value string
	store := &StateServer{data: map[string]string{
		"a": "b",
		"c": "d",
	}}

	err := store.KVGet(GetRequest{Key: "a"}, &value)
	if err != nil {
		t.Errorf("Unexpected error when getting a known key, err = %s", err.Error())
	}
	if value != "b" {
		t.Errorf("Expected b, found %s", value)
	}

	err = store.KVGet(GetRequest{Key: "UnknownKey"}, &value)
	errCode, ok := err.(StateServerError)
	if !ok {
		t.Errorf("Expected StateServerError, found %t", err)
	}
	if errCode != ErrorKeyNotFound {
		t.Errorf("Expected ErrorKeyNotFound, found %d", errCode)
	}
}

func TestKVSet(t *testing.T) {
	var ok bool
	store := &StateServer{data: map[string]string{
		"e": "f",
	}}

	err := store.KVSet(SetRequest{Key: "a", Value: "b"}, &ok)
	if err != nil {
		t.Errorf("Unexpected error when setting a key, err = %s", err.Error())
	}
	if !ok {
		t.Errorf("Unable to set a key")
	}

	err = store.KVSet(SetRequest{Key: "g", Value: "h", PrevUnset: true}, &ok)
	if err != nil {
		t.Errorf("Unexpected error when setting a previously-unset key, err = %s", err.Error())
	}
	if !ok {
		t.Errorf("Unable to set a previously-unset key")
	}

	err = store.KVSet(SetRequest{Key: "a", PrevValue: "b", CheckPrevValue: true, Value: "c"}, &ok)
	if err != nil {
		t.Errorf("Unexpected error when test-and-setting a key, err = %s", err.Error())
	}
	if !ok {
		t.Errorf("Unable to test-and-set a key")
	}

	err = store.KVSet(SetRequest{Key: "a", PrevValue: "b", CheckPrevValue: true, Value: "c"}, &ok)
	errCode, typeOk := err.(StateServerError)
	if !typeOk {
		t.Errorf("Expected StateServerError, found %t", err)
	}
	if errCode != ErrorNoMatch {
		t.Errorf("Expected ErrorNoMatch, found %d", errCode)
	}

	err = store.KVSet(SetRequest{Key: "e", Value: "i", PrevUnset: true}, &ok)
	errCode, typeOk = err.(StateServerError)
	if !typeOk {
		t.Errorf("Expected StateServerError, found %t", err)
	}
	if errCode != ErrorKeyExists {
		t.Errorf("Expected ErrorKeyExists, found %d", errCode)
	}
}

func TestKVDelete(t *testing.T) {
	var ok bool
	store := &StateServer{data: map[string]string{
		"a": "b",
		"c": "d",
		"e": "f",
	}}

	err := store.KVDelete(DeleteRequest{Key: "a"}, &ok)
	if err != nil {
		t.Errorf("Unexpected error when deleting a known key, err = %s", err.Error())
	}
	if !ok {
		t.Errorf("Unable to delete a known key")
	}

	err = store.KVDelete(DeleteRequest{Key: "c", PrevValue: "d", CheckPrevValue: true}, &ok)
	if err != nil {
		t.Errorf("Unexpected error when test-and-deleting a known key, err = %s", err.Error())
	}
	if !ok {
		t.Errorf("Unable to test-and-delete a known key")
	}

	err = store.KVDelete(DeleteRequest{Key: "Unknown"}, &ok)
	errCode, typeOk := err.(StateServerError)
	if !typeOk {
		t.Errorf("Expected StateServerError, found %t", err)
	}
	if errCode != ErrorKeyNotFound {
		t.Errorf("Expected ErrorKeyNotFound, found %d", errCode)
	}

	err = store.KVDelete(DeleteRequest{Key: "e", PrevValue: "WrongValue", CheckPrevValue: true}, &ok)
	errCode, typeOk = err.(StateServerError)
	if !typeOk {
		t.Errorf("Expected StateServerError, found %t", err)
	}
	if errCode != ErrorNoMatch {
		t.Errorf("Expected ErrorNoMatch, found %d", errCode)
	}
}
