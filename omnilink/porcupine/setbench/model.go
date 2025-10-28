package setbench

import (
	"encoding/json"
	"fmt"
	"maps"
	"os"
	"slices"
	"strings"

	"github.com/anishathalye/porcupine"
)

type setbenchState map[int]int

func (state setbenchState) clone() setbenchState {
	fresh := setbenchState{}
	maps.Copy(fresh, state)
	return fresh
}

type KVContains struct {
	Key    int
	Result bool
}

type KVInsert struct {
	Key, Value, Result int
}

type KVInsertIfAbsent struct {
	Key, Value, Result int
}

type KVErase struct {
	Key, Result int
}

type KVRangeQuery struct {
	Lo, Hi, Count int
}

type TerminateThread struct{}

var SetBenchModel = porcupine.Model{
	Init: func() any {
		return setbenchState{}
	},
	Step: func(state, input, output any) (bool, any) {
		stateT, ok := state.(setbenchState)
		if !ok {
			panic(fmt.Errorf("bad cast: %v", state))
		}
		switch input := input.(type) {
		case KVContains:
			_, contains := stateT[input.Key]
			return (input.Result == contains), stateT
		case KVInsert:
			stateCopy := stateT.clone()
			orig := stateCopy[input.Key]
			stateCopy[input.Key] = input.Value
			return (input.Result == orig), stateCopy
		case KVInsertIfAbsent:
			stateCopy := stateT.clone()
			orig, ok := stateCopy[input.Key]
			if !ok {
				stateCopy[input.Key] = input.Value
			}
			return (input.Result == orig), stateCopy
		case KVErase:
			stateCopy := stateT.clone()
			orig := stateCopy[input.Key]
			delete(stateCopy, input.Key)
			return (input.Result == orig), stateCopy
		case KVRangeQuery:
			Count := 0
			for k := range stateT {
				if input.Lo <= k && k <= input.Hi {
					Count++
				}
			}
			return (input.Count == Count), stateT
		case TerminateThread:
			return true, stateT
		default:
			panic(fmt.Errorf("unrecognized input: %v", input))
		}
	},
	Equal: func(state1, state2 any) bool {
		s1 := state1.(setbenchState)
		s2 := state2.(setbenchState)
		return maps.Equal(s1, s2)
	},
	DescribeState: func(state any) string {
		stateT := state.(setbenchState)
		var keys []int
		for k := range stateT {
			keys = append(keys, k)
		}
		slices.Sort(keys)
		var builder strings.Builder
		builder.WriteString("[")
		init := true
		for _, k := range keys {
			if !init {
				builder.WriteString(", ")
			}
			fmt.Fprintf(&builder, "%v: %v", k, stateT[k])
			init = false
		}
		builder.WriteString("]")
		return builder.String()
	},
	DescribeOperation: func(input, output any) string {
		switch input := input.(type) {
		case KVContains:
			return fmt.Sprintf("KVContains(%v, %v)", input.Key, input.Result)
		case KVInsert:
			return fmt.Sprintf("KVInsert(%v, %v, %v)", input.Key, input.Value, input.Result)
		case KVInsertIfAbsent:
			return fmt.Sprintf("KVInsertIfAbsent(%v, %v, %v)", input.Key, input.Value, input.Result)
		case KVErase:
			return fmt.Sprintf("KVErase(%v, %v)", input.Key, input.Result)
		case KVRangeQuery:
			return fmt.Sprintf("KVRangeQuery(%v, %v, %v)", input.Lo, input.Hi, input.Count)
		case TerminateThread:
			return "TerminateThread()"
		case nil:
			return "<nil>"
		default:
			panic(fmt.Errorf("unrecognized input: %v", input))
		}
	},
}

func LoadOperations(path string) ([]porcupine.Operation, error) {
	reader, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	decoder := json.NewDecoder(reader)
	var ops []porcupine.Operation = nil
	err = decoder.Decode(&ops)
	if err != nil {
		return nil, err
	}

	// Reconstruct type info on what the input was
	for i := range ops {
		opJS, ok := ops[i].Input.(map[string]any)
		if !ok {
			panic(fmt.Errorf("Bad input: %v", ops[i].Input))
		}
		operation_name, ok := opJS["operation_name"].(string)
		if !ok {
			panic(fmt.Errorf("Bad input: %v", ops[i].Input))
		}
		bytes, err := json.Marshal(opJS)
		if err != nil {
			panic(err)
		}
		switch operation_name {
		case "KVContains":
			var op KVContains
			err = json.Unmarshal(bytes, &op)
			if err != nil {
				panic(err)
			}
			ops[i].Input = op
		case "KVInsert":
			var op KVInsert
			err = json.Unmarshal(bytes, &op)
			if err != nil {
				panic(err)
			}
			ops[i].Input = op
		case "KVInsertIfAbsent":
			var op KVInsertIfAbsent
			err = json.Unmarshal(bytes, &op)
			if err != nil {
				panic(err)
			}
			ops[i].Input = op
		case "KVErase":
			var op KVErase
			err = json.Unmarshal(bytes, &op)
			if err != nil {
				panic(err)
			}
			ops[i].Input = op
		case "KVRangeQuery":
			var op KVRangeQuery
			err = json.Unmarshal(bytes, &op)
			if err != nil {
				panic(err)
			}
			ops[i].Input = op
		case "__TerminateThread":
			var op TerminateThread
			err = json.Unmarshal(bytes, &op)
			if err != nil {
				panic(err)
			}
			ops[i].Input = op
		}
	}

	return ops, nil
}
