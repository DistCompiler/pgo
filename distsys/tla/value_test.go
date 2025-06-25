package tla

import (
	"bytes"
	"encoding/gob"
	"testing"
)

func TestTLAModel(t *testing.T) {
	type Record struct {
		Name           string
		Operation      func() Value
		ExpectedResult string
	}

	tests := []Record{
		{
			Name: "Seq({})",
			Operation: func() Value {
				return ModuleSeq(MakeSet())
			},
			ExpectedResult: "{<<>>}",
		},
		{
			Name: "\\E foo \\in {} : TRUE",
			Operation: func() Value {
				return QuantifiedExistential([]Value{MakeSet()}, func([]Value) bool {
					return true
				})
			},
			ExpectedResult: "FALSE",
		},
		{
			Name: "[x \\in {} |-> x]",
			Operation: func() Value {
				return MakeRecord(nil)
			},
			ExpectedResult: "[x \\in {} |-> x]",
		},
		{
			Name: "[x \\in {1, 2, 3} |-> x + 1]",
			Operation: func() Value {
				return MakeFunction(
					[]Value{MakeSet(MakeNumber(1), MakeNumber(2), MakeNumber(3))},
					func(v []Value) Value {
						return ModulePlusSymbol(v[0], MakeNumber(1))
					},
				)
			},
			ExpectedResult: "((1) :> (2) @@ (2) :> (3) @@ (3) :> (4))",
		},
		{
			Name: "1 .. 3",
			Operation: func() Value {
				return ModuleDotDotSymbol(MakeNumber(1), MakeNumber(4))
			},
			ExpectedResult: "{1, 2, 3, 4}",
		},
		{
			Name: "function over empty set short-circuit",
			Operation: func() Value {
				return MakeFunction([]Value{MakeSet(MakeNumber(12)), MakeSet()}, func([]Value) Value {
					panic("should not be called")
				})
			},
			ExpectedResult: "[x \\in {} |-> x]",
		},
		{
			Name: "\"foo\"",
			Operation: func() Value {
				return MakeString("foo")
			},
			ExpectedResult: "\"foo\"",
		},
		{
			Name:           "TRUE",
			Operation:      func() Value { return ModuleTRUE },
			ExpectedResult: "TRUE",
		},
		{
			Name: "[k |-> 1] @@ [k |-> 2]",
			Operation: func() Value {
				return ModuleDoubleAtSignSymbol(
					MakeRecord([]RecordField{{MakeString("k"), MakeNumber(1)}}),
					MakeRecord([]RecordField{{MakeString("k"), MakeNumber(2)}}),
				)
			},
			ExpectedResult: "((\"k\") :> (1))",
		},
	}

	for _, test := range tests {
		t.Run(test.Name, func(t *testing.T) {
			actualValue := test.Operation()
			actualStr := actualValue.String()
			if actualStr != test.ExpectedResult {
				t.Errorf("result %s did not equal expected value %s", actualStr, test.ExpectedResult)
			}
		})
	}

	for _, test := range tests {
		t.Run(".gob "+test.Name, func(t *testing.T) {
			valueBefore := test.Operation()
			var buf bytes.Buffer
			encoder := gob.NewEncoder(&buf)
			err := encoder.Encode(&valueBefore)
			if err != nil {
				t.Error(err)
			}
			decoder := gob.NewDecoder(&buf)
			var valueAfter Value
			err = decoder.Decode(&valueAfter)
			if err != nil {
				t.Error(err)
			}
			if !valueBefore.Equal(valueAfter) {
				t.Errorf("%v was not equal to reparsed %v", valueBefore, valueAfter)
			}
		})
	}
}
