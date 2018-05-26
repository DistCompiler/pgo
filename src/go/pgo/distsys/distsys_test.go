package distsys

import (
	. "github.com/onsi/ginkgo"
	. "github.com/onsi/gomega"

	"testing"
)

var ownershipTable = NewOwnershipTable(map[string]string{
	"a": "10.10.10.1",
	"b": "10.10.10.2",
	"c": "10.10.10.3",
})

var _ = Describe("OwnershipTable", func() {
	It("panics when you lookup a nonexisting variable", func() {
		invalidVariable := func() {
			ownershipTable.Lookup("invalid-variable")
		}

		Expect(invalidVariable).To(Panic())
	})

	It("returns the owner for a variable in the ownership table", func() {
		Expect(ownershipTable.Lookup("a")).To(Equal("10.10.10.1"))
	})
})

var _ = Describe("BorrowSpec", func() {
	Context("Sorting entries", func() {
		It("Sorts an empty spec", func() {
			spec := BorrowSpec{
				ReadNames:  []string{},
				WriteNames: []string{},
			}

			sorted := spec.Sorted()
			Expect(len(sorted)).To(Equal(0))
		})

		It("Sorts disjoint read and write names", func() {
			spec := BorrowSpec{
				ReadNames:  []string{"a", "c"},
				WriteNames: []string{"d", "b"},
			}

			sorted := spec.Sorted()
			Expect(len(sorted)).To(Equal(4))

			Expect(sorted[0].Name).To(Equal("a"))
			Expect(sorted[0].Exclusive).To(Equal(false))

			Expect(sorted[1].Name).To(Equal("b"))
			Expect(sorted[1].Exclusive).To(Equal(true))

			Expect(sorted[2].Name).To(Equal("c"))
			Expect(sorted[2].Exclusive).To(Equal(false))

			Expect(sorted[3].Name).To(Equal("d"))
			Expect(sorted[3].Exclusive).To(Equal(true))
		})

		It("Sorts read and write names with non-empty intersections", func() {
			spec := BorrowSpec{
				ReadNames:  []string{"b", "a"},
				WriteNames: []string{"c", "b"},
			}

			sorted := spec.Sorted()
			Expect(len(sorted)).To(Equal(3))

			Expect(sorted[0].Name).To(Equal("a"))
			Expect(sorted[0].Exclusive).To(Equal(false))

			Expect(sorted[1].Name).To(Equal("b"))
			Expect(sorted[1].Exclusive).To(Equal(true))

			Expect(sorted[2].Name).To(Equal("c"))
			Expect(sorted[2].Exclusive).To(Equal(true))
		})
	})
})

var _ = Describe("GlobalStateOperation", func() {
	Context("Grouping variables", func() {
		It("Groups an empty spec", func() {
			op := GlobalStateOperation{
				spec:      &BorrowSpec{},
				ownership: ownershipTable,
			}

			groups := op.Groups()
			Expect(len(groups)).To(Equal(0))
		})

		It("Groups a spec where no grouping is possible", func() {
			spec := &BorrowSpec{ReadNames: []string{"a", "b", "c"}, WriteNames: []string{"b"}}
			op := GlobalStateOperation{
				spec:      spec,
				ownership: ownershipTable,
			}

			groups := op.Groups()
			Expect(len(groups)).To(Equal(3))

			Expect(groups[0].Peer).To(Equal("10.10.10.1"))
			Expect(len(groups[0].Names)).To(Equal(1))
			Expect(groups[0].Names[0].Name).To(Equal("a"))
			Expect(groups[0].Names[0].Exclusive).To(Equal(false))

			Expect(groups[1].Peer).To(Equal("10.10.10.2"))
			Expect(len(groups[1].Names)).To(Equal(1))
			Expect(groups[1].Names[0].Name).To(Equal("b"))
			Expect(groups[1].Names[0].Exclusive).To(Equal(true))

			Expect(groups[2].Peer).To(Equal("10.10.10.3"))
			Expect(len(groups[2].Names)).To(Equal(1))
			Expect(groups[2].Names[0].Name).To(Equal("c"))
			Expect(groups[2].Names[0].Exclusive).To(Equal(false))
		})

		It("Groups a spec where some grouping of variables is possible", func() {
			spec := &BorrowSpec{ReadNames: []string{"a", "b", "c"}, WriteNames: []string{"b"}}
			op := GlobalStateOperation{
				spec:      spec,
				ownership: ownershipTable,
			}

			// co-locate variables 'a' and 'b'
			ownershipTable.table["b"] = ownershipTable.table["a"]

			groups := op.Groups()
			Expect(len(groups)).To(Equal(2))

			// group 1: 'a' (non-exclusive) and 'b' (exclusive)
			Expect(groups[0].Peer).To(Equal("10.10.10.1"))
			Expect(len(groups[0].Names)).To(Equal(2))
			Expect(groups[0].Names[0].Name).To(Equal("a"))
			Expect(groups[0].Names[0].Exclusive).To(Equal(false))
			Expect(groups[0].Names[1].Name).To(Equal("b"))
			Expect(groups[0].Names[1].Exclusive).To(Equal(true))

			// group 2: 'c' (non-exclusive)
			Expect(groups[1].Peer).To(Equal("10.10.10.3"))
			Expect(len(groups[1].Names)).To(Equal(1))
			Expect(groups[1].Names[0].Name).To(Equal("c"))
			Expect(groups[1].Names[0].Exclusive).To(Equal(false))
		})

		It("Groups a spec where every variable is owned by the same peer", func() {
			spec := &BorrowSpec{ReadNames: []string{"a", "b", "c"}, WriteNames: []string{"b"}}
			op := GlobalStateOperation{
				spec:      spec,
				ownership: ownershipTable,
			}

			// co-locate variables 'a', 'b' and 'c'
			ownershipTable.table["b"] = ownershipTable.table["a"]
			ownershipTable.table["c"] = ownershipTable.table["a"]

			groups := op.Groups()
			Expect(len(groups)).To(Equal(1))

			Expect(groups[0].Peer).To(Equal("10.10.10.1"))
			Expect(len(groups[0].Names)).To(Equal(3))
			Expect(groups[0].Names[0].Name).To(Equal("a"))
			Expect(groups[0].Names[0].Exclusive).To(Equal(false))
			Expect(groups[0].Names[1].Name).To(Equal("b"))
			Expect(groups[0].Names[1].Exclusive).To(Equal(true))
			Expect(groups[0].Names[2].Name).To(Equal("c"))
			Expect(groups[0].Names[2].Exclusive).To(Equal(false))
		})
	})
})

var _ = Describe("VarReferences", func() {
	It("is able to generate a corresponding BorrowSpec", func() {
		refs := VarReferences(map[string]Reference{
			"a": Reference{Value: 10, Exclusive: false},
			"b": Reference{Value: "PGo", Exclusive: true},
			"c": Reference{Value: []int{1, 2, 3}, Exclusive: true},
		})

		spec := refs.ToBorrowSpec()

		Expect(len(spec.ReadNames)).To(Equal(1))
		Expect(spec.ReadNames[0]).To(Equal("a"))

		Expect(len(spec.WriteNames)).To(Equal(2))
		Expect(spec.WriteNames[0]).To(Equal("b"))
		Expect(spec.WriteNames[1]).To(Equal("c"))
	})
})

func TestBorrowSpec(t *testing.T) {
	RegisterFailHandler(Fail)
	RunSpecs(t, "BorrowSpec")
}
