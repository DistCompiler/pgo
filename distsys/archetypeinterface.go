package distsys

import (
	"fmt"
	"github.com/benbjohnson/immutable"
)

type ArchetypeInterface struct {
	ctx *MPCalContext
}

func (iface ArchetypeInterface) Self() TLAValue {
	return iface.ctx.self
}

func (iface ArchetypeInterface) ensureCriticalSectionWith(handle ArchetypeResourceHandle) {
	iface.ctx.dirtyResourceHandles[handle] = true
}

func (iface ArchetypeInterface) Write(handle ArchetypeResourceHandle, indices []TLAValue, value TLAValue) (err error) {
	iface.ensureCriticalSectionWith(handle)
	res := iface.ctx.getResourceByHandle(handle)
	for _, index := range indices {
		res, err = res.Index(index)
		if err != nil {
			return
		}
	}
	err = res.WriteValue(value)
	return
}

func (iface ArchetypeInterface) Read(handle ArchetypeResourceHandle, indices []TLAValue) (value TLAValue, err error) {
	iface.ensureCriticalSectionWith(handle)
	res := iface.ctx.getResourceByHandle(handle)
	for _, index := range indices {
		res, err = res.Index(index)
		if err != nil {
			return
		}
	}
	value, err = res.ReadValue()
	return
}

func (iface ArchetypeInterface) Fairness(id string, ceiling int) int {
	fairnessCounters := iface.ctx.fairnessCounters
	counter := fairnessCounters[id]
	var nextCounter int
	if counter >= ceiling - 1 {
		nextCounter = 0
	} else {
		nextCounter = counter + 1
	}
	fairnessCounters[id] = nextCounter
	return counter
}

func (iface ArchetypeInterface) GetConstant(name string) func(args... TLAValue) TLAValue {
	fn, wasFound := iface.ctx.constantDefns[name]
	if !wasFound {
		panic(fmt.Errorf("could not find constant definition %s", name))
	}
	return fn
}

func (iface ArchetypeInterface) RequireArchetypeResource(name string) ArchetypeResourceHandle {
	handle := ArchetypeResourceHandle(name)
	_ = iface.ctx.getResourceByHandle(handle)
	return handle
}

func (iface ArchetypeInterface) RequireArchetypeResourceRef(name string) (ArchetypeResourceHandle, error) {
	ptr := iface.RequireArchetypeResource(name)
	ptrVal, err := iface.Read(ptr, nil)
	if err != nil {
		return "", err
	}
	return iface.RequireArchetypeResource(ptrVal.AsString()), nil
}

func (iface ArchetypeInterface) EnsureArchetypeResourceLocal(name string, value TLAValue) {
	_ = iface.ctx.ensureArchetypeResource(name, LocalArchetypeResourceMaker(value))
}

func (iface ArchetypeInterface) ReadArchetypeResourceLocal(name string) TLAValue {
	return iface.ctx.getResourceByHandle(ArchetypeResourceHandle(name)).(*LocalArchetypeResource).value
}

func (iface ArchetypeInterface) getCriticalSection(name string) MPCalCriticalSection {
	if criticalSection, ok := iface.ctx.jumpTable[name]; ok {
		return criticalSection
	}
	panic(fmt.Errorf("could not find critical section %s", name))
}


func (iface ArchetypeInterface) getProc(name string) MPCalProc {
	if proc, ok := iface.ctx.procTable[name]; ok {
		return proc
	}
	panic(fmt.Errorf("could not find procedure %s", name))
}

var defaultLocalArchetypeResourceMaker = LocalArchetypeResourceMaker(TLAValue{})

func (iface ArchetypeInterface) ensureArchetypeResourceLocal(name string) ArchetypeResourceHandle {
	return iface.ctx.ensureArchetypeResource(name, defaultLocalArchetypeResourceMaker)
}

func (iface ArchetypeInterface) Goto(target string) error {
	_ = iface.getCriticalSection(target) // crash now if the new pc isn't in the jump table
	pc := iface.RequireArchetypeResource(".pc")
	return iface.Write(pc, nil, NewTLAString(target))
}

func (iface ArchetypeInterface) Call(procName string, returnPC string, argVals... TLAValue) error {
	proc := iface.getProc(procName)
	stack := iface.RequireArchetypeResource(".stack")
	stackVal, err := iface.Read(stack, nil)
	if err != nil {
		return err
	}

	if len(argVals) > len(proc.StateVars) {
		panic(fmt.Errorf("too many arguments when calling procedure %s", proc.Name))
	}

	// store all the callee's locals into the stack, to avoid clobbering them while the procedure runs
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	builder.Set(NewTLAString(".pc"), NewTLAString(returnPC)) // store return address
	for argIdx, argVarName := range proc.StateVars {
		argHandle := iface.ensureArchetypeResourceLocal(argVarName)

		// save original argument value
		argVal, err := iface.Read(argHandle, nil)
		if err != nil {
			return err
		}
		builder.Set(NewTLAString(argVarName), argVal)

		// write the argument value into callee state (if we are still dealing with args; extra state vars are not args)
		if argIdx < len(argVals) {
			err = iface.Write(argHandle, nil, argVals[argIdx])
			if err != nil {
				return err
			}
		}
	}
	newStackRecord := TLAValue{&tlaValueFunction{builder.Map()}}

	// push the record onto the stack via tuple concatenation
	err = iface.Write(stack, nil, TLA_OSymbol(NewTLATuple(newStackRecord), stackVal))
	if err != nil {
		return err
	}

	// perform the preamble, which will set up any initial state variable values caller-side (yes, that is how PCal does it)
	err = proc.PreAmble(iface)
	if err != nil {
		return err
	}

	// finally, jump to procedure start label
	return iface.Goto(proc.Label)
}

func (iface ArchetypeInterface) TailCall(procName string, argVals... TLAValue) error {
	// pull the top-of-stack return address from the initial stack, so we can use it in the tail-call process below
	stack := iface.RequireArchetypeResource(".stack")
	stackVal, err := iface.Read(stack, nil)
	if err != nil {
		return err
	}
	tailPC, ok := stackVal.AsFunction().Get(NewTLAString(".pc"))
	if !ok {
		panic(fmt.Errorf("stack record %v does not contain a program counter (.pc)", stackVal))
	}

	// first, perform a standard return, to ensure that we've dropped our current stack frame and restored
	// all the relevant state variables, as if we really returned
	err = iface.Return()
	if err != nil {
		return err
	}
	// then immediately call out to the tail-call target, both clobbering the PC we just jumped to via return,
	// and preserving it by making it the return target for the call we clobber it with.
	return iface.Call(procName, tailPC.(TLAValue).AsString(), argVals...)
}

func (iface ArchetypeInterface) Return() error {
	stack := iface.RequireArchetypeResource(".stack")
	// rewrite the stack, "popping" one the head element
	stackVal, err := iface.Read(stack, nil)
	if err != nil {
		return err
	}
	err = iface.Write(stack, nil, TLA_Tail(stackVal))
	if err != nil {
		return err
	}

	// each element of the record ("function") at stack head maps a resource name to a resource value,
	// with the associated value being a snapshot of that resource that must be restored
	// this includes the magic .pc resource, which will effectively jump us back to the caller
	headRec := TLA_Head(stackVal)
	headFn := headRec.AsFunction()
	it := headFn.Iterator()
	for !it.Done() {
		name, value := it.Next()
		handle := iface.RequireArchetypeResource(name.(TLAValue).AsString())
		err = iface.Write(handle, nil, value.(TLAValue))
		if err != nil {
			return err
		}
	}
	return nil
}
