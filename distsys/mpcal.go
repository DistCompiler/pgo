package distsys

func WhileCatchingPanics(fns ...func() TLAValue) (result []TLAValue, err error) {
	defer func() {
		if r := recover(); r != nil {
			result = nil
			err = r.(error)
		}
	}()
	for _, fn := range fns {
		result = append(result, fn())
	}
	return
}

type PCalSectionContext struct {
	resources []ArchetypeResource
}

func NewPCalSectionContext() *PCalSectionContext {
	return &PCalSectionContext{}
}

func (ctx *PCalSectionContext) recordResource(res ArchetypeResource) {
	for _, existingRes := range ctx.resources {
		if existingRes == res {
			return
		}
	}
	ctx.resources = append(ctx.resources, res)
}

func (ctx *PCalSectionContext) Abort() {
	for i := len(ctx.resources) - 1; i >= 0; i-- {
		ctx.resources[i].Abort()
	}
}

func (ctx *PCalSectionContext) Commit() (err error) {
	for i := len(ctx.resources) - 1; i >= 0; i-- {
		err = ctx.resources[i].PreCommit()
		if err != nil {
			break
		}
	}
	if err != nil {
		for i := len(ctx.resources) - 1; i >= 0; i-- {
			ctx.resources[i].Abort()
		}
	} else {
		for i := len(ctx.resources) - 1; i >= 0; i-- {
			ctx.resources[i].Commit()
		}
	}
	return
}

func (ctx *PCalSectionContext) Write(resource ArchetypeResource, indices []TLAValue, value TLAValue) error {
	ctx.recordResource(resource)
	if len(indices) == 0 {
		return resource.WriteValue(value)
	} else {
		resAtIndex, err := resource.Index(indices[0])
		if err != nil {
			return err
		}
		return ctx.Write(resAtIndex, indices[1:], value)
	}
}

func (ctx *PCalSectionContext) Read(resource ArchetypeResource, indices []TLAValue) TLAValue {
	ctx.recordResource(resource)
	if len(indices) == 0 {
		value, err := resource.ReadValue()
		if err != nil {
			panic(err)
		}
		return value
	} else {
		resAtIndex, err := resource.Index(indices[0])
		if err != nil {
			panic(err)
		}
		return ctx.Read(resAtIndex, indices[1:])
	}
}
