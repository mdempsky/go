// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package noder

import "cmd/compile/internal/types2"

type dupTypes struct {
	origs map[types2.Type]types2.Type
}

func (d *dupTypes) orig(t types2.Type) types2.Type {
	if orig, ok := d.origs[t]; ok {
		return orig
	}
	return t
}

func (d *dupTypes) add(t, orig types2.Type) {
	if t == orig {
		return
	}

	if d.origs == nil {
		d.origs = make(map[types2.Type]types2.Type)
	}
	assert(d.origs[t] == nil)
	d.origs[t] = orig

	switch t := t.(type) {
	case *types2.Pointer:
		orig := orig.(*types2.Pointer)
		d.add(t.Elem(), orig.Elem())

	case *types2.Slice:
		orig := orig.(*types2.Slice)
		d.add(t.Elem(), orig.Elem())

	case *types2.Map:
		orig := orig.(*types2.Map)
		d.add(t.Key(), orig.Key())
		d.add(t.Elem(), orig.Elem())

	case *types2.Array:
		orig := orig.(*types2.Array)
		assert(t.Len() == orig.Len())
		d.add(t.Elem(), orig.Elem())

	case *types2.Chan:
		orig := orig.(*types2.Chan)
		assert(t.Dir() == orig.Dir())
		d.add(t.Elem(), orig.Elem())

	case *types2.Struct:
		orig := orig.(*types2.Struct)
		assert(t.NumFields() == orig.NumFields())
		for i := 0; i < t.NumFields(); i++ {
			d.add(t.Field(i).Type(), orig.Field(i).Type())
		}

	case *types2.Interface:
		orig := orig.(*types2.Interface)
		assert(t.NumExplicitMethods() == orig.NumExplicitMethods())
		assert(t.NumEmbeddeds() == orig.NumEmbeddeds())
		for i := 0; i < t.NumExplicitMethods(); i++ {
			d.add(t.ExplicitMethod(i).Type(), orig.ExplicitMethod(i).Type())
		}
		for i := 0; i < t.NumEmbeddeds(); i++ {
			d.add(t.EmbeddedType(i), orig.EmbeddedType(i))
		}

	case *types2.Signature:
		orig := orig.(*types2.Signature)
		assert((t.Recv() == nil) == (orig.Recv() == nil))
		if t.Recv() != nil {
			d.add(t.Recv().Type(), orig.Recv().Type())
		}
		d.add(t.Params(), orig.Params())
		d.add(t.Results(), orig.Results())

	case *types2.Tuple:
		orig := orig.(*types2.Tuple)
		assert(t.Len() == orig.Len())
		for i := 0; i < t.Len(); i++ {
			d.add(t.At(i).Type(), orig.At(i).Type())
		}

	case *types2.TypeParam:
		orig := orig.(*types2.TypeParam)
		assert(t.Index() == orig.Index())
		// XXX: t.Bound() and orig.Bound() should probably be identical
		// too, but are not for the same reason that we need to
		// deduplicate them here I think.

	default:
		assert(types2.Identical(t, orig))
	}
}
