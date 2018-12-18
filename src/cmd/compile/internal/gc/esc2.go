// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"fmt"
	"os"
	"strconv"
	"strings"
)

// If oldEscCompat is true, we try to be more compatible with esc.go's
// quirks.
// TODO(mdempsky): Remove.
const oldEscCompat = true

// If esc2Live is true, then esc2.go drives escape analysis instead of
// esc.go.
const esc2Live = false

// TODO(mdempsky): Document how to write and maintain code.
//
// In particular, it's important to always visit the entire AST. That
// is, you have to write something like:
//
//    if x {
//        e.discard(n.Left)
//    } else {
//        e.value(k, n.Left)
//    }
//
// Rather than just "if !x { e.value(k, n.Left) }".

// TODO(mdempsky): esc.go marks reflect.Value.Pointer and
// reflect.Value.UnsafeAddr's receiver params as esc:0x12 because it
// flows to the result as a uintptr, but we mark it as esc:0x1 here.

func (e *EscState) stmt(n *Node) {
	if n == nil {
		return
	}

	lno := setlineno(n)
	defer func() {
		lineno = lno
	}()

	if Debug['m'] > 2 {
		fmt.Printf("%v:[%d] %v stmt: %v\n", linestr(lineno), e.loopdepth, funcSym(Curfn), n)
	}

	// ninit logically runs at a different loopdepth than the rest of the for loop.
	e.stmts(n.Ninit)

	switch n.Op {
	default:
		Fatalf("unexpected stmt: %v", n)

	case OEMPTY, ODCLCONST, ODCLTYPE, OFALL:
		// nop

	case OBREAK, OCONTINUE, OGOTO:
		// TODO(mdempsky): Handle dead code?

	case OBLOCK:
		e.stmts(n.List)

	case ODCL:
		// Record loop depth at declaration.
		e.dcl(n.Left)

	case OLABEL:
		switch asNode(n.Sym.Label) {
		case &nonlooping:
			if Debug['m'] > 2 {
				fmt.Printf("%v:%v non-looping label\n", linestr(lineno), n)
			}
		case &looping:
			if Debug['m'] > 2 {
				fmt.Printf("%v: %v looping label\n", linestr(lineno), n)
			}
			e.loopdepth++
		}

		// n.Sym.Label = nil

	case OIF:
		e.discard(n.Left)
		e.stmts(n.Nbody)
		e.stmts(n.Rlist)

	case OFOR, OFORUNTIL:
		e.loopdepth++
		e.discard(n.Left)
		e.stmt(n.Right)
		e.stmts(n.Nbody)
		e.loopdepth--

	case ORANGE:
		// for List = range Right { Nbody }

		e.loopdepth++
		ks := e.addrs(n.List)
		e.loopdepth--

		// ORANGE node's Right is evaluated outside the loop
		k := e.discardHole()
		if len(ks) >= 2 {
			k = ks[1]
		}
		if n.Right.Type.IsArray() {
			e.value(k.note(n, "range"), n.Right)
		} else {
			e.value(k.deref(n, "range-deref"), n.Right)
		}

		e.loopdepth++
		e.stmts(n.Nbody)
		e.loopdepth--

	case OSWITCH:
		var tv *EscLocation
		if n.Left != nil {
			if n.Left.Op == OTYPESW {
				k := e.discardHole()
				if n.Left.Left != nil {
					tv = e.newLoc(n.Left)
					k = EscHole{dst: tv}
				}
				e.value(k, n.Left.Right)
			} else {
				e.discard(n.Left)
			}
		}

		for _, cas := range n.List.Slice() { // cases
			if tv != nil {
				// type switch variables have no ODCL.
				cv := cas.Rlist.First()
				k := e.dcl(cv)
				if types.Haspointers(cv.Type) {
					// Implicit ODOTTYPE.
					if !cv.Type.IsInterface() && !isdirectiface(cv.Type) {
						k = k.shift(1)
					}
					e.flow(k.note(n, "switch case"), tv)
				}
			}

			e.discards(cas.List)
			e.stmts(cas.Nbody)
		}

	case OSELECT:
		for _, cas := range n.List.Slice() {
			e.stmt(cas.Left)
			e.stmts(cas.Nbody)
		}
	case OSELRECV:
		e.assign(n.Left, n.Right, "selrecv", n)
	case OSELRECV2:
		e.assign(n.Left, n.Right, "selrecv", n)
		e.assign(n.List.First(), nil, "selrecv", n)
	case OSEND:
		e.discard(n.Left)
		e.assignHeap(n.Right, "send", n)

	case OAS, OASOP:
		e.assign(n.Left, n.Right, "assign", n)

	case OAS2:
		for i, nl := range n.List.Slice() {
			e.assign(nl, n.Rlist.Index(i), "assign-pair", n)
		}

	case OAS2DOTTYPE: // v, ok = x.(type)
		e.assign(n.List.First(), n.Rlist.First(), "assign-pair-dot-type", n)
		e.assign(n.List.Second(), nil, "assign-pair-dot-type", n)
	case OAS2MAPR: // v, ok = m[k]
		e.assign(n.List.First(), n.Rlist.First(), "assign-pair-mapr", n)
		e.assign(n.List.Second(), nil, "assign-pair-mapr", n)
	case OAS2RECV: // v, ok = <-ch
		e.assign(n.List.First(), n.Rlist.First(), "assign-pair-receive", n)
		e.assign(n.List.Second(), nil, "assign-pair-receive", n)

	case OAS2FUNC:
		e.call(e.addrs(n.List), n.Rlist.First())
	case ORETURN:
		ks := e.resultHoles()
		if len(ks) > 1 && n.List.Len() == 1 {
			// TODO(mdempsky): Handle implicit conversions.
			e.call(ks, n.List.First())
		} else {
			for i, v := range n.List.Slice() {
				e.value(ks[i], v)
			}
		}
	case OCALLFUNC, OCALLMETH, OCALLINTER:
		e.call(nil, n)
	case OGO, ODEFER:
		call := n.Left
		if n.Op == ODEFER && e.loopdepth == 1 {
			e.stmt(call)
			break
		}

		switch call.Op {
		case OCALLFUNC, OCALLMETH, OCALLINTER:
			e.assignHeap(call.Left, "go/defer func", n)

			args := call.List.Slice()
			if len(args) == 1 && args[0].Type.IsFuncArgStruct() {
				var holes []EscHole
				for i, n := 0, args[0].Type.NumFields(); i < n; i++ {
					holes = append(holes, e.heapHole())
				}
				e.call(holes, args[0])
			} else {
				for _, arg := range args {
					e.assignHeap(arg, "go/defer func arg", n)
				}
				if call.Left.Type.IsVariadic() && !call.IsDDD() && len(args) >= call.Left.Type.NumParams() {
					// TODO(mdempsky): Is this right?
					e.spill(e.heapHole(), call)
				}
			}

			// TODO(mdempsky): There should be a more
			// generic way of handling these.
		case OCLOSE, OPANIC:
			e.assignHeap(call.Left, "go/defer func arg", n)
		case OCOPY:
			e.assignHeap(call.Left, "go/defer func arg", n)
			e.assignHeap(call.Right, "go/defer func arg", n)
		case ODELETE, OPRINT, OPRINTN:
			// TODO(mdempsky): Handle f(g()), but
			// typecheck doesn't handle it either.
			for _, arg := range call.List.Slice() {
				e.assignHeap(arg, "go/defer func arg", n)
			}
		case ORECOVER:
			// nop

		default:
			Fatalf("TODO: %v", n)
		}

	case ORETJMP:
		// TODO(mdempsky): What do? esc.go just ignores it.

	case OCLOSE:
		e.discard(n.Left)
	case OPANIC:
		e.assignHeap(n.Left, "panic", n)
	case ODELETE, OPRINT, OPRINTN:
		// TODO(mdempsky): Handle f(g()).
		e.discards(n.List)

	case OCOPY, ORECOVER, ORECV:
		e.valueSkipInit(e.discardHole(), n)
	}
}

func (e *EscState) stmts(l Nodes) {
	for _, n := range l.Slice() {
		e.stmt(n)
	}
}

func (e *EscState) value(k EscHole, n *Node) {
	if n == nil {
		return
	}
	e.stmts(n.Ninit)
	e.valueSkipInit(k, n)
}

func (e *EscState) valueSkipInit(k EscHole, n *Node) {
	if n == nil {
		return
	}

	lno := setlineno(n)
	defer func() {
		lineno = lno
	}()

	if !types.Haspointers(n.Type) && !isReflectHeaderDataField(n) && k.derefs >= 0 {
		if debugLevel(2) && k.dst != &BlankLoc {
			Warnl(n.Pos, "discarding value of non-pointer %v", n)
		}
		k = e.discardHole()
	}

	// fmt.Printf("valueSkipInit: %v, %v\n", k, n)

	switch n.Op {
	default:
		Fatalf("unexpected expr: %v", n)

	case OLITERAL, OGETG, OCLOSUREVAR, OTYPE:
		// nop

	case ONAME:
		if n.Class() == PFUNC || n.Class() == PEXTERN {
			return
		}
		if n.IsClosureVar() {
			n = n.Name.Defn
		}
		e.flow(k, e.oldLoc(n))

	case OPLUS, ONEG, OBITNOT, ONOT:
		e.discard(n.Left)
	case OADD, OSUB, OOR, OXOR, OMUL, ODIV, OMOD, OLSH, ORSH, OAND, OANDNOT, OEQ, ONE, OLT, OLE, OGT, OGE, OANDAND, OOROR:
		e.discard(n.Left)
		e.discard(n.Right)

	case OADDR:
		if Debug['m'] != 0 {
			e.spill(k, n) // Close enough.
		}
		e.value(k.addr(n, "address-of"), n.Left) // "address-of"
	case ODEREF:
		e.value(k.deref(n, "indirection"), n.Left) // "indirection"
	case ODOT, ODOTMETH, ODOTINTER:
		e.value(k.note(n, "dot"), n.Left)
	case ODOTPTR:
		e.value(k.deref(n, "dot of pointer"), n.Left) // "dot of pointer"
	case ODOTTYPE, ODOTTYPE2:
		if !n.Type.IsInterface() && !isdirectiface(n.Type) {
			k = k.shift(1)
		}
		e.value(k.note(n, "dot"), n.Left)
	case OINDEX:
		if n.Left.Type.IsArray() {
			e.value(k.note(n, "fixed-array-index-of"), n.Left)
		} else {
			// TODO(mdempsky): Fix why reason text.
			e.value(k.deref(n, "dot of pointer"), n.Left)
		}
		e.discard(n.Right)
	case OINDEXMAP:
		e.discard(n.Left)
		e.discard(n.Right)
	case OSLICE, OSLICEARR, OSLICE3, OSLICE3ARR, OSLICESTR:
		e.value(k.note(n, "slice"), n.Left)
		low, high, max := n.SliceBounds()
		e.discard(low)
		e.discard(high)
		e.discard(max)

	case OCONV, OCONVNOP:
		if n.Type.Etype == TUNSAFEPTR && n.Left.Type.Etype == TUINTPTR {
			e.unsafeValue(k, n.Left)
		} else {
			e.value(k, n.Left)
		}
	case OCONVIFACE:
		if !n.Left.Type.IsInterface() && !isdirectiface(n.Left.Type) {
			k = e.spill(k, n)
		}
		e.value(k.note(n, "interface-converted"), n.Left)

	case ORECV:
		e.discard(n.Left)

	case OCALLMETH, OCALLFUNC, OCALLINTER:
		e.call([]EscHole{k}, n)

	case ONEW:
		e.spill(k, n)

	case OMAKESLICE:
		e.spill(k, n)
		e.discard(n.Left)
		e.discard(n.Right)

	case OMAKECHAN, OMAKEMAP:
		e.spill(k, n) // TODO(mdempsky): Always spills.
		e.discard(n.Left)

	case OLEN, OCAP, OREAL, OIMAG:
		e.discard(n.Left)
	case OCOMPLEX:
		// TODO(mdempsky): If n.List.Len() == 1, then complex(f()).
		e.discard(n.Left)
		e.discard(n.Right)

	case ORECOVER:
		// nop

	case OCALLPART:
		e.spill(k, n)

		// Contents make it to memory, lose loc.
		// TODO(mdempsky): What does this mean?
		e.assignHeap(n.Left, "call part", n)

	case OPTRLIT:
		e.value(e.spill(k, n).note(n, "pointer literal [assign]"), n.Left)

	case OARRAYLIT:
		for _, elt := range n.List.Slice() {
			if elt.Op == OKEY {
				elt = elt.Right
			}
			e.value(k.note(n, "array literal element"), elt)
		}

	case OSLICELIT:
		// Slice is not leaked until proven otherwise
		k = e.spill(k, n)

		// Link values to slice
		for _, elt := range n.List.Slice() {
			if elt.Op == OKEY {
				elt = elt.Right
			}
			e.value(k.note(n, "slice-literal-element"), elt)
		}

	case OSTRUCTLIT:
		for _, elt := range n.List.Slice() {
			e.value(k.note(n, "struct literal element"), elt.Left)
		}

	case OMAPLIT:
		e.spill(k, n) // TODO(mdempsky): Always leaks.

		// Keys and values make it to memory, lose loc.
		for _, elt := range n.List.Slice() {
			e.assignHeap(elt.Left, "map literal key", n)
			e.assignHeap(elt.Right, "map literal value", n)
		}

	case OCLOSURE:
		k = e.spill(k, n)

		// Link addresses of captured variables to closure.
		for _, v := range n.Func.Closure.Func.Cvars.Slice() {
			if v.Op == OXXX { // unnamed out argument; see dcl.go:/^funcargs
				continue
			}

			k := k
			if !v.Name.Byval() {
				k = k.addr(v, "reference")
			}

			e.value(k.note(n, "captured by a closure"), v.Name.Defn)
		}

	case ORUNES2STR, OBYTES2STR, OSTR2RUNES, OSTR2BYTES, ORUNESTR:
		e.spill(k, n)
		e.discard(n.Left)

	case OADDSTR:
		e.spill(k, n)

		// Arguments of OADDSTR do not escape:
		// runtime.concatstrings makes sure of that.
		e.discards(n.List)

	case OAPPEND:
		args := n.List.Slice()
		if len(args) == 1 {
			Fatalf("TODO: %v", n)
		}

		if oldEscCompat && types.Haspointers(args[0].Type.Elem()) {
			k = e.teeHole(k, e.heapHole().deref(n, "appendee slice"))
		}
		e.value(k, args[0])

		if n.IsDDD() {
			k2 := e.discardHole()
			if oldEscCompat && args[1].Type.IsSlice() && types.Haspointers(args[1].Type.Elem()) {
				k2 = e.heapHole().deref(n, "appended slice...")
			}
			e.value(k2, args[1])
		} else {
			for _, arg := range args[1:] {
				e.assignHeap(arg, "appended to slice", n)
			}
		}

	case OCOPY:
		// TODO(mdempsky): Handle copy(f()), but typecheck
		// doesn't handle that anyway.

		e.discard(n.Left)

		k2 := e.discardHole()
		if n.Right.Type.IsSlice() && types.Haspointers(n.Right.Type.Elem()) {
			k2 = e.heapHole().deref(n, "copied slice")
		}
		e.value(k2, n.Right)
	}
}

// unsafeValue evaluates a uintptr-typed arithmetic expression looking
// for conversions from an unsafe.Pointer.
func (e *EscState) unsafeValue(k EscHole, n *Node) {
	if n.Type.Etype != TUINTPTR {
		Fatalf("unexpected type %v for %v", n.Type, n)
	}

	// TODO(mdempsky): Recognize
	// reflect.Value.{Pointer,UnsafeAddr} and
	// reflect.{Slice,String}Header.Data.

	switch n.Op {
	case OCONV, OCONVNOP:
		if n.Left.Type.Etype == TUNSAFEPTR {
			e.value(k, n.Left)
		} else {
			e.discard(n.Left)
		}
	case OPLUS, ONEG, OBITNOT:
		e.unsafeValue(k, n.Left)
	case OADD, OSUB, OOR, OXOR, OMUL, ODIV, OMOD, OLSH, ORSH, OAND, OANDNOT:
		e.unsafeValue(k, n.Left)
		e.unsafeValue(k, n.Right)
	default:
		e.discard(n)
	}
}

func (e *EscState) discard(n *Node) {
	e.value(e.discardHole(), n)
}

func (e *EscState) discards(l Nodes) {
	for _, n := range l.Slice() {
		e.discard(n)
	}
}

func (e *EscState) addr(n *Node) EscHole {
	if n == nil || n.isBlank() {
		// Can happen at least in OSELRECV.
		// TODO(mdempsky): Anywhere else?
		return e.discardHole()
	}

	k := e.heapHole()

	switch n.Op {
	default:
		Fatalf("unexpected addr: %v", n)
	case ONAME:
		if n.Class() == PFUNC {
			Fatalf("bad")
		}
		if n.Class() == PEXTERN {
			break
		}
		if n.IsClosureVar() {
			n = n.Name.Defn
		}
		k = EscHole{dst: e.oldLoc(n)}
	case ODOT:
		k = e.addr(n.Left)
	case OINDEX:
		e.discard(n.Right)
		if n.Left.Type.IsArray() {
			k = e.addr(n.Left)
		} else {
			e.discard(n.Left)
		}
	case ODEREF, ODOTPTR:
		e.discard(n)
	case OINDEXMAP:
		e.discard(n.Left)
		e.assignHeap(n.Right, "key of map put", n)
	}

	if !types.Haspointers(n.Type) && !isReflectHeaderDataField(n) {
		if debugLevel(2) && k.dst != &BlankLoc {
			Warnl(n.Pos, "discarding assignment to non-pointer destination %v", n)
		}
		k = e.discardHole()
	}

	return k
}

func (e *EscState) addrs(l Nodes) []EscHole {
	var ks []EscHole
	for _, n := range l.Slice() {
		ks = append(ks, e.addr(n))
	}
	return ks
}

func (e *EscState) assign(dst, src *Node, why string, where *Node) {
	// Filter out some no-op assignments for escape analysis.
	ignore := (!oldEscCompat || why == "assign") && dst != nil && src != nil && e.isSelfAssign(dst, src)
	if ignore && Debug['m'] != 0 {
		Warnl(where.Pos, "%v ignoring self-assignment in %S", funcSym(Curfn), where)
	}

	if debugLevel(3) {
		Dump("esc2 assignment", where)
	}

	k := e.addr(dst)
	if ignore {
		k = e.discardHole()
	}
	e.value(k, src)
}

func (e *EscState) assignHeap(src *Node, why string, where *Node) {
	e.value(e.heapHole().note(where, why), src)
}

func (e *EscState) call(ks []EscHole, call *Node) {
	if ks != nil && len(ks) != call.Left.Type.NumResults() {
		Warnl(call.Pos, "expect %v values, but %v has %v results", len(ks), call.Left, call.Left.Type.NumResults())
	}

	// TODO(mdempsky): Should this handle builtin calls too?

	var indirect bool
	var fn *Node
	switch call.Op {
	default:
		Fatalf("esccall: %v", call.Op)

	case OCALLFUNC:
		fn = call.Left

		// TODO(mdempsky): If fn.Op == OCLOSURE, we can
		// replace fn with fn.Func.Closure.Func.Nname. In this
		// case, we don't need to treat the closure's return
		// values as inherently escaping either.

		// TODO(mdempsky): Is handling method expressions
		// really this simple?
		//
		// if fn.isMethodExpression() {
		// 	fn = asNode(fn.Sym.Def)
		// }

		indirect = fn.Op != ONAME || fn.Class() != PFUNC

	case OCALLMETH:
		fn = asNode(call.Left.Sym.Def)

	case OCALLINTER:
		indirect = true
	}

	fntype := call.Left.Type

	var recvK EscHole
	var paramKs []EscHole

	if debugLevel(2) {
		Dump("call", call)
	}

	// Warnl(call.Pos, "figuring out how to call %v", call)

	if !indirect && fn != nil && fn.Op == ONAME && fn.Class() == PFUNC &&
		fn.Name.Defn != nil && fn.Name.Defn.Nbody.Len() != 0 && fn.Name.Param.Ntype != nil && fn.Name.Defn.Esc < EscFuncTagged {

		fntype = fn.Type

		// function in same mutually recursive group. Incorporate into flow graph.
		if debugLevel(2) {
			Warnl(call.Pos, "calling %v recursively", call)
		}

		if fn.Name.Defn.Esc == EscFuncUnknown {
			Fatalf("graph inconsistency")
		}

		// Results.
		if ks != nil {
			for i, result := range fntype.Results().FieldSlice() {
				e.flow(ks[i], e.oldLoc(asNode(result.Nname)))
			}
		}

		// Receiver.
		if call.Op != OCALLFUNC {
			recvK = e.paramHole(fntype.Recv())
		}

		// Parameters.
		for _, param := range fntype.Params().FieldSlice() {
			paramKs = append(paramKs, e.paramHole(param))
		}
	} else {
		if debugLevel(2) {
			Warnl(call.Pos, "calling %v/%v using its tags (indirect=%v)", fn, fntype, indirect)
		}

		// If there is a receiver, it also leaks to heap.
		if call.Op != OCALLFUNC {
			recvK = e.tagHole(ks, indirect, fntype.Recv())
		}

		for _, param := range fntype.Params().FieldSlice() {
			paramKs = append(paramKs, e.tagHole(ks, indirect, param))
		}
	}

	if fntype.IsVariadic() && !call.IsDDD() {
		vi := fntype.NumParams() - 1

		nva := call.List.Len()
		if nva == 1 && call.List.First().Type.IsFuncArgStruct() {
			nva = call.List.First().Type.NumFields()
		}
		nva -= vi

		dddK := e.spill(paramKs[vi], call)
		paramKs = paramKs[:vi]
		for i := 0; i < nva; i++ {
			paramKs = append(paramKs, dddK)
		}

		if nva == 0 {
			call.Esc = 42
		}
	}

	// TODO(mdempsky): Handle implicit conversions.

	if call.Op != OCALLFUNC {
		e.value(recvK, call.Left.Left)
	} else if indirect {
		// indirect and OCALLFUNC = could be captured variables, too. (#14409)
		e.value(e.teeHole(ks...).deref(call, "captured by called closure"), fn)
	}

	if len(paramKs) > 1 && call.List.Len() == 1 {
		e.call(paramKs, call.List.First())
	} else {
		for i, arg := range call.List.Slice() {
			// For arguments to go:uintptrescapes, peel
			// away an unsafe.Pointer->uintptr conversion,
			// if present.
			if !indirect && arg.Op == OCONVNOP && arg.Type.Etype == TUINTPTR && arg.Left.Type.Etype == TUNSAFEPTR {
				x := i
				if fntype.IsVariadic() && x >= fntype.NumParams() {
					x = fntype.NumParams() - 1
				}
				if fntype.Params().Field(x).Note == uintptrEscapesTag {
					arg = arg.Left
				}
			}

			e.value(paramKs[i], arg)
		}
	}
}

func (e *EscState) paramHole(param *types.Field) EscHole {
	if !types.Haspointers(param.Type) {
		return e.discardHole()
	}
	return EscHole{dst: e.oldLoc(asNode(param.Nname))}
}

func (e *EscState) teeHole(ks ...EscHole) EscHole {
	if len(ks) == 0 {
		return e.discardHole()
	}
	if len(ks) == 1 {
		return ks[0]
	}

	loc := e.newLoc(nil)
	for _, k := range ks {
		e.flow(k, loc)
	}
	return EscHole{dst: loc}
}

func (e *EscState) tagHole(ks []EscHole, indirect bool, param *types.Field) EscHole {
	tag := param.Note
	if debugLevel(2) {
		fmt.Printf("tagHole: [%v] = %q, indirect=%v\n", ks, tag, indirect)
	}

	if indirect {
		// TODO(mdempsky): Perhaps overly conservative. I
		// don't think we need to guarantee that f(uintptr(p))
		// works if f is an indirect call to a uintptrescapes
		// function, for example.
		return e.heapHole()
	}
	if tag == "" && !types.Haspointers(param.Type) {
		return e.discardHole()
	}
	if tag == "" || tag == uintptrEscapesTag || tag == unsafeUintptrTag {
		return e.heapHole()
	}

	if !strings.HasPrefix(tag, "esc:0x") {
		Fatalf("weird tag: %q", tag)
	}
	esc, err := strconv.ParseUint(tag[6:], 16, 16)
	if err != nil {
		Fatalf("weird tag: %q -> %v", tag, err)
	}

	if esc == EscHeap {
		return e.heapHole()
	}
	if esc == EscNone {
		return e.discardHole()
	}

	// TODO(mdempsky): Should there be a Node for this?
	loc := e.newLoc(nil)

	if esc&EscContentEscapes != 0 {
		e.flow(e.heapHole().shift(1), loc)
	}

	for i, k := range ks {
		x := int(esc>>uint(EscReturnBits+i*bitsPerOutputInTag)) & int(bitsMaskForTag)
		if x != 0 {
			e.flow(k.shift(x-1), loc)
		}
	}

	return EscHole{dst: loc}
}

type EscLocation struct {
	n         *Node
	edges     []EscEdge
	curfn     *Node
	loopDepth int

	distance int
	walkgen  uint32
	escapes  bool
	paramEsc uint16
}

type EscEdge struct {
	src    *EscLocation
	derefs int
}

type EscHole struct {
	dst    *EscLocation
	derefs int
}

func (k EscHole) note(where *Node, why string) EscHole {
	// TODO(mdempsky): Keep a record of where/why for diagnostics.
	return k
}

func (k EscHole) shift(delta int) EscHole {
	k.derefs += delta
	if k.derefs < -1 {
		Fatalf("derefs underflow: %v", k.derefs)
	}
	return k
}

func (k EscHole) deref(where *Node, why string) EscHole { return k.shift(1).note(where, why) }
func (k EscHole) addr(where *Node, why string) EscHole  { return k.shift(-1).note(where, why) }

func (e *EscState) dcl(n *Node) EscHole {
	loc := e.oldLoc(n)
	loc.loopDepth = int(e.loopdepth)
	return EscHole{dst: loc}
}

func (e *EscState) spill(k EscHole, n *Node) EscHole {
	loc := e.newLoc(n)
	e.flow(k.addr(n, "spill"), loc)
	return EscHole{dst: loc}
}

func normalize(n *Node) *Node {
	if n == nil {
		return nil
	}

	// esc.go may have moved the node to the heap and rewritten
	// the function signature already. Normalize to account for
	// this.
	if n.Op == ONAME && (n.Class() == PPARAM || n.Class() == PPARAMOUT) && n.Name.Param.Heapaddr != nil {
		for _, n2 := range n.Name.Curfn.Func.Dcl {
			if n2.Op == ONAME && n2.Name.Param.Stackcopy == n {
				return n2
			}
		}
		Fatalf("can't find heap version of %v", n)
	}

	return n
}

func (e *EscState) newLoc(n *Node) *EscLocation {
	if Curfn == nil {
		Fatalf("Curfn isn't set")
	}

	n = normalize(n)

	// TODO(mdempsky): Validate n.Op?
	if _, ok := escLocs[n]; ok {
		if debugLevel(1) {
			Warnl(n.Pos, "%v already has a location", n)
		}
	}
	if debugLevel(1) {
		var pos src.XPos
		if n != nil {
			pos = n.Pos
		}
		Warnl(pos, "allocating location for %v (%p) at ld=%v", n, n, e.loopdepth)
	}
	loc := &EscLocation{
		n:         n,
		curfn:     Curfn,
		loopDepth: int(e.loopdepth),
	}
	allocLocs++
	if n != nil {
		escLocs[n] = loc

		// TODO(mdempsky): Perhaps set n.Esc and then just return &HeapLoc?
		if /*n.Esc != EscHeap &&*/ n.Type != nil && !loc.isName(PPARAM) && !loc.isName(PPARAMOUT) &&
			(n.Type.Width > maxStackVarSize ||
				(n.Op == ONEW || n.Op == OPTRLIT) && n.Type.Elem().Width >= maxImplicitStackVarSize ||
				n.Op == OMAKESLICE && !isSmallMakeSlice(n)) {
			if debugLevel(2) {
				Warnl(n.Pos, "spilling %v directly to the heap", n)
			}
			e.flow(e.heapHole().addr(nil, ""), loc)
		}
	}
	return loc
}

func (e *EscState) oldLoc(n *Node) *EscLocation {
	n = normalize(n)
	if n == nil {
		Fatalf("can't get old location for nil pointer")
	}
	loc, ok := escLocs[n]
	if !ok {
		// TODO(mdempsky): Fix ".this".
		if debugLevel(1) && !(n.Op == ONAME && n.Sym.Name == ".this") {
			Warnl(n.Pos, "%v (%p) doesn't have a location yet", n, n)
		}
		return e.newLoc(n)
	}
	return loc
}

var (
	HeapLoc  EscLocation
	BlankLoc EscLocation
)

func (l *EscLocation) String() string {
	switch l {
	case &HeapLoc:
		return "[heap]"
	case &BlankLoc:
		return "[blank]"
	}

	return fmt.Sprintf("%v", l.n)
}

func (e *EscState) flow(k EscHole, src_ *EscLocation) {
	// TODO(mdempsky): More optimizations. E.g., src == dst &&
	// k.derefs >= 0 can be ignored.

	var pos src.XPos
	if src_.n != nil {
		pos = src_.n.Pos
	}

	dst := k.dst
	if dst == &BlankLoc {
		if debugLevel(2) {
			Warnl(pos, "esc2: %v <~ %v, derefs=%v (dropped)", dst, src_, k.derefs)
		}
		return
	}

	if debugLevel(2) {
		Warnl(pos, "esc2: %v <~ %v, derefs=%v", dst, src_, k.derefs)
	}

	// TODO(mdempsky): Deduplicate edges?

	allocEdges++

	dst.edges = append(dst.edges, EscEdge{src: src_, derefs: k.derefs})
	if debugLevel(2) {
		Warnl(pos, "flow: %v (%p) now has %v edges", dst, dst, len(dst.edges))
	}
}

func (e *EscState) heapHole() EscHole    { return EscHole{dst: &HeapLoc} }
func (e *EscState) discardHole() EscHole { return EscHole{dst: &BlankLoc} }

func (e *EscState) resultHoles() []EscHole {
	var ks []EscHole
	for _, f := range Curfn.Type.Results().FieldSlice() {
		if !types.Haspointers(f.Type) {
			ks = append(ks, e.discardHole())
		} else {
			ks = append(ks, EscHole{dst: e.oldLoc(asNode(f.Nname))})
		}
	}
	return ks
}

var escLocs = map[*Node]*EscLocation{}

func (e *EscState) setup(all []*Node) {
	e.loopdepth = 1
	for _, fn := range all {
		Curfn = fn
		for _, dcl := range fn.Func.Dcl {
			if dcl.Op == ONAME {
				loc := e.newLoc(dcl)
				if dcl.Class() == PPARAM && fn.Nbody.Len() == 0 && !fn.Noescape() {
					loc.paramEsc = EscHeap
				}

				if oldEscCompat && e.recursive && dcl.Class() == PPARAMOUT {
					e.flow(e.heapHole(), loc)
				}
			}
		}
	}
	Curfn = nil
}

func (e *EscState) flood(all []*Node) {
	for _, fn := range all {
		Curfn = fn
		if fn.Op != ODCLFUNC {
			Warnl(fn.Pos, "what is it? %v", fn)
			continue
		}
		for _, dcl := range fn.Func.Dcl {
			// TODO(mdempsky): Sometimes this discovers
			// new ONAMEs that weren't in setup. Probably
			// from movetoheap?
			if dcl.Op == ONAME {
				e.walk(e.oldLoc(dcl))
			}
		}
	}
	Curfn = nil

	e.walk(&HeapLoc)
}

func (e *EscState) walk(root *EscLocation) {
	if debugLevel(1) {
		Warnl(src.NoXPos, "esc2: walking from %v", root)
	}
	e.walkgen++
	root.walkgen = e.walkgen
	root.distance = 0
	todo := []*EscLocation{root}
	for len(todo) > 0 {
		p := todo[0]
		todo = todo[1:]

		base := p.distance
		if debugLevel(1) {
			Warnl(src.NoXPos, "esc2: visiting %v (%p) at distance %v from root %v; %v edges", p, p, base, root, len(p.edges))
		}

		if base < 0 {
			base = 0

			// p's address flows to root. If root outlives
			// p, then p needs to be heap allocated.
			if root.outlives(p) {
				if !p.escapes && debugLevel(1) {
					var pos src.XPos
					if p.n != nil {
						pos = p.n.Pos
					}
					Warnl(pos, "esc2: found a path from %v to %v that escapes", root, p)
				}
				p.escapes = true

				// TODO(mdempsky): This is clumsy.
				if root != &HeapLoc {
					e.flow(EscHole{dst: &HeapLoc}, p)
				}
			}
		}

		// p's value flows to root. If p is a function
		// parameter and root is the heap or a corresponding
		// result parameter, then record that value flow for
		// tagging the function later.
		if p.isName(PPARAM) {
			if root == &HeapLoc {
				p.leak(-1, base)
			} else if root.isName(PPARAMOUT) && root.n.Name.Curfn == p.n.Name.Curfn {
				// TODO(mdempsky): Eliminate dependency on Vargen here.
				p.leak(int(root.n.Name.Vargen)-1, base)
			}
		}

		for _, edge := range p.edges {
			dist := base + edge.derefs
			if debugLevel(1) {
				Warnl(src.NoXPos, "esc2: edge from %v (%v) ~> %v (%v) at distance %v", p, p.distance, edge.src, edge.src.distance, dist)
			}
			if edge.src.walkgen != e.walkgen || edge.src.distance > dist {
				edge.src.walkgen = e.walkgen
				edge.src.distance = dist
				todo = append(todo, edge.src)
			}
		}
	}
}

func (l *EscLocation) isName(c Class) bool {
	return l.n != nil && l.n.Op == ONAME && l.n.Class() == c
}

// outlives reports whether values stored in l may survive beyond
// other's lifetime if stack allocated.
func (l *EscLocation) outlives(other *EscLocation) bool {
	// The heap outlives everything.
	if l == &HeapLoc {
		return true
	}

	// Result parameters flow to the heap, so in effect they
	// outlive any other location.
	//
	// TODO(mdempsky): It should be possible to optimize
	// directly-called function literal result parameters, but
	// it's probably not worth the complexity. For example:
	//
	//    var u int  // could be stack allocated
	//    *(func() *int { return &u }()) = 42
	//
	//    func(p *int) {
	//        *p = 42
	//    }(func() *int {
	//        return new(int)  // must be heap allocated
	//    }())
	if l.isName(PPARAMOUT) {
		return true
	}

	// If l and other are within the same function, then l
	// outlives other if it was declared outside other's loop
	// scope. For example:
	//
	//    var l *int
	//    for {
	//        l = new(int)
	//    }
	if l.curfn == other.curfn && l.loopDepth < other.loopDepth {
		return true
	}

	// If other is declared within a child closure of where l is
	// declared, then l outlives it. For example:
	//
	//    var l *int
	//    func() {
	//        l = new(int)
	//    }
	if strings.HasPrefix(other.curfn.Func.Nname.Sym.Name, l.curfn.Func.Nname.Sym.Name+".") {
		return true
	}

	return false
}

func (l *EscLocation) leak(ri, derefs int) {
	if l.paramEsc == EscHeap {
		return
	}

	const numResults = (16 - EscReturnBits) / bitsPerOutputInTag
	if ri >= numResults {
		ri = -1
	}

	if ri == -1 {
		if derefs > 0 {
			l.paramEsc |= EscContentEscapes
		} else {
			l.paramEsc = EscHeap
		}
		return
	}

	x := 1 + uint16(derefs)
	if derefs > maxEncodedLevel {
		x = 1 + uint16(maxEncodedLevel)
	}

	shift := uint(EscReturnBits + ri*bitsPerOutputInTag)
	if (x<<shift)>>shift != x {
		Fatalf("encoding error")
	}

	if old := (l.paramEsc >> shift) & bitsMaskForTag; old == 0 || x < old {
		l.paramEsc = (l.paramEsc &^ (bitsMaskForTag << shift)) | (x << shift)
	}
}

func debugLevel(x int) bool {
	return Debug['m'] >= x && os.Getenv("ESC2") != ""
}

func (e *EscState) cleanup(all []*Node) {
	if esc2Live {
		for n, loc := range escLocs {
			switch n.Op {
			case OTYPESW:
				continue
			case OCALLFUNC, OCALLMETH, OCALLINTER:
				n.Right = nodl(n.Pos, ODDDARG, nil, nil)
				n = n.Right
			}

			// TODO(mdempsky): Describe path when Debug['m'] >= 2.

			if loc.escapes {
				if Debug['m'] != 0 && n.Op != ONAME {
					Warnl(n.Pos, "%S escapes to heap", n)
				}
				n.Esc = EscHeap
				addrescapes(n)
			} else if loc.isName(PPARAM) {
				n.Esc = finalizeEsc(loc.paramEsc)

				if Debug['m'] != 0 && types.Haspointers(n.Type) {
					if n.Esc == EscNone {
						Warnl(n.Pos, "%S %S does not escape", funcSym(loc.curfn), n)
					} else if n.Esc == EscHeap {
						Warnl(n.Pos, "leaking param: %S", n)
					} else {
						if n.Esc&EscContentEscapes != 0 {
							Warnl(n.Pos, "leaking param content: %S", n)
						}
						for i := 0; i < 16; i++ {
							x := (n.Esc >> uint(EscReturnBits+i*bitsPerOutputInTag)) & bitsMaskForTag
							if x != 0 {
								res := n.Name.Curfn.Type.Results().Field(i).Sym
								Warnl(n.Pos, "leaking param: %S to result %v level=%d", n, res, x-1)
							}
						}
					}
				}
			} else {
				n.Esc = EscNone
				if Debug['m'] != 0 && n.Op != ONAME {
					Warnl(n.Pos, "%S %S does not escape", funcSym(loc.curfn), n)
				}
			}
		}
	} else {
		for n, loc := range escLocs {
			var esc uint16 = EscUnknown
			switch n.Op {
			case OCALLFUNC, OCALLMETH, OCALLINTER:
				// esc.go doesn't create ODDDARG for all
				// calls. If it's missing, then walk.go treats
				// it as EscUnknown.
				if x := n.Right; x != nil {
					esc = x.Esc
				} else if n.Esc == 42 {
					continue
				}
			case ONAME:
				if n.Class() == PAUTOHEAP {
					esc = EscHeap
				} else {
					esc = EscNone
				}
			case OTYPESW:
				// Temporary location; not real.
				continue
			default:
				esc = n.Esc
			}
			escaped := esc != EscNone
			if escaped != loc.escapes {
				Warnl(n.Pos, "noooo: %v (%v) is 0x%x, but %v", n, n.Op, esc, loc.escapes)
			}

			if n.Op == ONAME && n.Class() == PAUTOHEAP {
				n = n.Name.Param.Stackcopy
				if n == nil {
					continue
				}
			}
			if n.Op == ONAME && n.Class() == PPARAM && types.Haspointers(n.Type) {
				want := optimizeReturns(n.Esc)
				if want == EscReturn|EscContentEscapes {
					// esc.go leaves EscReturn sometimes
					// when it doesn't matter.
					want = EscNone | EscContentEscapes
				}

				// TODO(mdempsky): It seems like I'm not
				// handling escaped parameters
				// correctly. Figure this out, and in the mean
				// time, since 0 is nonsense, just use EscHeap
				// conservatively.
				if want == 0 {
					want = EscHeap
				}

				loc.paramEsc = finalizeEsc(loc.paramEsc)
				if want != loc.paramEsc {
					Warnl(n.Pos, "waahh: %v is 0x%x, but 0x%x", n, want, loc.paramEsc)
				}
			}
		}
	}

	if allocLocs > maxLocs {
		maxLocs = allocLocs
	}
	totalLocs += allocLocs

	if allocEdges > maxEdges {
		maxEdges = allocEdges
	}
	totalEdges += allocEdges

	if allocState > maxState {
		maxState = allocState
	}
	totalState += allocState

	if allocFlow > maxFlow {
		maxFlow = allocFlow
	}
	totalFlow += allocFlow

	escLocs = map[*Node]*EscLocation{}

	HeapLoc = EscLocation{}
	BlankLoc = EscLocation{}
}

var allocLocs, maxLocs, totalLocs int
var allocEdges, maxEdges, totalEdges int

func escfinished() {
	if debugLevel(1) {
		fmt.Printf("locations:   %d\t%d\n", totalLocs, maxLocs)
		fmt.Printf("edges:       %d\t%d\n", totalEdges, maxEdges)
		fmt.Printf("state:       %d\t%d\n", totalState, maxState)
		fmt.Printf("flow:        %d\t%d\n", totalFlow, maxFlow)
	}
}

func finalizeEsc(esc uint16) uint16 {
	esc = optimizeReturns(esc)

	if esc>>EscReturnBits != 0 {
		esc |= EscReturn
	} else if esc&EscMask == 0 {
		esc |= EscNone
	}

	return esc
}

func optimizeReturns(esc uint16) uint16 {
	if esc&EscContentEscapes != 0 {
		// EscContentEscapes represents a path of length 1
		// from the heap. No point in keeping paths of equal
		// or longer length to result parameters.
		for i := 0; i < 16; i++ {
			shift := uint(EscReturnBits + i*bitsPerOutputInTag)
			if x := (esc >> shift) & bitsMaskForTag; x >= 2 {
				esc &^= bitsMaskForTag << shift
			}
		}
	}
	return esc
}
