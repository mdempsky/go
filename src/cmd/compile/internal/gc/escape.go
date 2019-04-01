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

// Escape analysis.
//
// Here we analyze functions to determine whether Go variables can be
// allocated on the stack. The two key invariants we have to respect
// are: (1) objects allocated on the heap cannot point to objects on
// the stack, and (2) a pointer to a stack object cannot outlive that
// object (e.g., either because the function returned or its space is
// reused in a loop).
//
// We implement this with a simple data-flow analysis algorithm. For
// every Go variable, we create a "location." We then lower all Go
// statements into edges representing an assignment between the two,
// possibly with an addressing operation or an arbitrary number of
// dereference operations. For example:
//
//     p = &q    // -1
//     p = q     //  0
//     p = *q    //  1
//     p = **q   //  2
//
// Note that "p = &&q" is invalid, so the dereferences count can never
// go below -1.
//
// Assignments can also be directly to the heap.
//
// All Go language constructs are lowered into this graph
// representation. For example:
//
//     var x struct { f, g *int }
//     var u []*int
//
//     x.f = u[0]
//
// is modeled as
//
//     x = *u
//
// We then define dist(p, q) as the shortest path distance from p to q
// on this graph, except that intermediate distance is bounded at 0.
// For example:
//
//     p = **q    //  2
//     q = &r     // -1
//     r = *s     //  1
//
// We have dist(p, r) == 1, dist(p, s) == 3, dist(q, s) == 1.
//
// Intuitively, if dist(p, q) == 0, then any value stored in q may be
// stored in p; if dist(p, q) == 1, then any value *pointed to* by q
// may be stored in p; and so on.
//
// Finally, if there exists p,q,r such that dist(p, q) == 0 and q =
// &r, then r's address leaks to p. If p outlives r, then r must be
// heap allocated.

// If esc2Live is true, then esc2.go drives escape analysis instead of
// esc.go.
var esc2Live bool

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

type Escape struct {
	loopdepth int
}

func escapesComponent(all []*Node, recursive bool) {
	var e Escape

	for _, n := range all {
		if n.Op == ODCLFUNC {
			n.Esc = EscFuncPlanned
			if Debug['m'] > 3 {
				Dump("escAnalyze", n)
			}
		}
	}

	e.setup(all)

	// flow-analyze functions
	for _, n := range all {
		if n.Op == ODCLFUNC {
			e.escfunc(n)
		}
	}

	e.flood(all)

	e.cleanup(all)

	// for all top level functions, tag the typenodes corresponding to the param nodes
	for _, n := range all {
		if n.Op == ODCLFUNC {
			esctag(n)
		}
	}
}

func (e *Escape) setup(all []*Node) {
	e.loopdepth = 1
	for _, fn := range all {
		Curfn = fn
		for _, dcl := range fn.Func.Dcl {
			if dcl.Op == ONAME {
				loc := e.newLoc(dcl)
				loc.transient = false
				if dcl.Class() == PPARAM && fn.Nbody.Len() == 0 && !fn.Noescape() {
					loc.paramEsc = EscHeap
				}
			}
		}
	}
	Curfn = nil
}

func (e *Escape) escfunc(fn *Node) {
	if fn.Esc != EscFuncPlanned {
		Fatalf("repeat escfunc %v", fn.Func.Nname)
	}
	fn.Esc = EscFuncStarted

	inspectList(fn.Nbody, func(n *Node) bool {
		switch n.Op {
		case OLABEL:
			if n.Sym == nil {
				Fatalf("esc:label without label: %+v", n)
			}

			// Walk will complain about this label being already defined, but that's not until
			// after escape analysis. in the future, maybe pull label & goto analysis out of walk and put before esc
			n.Sym.Label = asTypesNode(&nonlooping)

		case OGOTO:
			if n.Sym == nil {
				Fatalf("esc:goto without label: %+v", n)
			}

			// If we come past one that's uninitialized, this must be a (harmless) forward jump
			// but if it's set to nonlooping the label must have preceded this goto.
			if asNode(n.Sym.Label) == &nonlooping {
				n.Sym.Label = asTypesNode(&looping)
			}
		}

		return true
	})

	savefn := Curfn
	Curfn = fn
	e.loopdepth = 1

	e.stmts(fn.Nbody)

	Curfn = savefn
}

func (e *Escape) stmt(n *Node) {
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

	case ODCLCONST, ODCLTYPE, OEMPTY, OFALL, OINLMARK:
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

		n.Sym.Label = nil

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

		// Right is evaluated outside the loop.
		tv := e.newLoc(n)
		tv.transient = false
		e.value(tv.asHole(), n.Right)

		e.loopdepth++
		ks := e.addrs(n.List)
		if len(ks) >= 2 {
			if n.Right.Type.IsArray() {
				e.flow(ks[1].note(n, "range"), tv)
			} else {
				e.flow(ks[1].deref(n, "range-deref"), tv)
			}
		}

		e.stmts(n.Nbody)
		e.loopdepth--

	case OSWITCH:
		var tv *EscLocation
		if n.Left != nil {
			if n.Left.Op == OTYPESW {
				k := e.discardHole()
				if n.Left.Left != nil {
					tv = e.newLoc(n.Left)
					tv.transient = false
					k = tv.asHole()
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
	case ORECV:
		// TODO(mdempsky): Consider e.discard(n.Left).
		e.valueSkipInit(e.discardHole(), n) // already visited Ninit
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
		e.stmts(n.Rlist.First().Ninit)
		e.call(e.addrs(n.List), n.Rlist.First(), nil)
	case ORETURN:
		ks := e.resultHoles()
		for i, v := range n.List.Slice() {
			e.value(ks[i], v)
		}
	case OCALLFUNC, OCALLMETH, OCALLINTER, OCLOSE, OCOPY, ODELETE, OPANIC, OPRINT, OPRINTN, ORECOVER:
		e.call(nil, n, nil)
	case OGO, ODEFER:
		e.stmts(n.Left.Ninit)
		e.call(nil, n.Left, n)

	case ORETJMP:
		// TODO(mdempsky): What do? esc.go just ignores it.
	}
}

func (e *Escape) stmts(l Nodes) {
	// TODO(mdempsky): Preserve and restore e.loopdepth?
	for _, n := range l.Slice() {
		e.stmt(n)
	}
}

func (e *Escape) value(k EscHole, n *Node) {
	if n == nil {
		return
	}
	e.stmts(n.Ninit)
	e.valueSkipInit(k, n)
}

func (e *Escape) valueSkipInit(k EscHole, n *Node) {
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
		} else {
			e.notTracked(k, n, "direct iface")
		}
		e.value(k.note(n, "interface-converted"), n.Left)

	case ORECV:
		e.discard(n.Left)

	case OCALLMETH, OCALLFUNC, OCALLINTER, OLEN, OCAP, OCOMPLEX, OREAL, OIMAG, OAPPEND, OCOPY:
		e.call([]EscHole{k}, n, nil)

	case ONEW:
		e.spill(k, n)

	case OMAKESLICE:
		e.spill(k, n)
		e.discard(n.Left)
		e.discard(n.Right)
	case OMAKECHAN:
		e.notTracked(k, n, "make chan")
		e.discard(n.Left)
	case OMAKEMAP:
		e.spill(k, n)
		e.discard(n.Left)

	case ORECOVER:
		// nop

	case OCALLPART:
		e.spill(k, n)

		// esc.go says "Contents make it to memory, lose
		// track."  I think we can just flow n.Left to our
		// spilled location though.
		// TODO(mdempsky): Try that.
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
		e.spill(k, n)

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
	}
}

// TODO(mdempsky): Remove.
func (e *Escape) notTracked(k EscHole, n *Node, why string) {
	e.spill(k, n)
}

// unsafeValue evaluates a uintptr-typed arithmetic expression looking
// for conversions from an unsafe.Pointer.
func (e *Escape) unsafeValue(k EscHole, n *Node) {
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

func (e *Escape) discard(n *Node) {
	e.value(e.discardHole(), n)
}

func (e *Escape) discards(l Nodes) {
	for _, n := range l.Slice() {
		e.discard(n)
	}
}

func (e *Escape) addr(n *Node) EscHole {
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
		k = e.oldLoc(n).asHole()
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

func (e *Escape) addrs(l Nodes) []EscHole {
	var ks []EscHole
	for _, n := range l.Slice() {
		ks = append(ks, e.addr(n))
	}
	return ks
}

func (e *Escape) assign(dst, src *Node, why string, where *Node) {
	// Filter out some no-op assignments for escape analysis.
	ignore := dst != nil && src != nil && isSelfAssign(dst, src)
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

func (e *Escape) assignHeap(src *Node, why string, where *Node) {
	e.value(e.heapHole().note(where, why), src)
}

func (e *Escape) call(ks []EscHole, call, where *Node) {
	var fn, recv *Node
	args := call.List.Slice()
	switch call.Op {
	case OCALLFUNC:
		fn = call.Left
		if fn.Op == OCLOSURE {
			fn = fn.Func.Closure.Func.Nname
		}
	case OCALLMETH:
		fn = asNode(call.Left.Type.FuncType().Nname)
		recv = call.Left.Left
	case OCALLINTER:
		recv = call.Left.Left
	case OAPPEND, ODELETE, OPRINT, OPRINTN, ORECOVER:
		// ok
	case OLEN, OCAP, OREAL, OIMAG, OCLOSE, OPANIC:
		args = []*Node{call.Left}
	case OCOMPLEX, OCOPY:
		args = []*Node{call.Left, call.Right}
	default:
		Fatalf("unexpected call op: %v", call.Op)
	}

	direct := fn != nil && fn.Op == ONAME && fn.Class() == PFUNC

	var fntype *types.Type
	var recvK EscHole
	var paramKs []EscHole

	if where != nil && !(where.Op == ODEFER && e.loopdepth == 1) {
		if recv != nil {
			recvK = e.heapHole()
		}
		for range args {
			paramKs = append(paramKs, e.heapHole())
		}
		switch call.Op {
		case OCALLFUNC, OCALLMETH, OCALLINTER:
			fntype = call.Left.Type
		}
	} else if direct && fn.Name.Defn != nil && fn.Name.Defn.Esc < EscFuncTagged {
		// Function in same mutually recursive
		// group. Incorporate into flow graph.

		if fn.Name.Defn.Nbody.Len() == 0 || fn.Name.Param.Ntype == nil {
			Fatalf("huh, those checks did matter")
		}
		if fn.Name.Defn.Esc == EscFuncUnknown {
			Fatalf("graph inconsistency")
		}

		fntype = fn.Type

		// Results.
		if ks != nil {
			for i, result := range fntype.Results().FieldSlice() {
				e.value(ks[i], asNode(result.Nname))
			}
		}

		// Parameters.
		if r := fntype.Recv(); r != nil {
			recvK = e.addr(asNode(r.Nname))
		}
		for _, param := range fntype.Params().FieldSlice() {
			paramKs = append(paramKs, e.addr(asNode(param.Nname)))
		}
	} else if call.Op == OCALLFUNC || call.Op == OCALLMETH || call.Op == OCALLINTER {
		fntype = call.Left.Type
		if debugLevel(2) {
			Warnl(call.Pos, "calling %v/%v using its tags (direct=%v)", call.Left, fntype, direct)
		}

		if r := fntype.Recv(); r != nil {
			recvK = e.tagHole(ks, direct, r, where == nil)
		}
		for _, param := range fntype.Params().FieldSlice() {
			paramKs = append(paramKs, e.tagHole(ks, direct, param, where == nil))
		}
	} else {
		// Handle escape analysis for builtins.

		// By default, we just discard everything. However, if
		// we're in a top-level defer statement, we can't
		// allow transient values.
		k := e.discardHole()
		if where != nil {
			loc := e.newLoc(where)
			loc.transient = false
			k = loc.asHole()
		}
		for range args {
			paramKs = append(paramKs, k)
		}

		switch call.Op {
		case OAPPEND:
			// Appendee slice may flow directly to the
			// result, if it has enough
			// capacity. Alternatively, a new heap slice
			// might be allocated, and all slice elements
			// might flow to heap.
			paramKs[0] = e.teeHole(paramKs[0], ks[0])
			if types.Haspointers(args[0].Type.Elem()) {
				paramKs[0] = e.teeHole(paramKs[0], e.heapHole().deref(call, "appendee slice"))
			}

			if call.IsDDD() {
				if args[1].Type.IsSlice() && types.Haspointers(args[1].Type.Elem()) {
					paramKs[1] = e.teeHole(paramKs[1], e.heapHole().deref(call, "appended slice..."))
				}
			} else {
				for i := 1; i < len(args); i++ {
					paramKs[i] = e.heapHole()
				}
			}

		case OCOPY:
			if call.Right.Type.IsSlice() && types.Haspointers(call.Right.Type.Elem()) {
				paramKs[1] = e.teeHole(paramKs[1], e.heapHole().deref(call, "copied slice"))
			}

		case OPANIC:
			paramKs[0] = e.heapHole()
		}
	}

	// TODO(mdempsky): Remove after early ddd-ification.
	if fntype != nil && fntype.IsVariadic() && !call.IsDDD() {
		vi := fntype.NumParams() - 1

		nva := call.List.Len()
		nva -= vi

		dddK := e.spill(paramKs[vi], call)
		paramKs = paramKs[:vi]
		for i := 0; i < nva; i++ {
			paramKs = append(paramKs, dddK)
		}

		if nva == 0 {
			call.Esc = 42 // flag for EscState.cleanup
		}
	}

	if call.Op == OCALLFUNC {
		k := e.discardHole()
		if where != nil {
			if where.Op == ODEFER && e.loopdepth == 1 {
				loc := e.newLoc(nil)
				loc.transient = false
				k = loc.asHole()
			} else {
				k = e.heapHole()
			}
		}
		e.value(k, call.Left)
	}

	if recv != nil {
		e.value(recvK, recv)
	}

	for i, arg := range args {
		// For arguments to go:uintptrescapes, peel
		// away an unsafe.Pointer->uintptr conversion,
		// if present.
		if direct && arg.Op == OCONVNOP && arg.Type.Etype == TUINTPTR && arg.Left.Type.Etype == TUNSAFEPTR {
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

// teeHole returns a new hole that flows into each of ks.
func (e *Escape) teeHole(ks ...EscHole) EscHole {
	if len(ks) == 0 {
		return e.discardHole()
	}
	if len(ks) == 1 {
		return ks[0]
	}

	// Given holes "l1 = _", "l2 = **_", "l3 = *_", ..., create a
	// new temporary location ltmp, wire it into place, and return
	// a hole for "ltmp = _".
	loc := e.newLoc(nil)
	for _, k := range ks {
		if k.derefs < 0 {
			// N.B., "p = &q" and "p = &tmp; tmp = q" are
			// not semantically equivalent. To combine
			// holes like "l1 = _" and "l2 = &_", we'd
			// need to wire them as "l1 = *ltmp" and "l2 =
			// ltmp" and return "ltmp = &_" instead.
			Fatalf("teeHole: negative derefs")
		}
		e.flow(k, loc)
	}
	return loc.asHole()
}

func (e *Escape) tagHole(ks []EscHole, direct bool, param *types.Field, transient bool) EscHole {
	tag := param.Note
	if debugLevel(2) {
		fmt.Printf("tagHole: [%v] = %q, direct=%v\n", ks, tag, direct)
	}

	if !direct {
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

	var tagKs []EscHole
	if !transient {
		loc := e.newLoc(nil)
		loc.transient = false
		tagKs = append(tagKs, loc.asHole())
	}

	if esc&EscContentEscapes != 0 {
		tagKs = append(tagKs, e.heapHole().shift(1))
	}

	for i, k := range ks {
		x := int(esc>>uint(EscReturnBits+i*bitsPerOutputInTag)) & int(bitsMaskForTag)
		if x != 0 {
			tagKs = append(tagKs, k.shift(x-1))
		}
	}

	return e.teeHole(tagKs...)
}

type EscLocation struct {
	n         *Node
	edges     []EscEdge
	curfn     *Node
	loopDepth int

	distance  int
	walkgen   uint32
	escapes   bool
	transient bool
	paramEsc  uint16
}

type EscEdge struct {
	src    *EscLocation
	derefs int
}

// An EscHole represents a context for evaluation a Go
// expression. Intuitively, when evaluating x in "l = **x", we'd have
// a hole with dst==l and derefs==2.
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

func (e *Escape) dcl(n *Node) EscHole {
	loc := e.oldLoc(n)
	loc.loopDepth = int(e.loopdepth)
	return loc.asHole()
}

func (e *Escape) spill(k EscHole, n *Node) EscHole {
	// TODO(mdempsky): Optimize. E.g., if k is the heap or blank,
	// then we already know whether n leaks, and we can return a
	// more optimized hole.
	loc := e.newLoc(n)
	e.flow(k.addr(n, "spill"), loc)
	return loc.asHole()
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

func (e *Escape) newLoc(n *Node) *EscLocation {
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
		transient: true,
	}
	allLocs = append(allLocs, loc)
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

func (e *Escape) oldLoc(n *Node) *EscLocation {
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

func (l *EscLocation) asHole() EscHole {
	return EscHole{dst: l}
}

func (l *EscLocation) String() string {
	switch l {
	case &HeapLoc:
		return "[heap]"
	case &BlankLoc:
		return "[blank]"
	}

	return fmt.Sprintf("%v", l.n)
}

func (e *Escape) flow(k EscHole, src_ *EscLocation) {
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

	dst.edges = append(dst.edges, EscEdge{src: src_, derefs: k.derefs})
	if debugLevel(2) {
		Warnl(pos, "flow: %v (%p) now has %v edges", dst, dst, len(dst.edges))
	}
}

func (e *Escape) heapHole() EscHole    { return HeapLoc.asHole() }
func (e *Escape) discardHole() EscHole { return BlankLoc.asHole() }

func (e *Escape) resultHoles() []EscHole {
	var ks []EscHole
	for _, f := range Curfn.Type.Results().FieldSlice() {
		ks = append(ks, e.addr(asNode(f.Nname)))
	}
	return ks
}

var escLocs = map[*Node]*EscLocation{}
var allLocs []*EscLocation

func (e *Escape) flood(all []*Node) {
	var walkgen uint32

	for _, loc := range allLocs {
		walkgen++
		e.walk(loc, walkgen)
	}

	walkgen++
	e.walk(&HeapLoc, walkgen)
}

func (e *Escape) walk(root *EscLocation, walkgen uint32) {
	if debugLevel(1) {
		Warnl(src.NoXPos, "esc2: walking from %v", root)
	}
	root.walkgen = walkgen
	root.distance = 0
	todo := []*EscLocation{root}
	for len(todo) > 0 {
		p := todo[0]
		todo = todo[1:]

		base := p.distance
		if debugLevel(1) {
			Warnl(src.NoXPos, "esc2: visiting %v (%p) at distance %v from root %v; %v edges", p, p, base, root, len(p.edges))
		}

		addressOf := base < 0
		if addressOf {
			base = 0

			// TODO(mdempsky): Explain this.
			if !root.transient {
				p.transient = false
			}
		}

		// p's address flows to root. If root outlives
		// p, then p needs to be heap allocated.
		if root.outlives(p) {
			if addressOf && !p.escapes {
				if debugLevel(1) {
					var pos src.XPos
					if p.n != nil {
						pos = p.n.Pos
					}
					Warnl(pos, "esc2: found a path from %v to %v that escapes", root, p)
				}
				p.escapes = true

				// TODO(mdempsky): This is clumsy.
				if root != &HeapLoc {
					e.flow(HeapLoc.asHole(), p)
				}
			}

			// p's value flows to root. If p is a function
			// parameter and root is the heap or a corresponding
			// result parameter, then record that value flow for
			// tagging the function later.
			if p.isName(PPARAM) {
				vi := -1
				if root.isName(PPARAMOUT) && root.n.Name.Curfn == p.n.Name.Curfn {
					// TODO(mdempsky): Eliminate dependency on Vargen here.
					vi = int(root.n.Name.Vargen) - 1
				}
				p.leak(vi, base)
			}
		}

		for _, edge := range p.edges {
			dist := base + edge.derefs
			if debugLevel(1) {
				Warnl(src.NoXPos, "esc2: edge from %v (%v) ~> %v (%v) at distance %v", p, p.distance, edge.src, edge.src.distance, dist)
			}
			if edge.src.walkgen != walkgen || edge.src.distance > dist {
				edge.src.walkgen = walkgen
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

func dddLen(n *Node) int {
	switch n.Op {
	case OCALLFUNC, OCALLMETH, OCALLINTER:
	default:
		Fatalf("%v doesn't need ... slice", n)
	}

	if !n.Left.Type.IsVariadic() {
		// TODO(mdempsky): Should this be an error?
		return 0
	}

	return n.List.Len() - (n.Left.Type.NumParams() - 1)
}

func (e *Escape) cleanup(all []*Node) {
	for n, loc := range escLocs {
		switch n.Op {
		case OTYPESW:
			continue
		case OCALLFUNC, OCALLMETH, OCALLINTER:
			elt := n.Left.Type.Params().Field(n.Left.Type.NumParams() - 1).Type.Elem()
			ddd := nodl(n.Pos, ODDDARG, nil, nil)
			ddd.Type = types.NewPtr(types.NewArray(elt, int64(dddLen(n))))

			n.Right = ddd
			n = ddd
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
			if loc.transient {
				switch n.Op {
				case OCALLPART, OCLOSURE, ODDDARG, OARRAYLIT, OSLICELIT, OPTRLIT, OSTRUCTLIT:
					n.SetNoescape(true)
				}
			}

			if Debug['m'] != 0 && n.Op != ONAME && n.Op != OTYPESW && n.Op != ORANGE && n.Op != ODEFER {
				Warnl(n.Pos, "%S %S does not escape", funcSym(loc.curfn), n)
			}
		}
	}

	escLocs = map[*Node]*EscLocation{}
	allLocs = nil

	HeapLoc = EscLocation{}
	BlankLoc = EscLocation{}
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
