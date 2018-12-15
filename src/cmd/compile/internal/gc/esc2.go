package gc

import (
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"fmt"
	"os"
	"strconv"
	"strings"
)

// TODO(mdempsky): Handle conversions and untyped values better.

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
			e.value(k.copy(n, "range"), n.Right)
		} else {
			e.value(k.deref(n, "range-deref"), n.Right)
		}

		e.loopdepth++
		e.stmts(n.Nbody)
		e.loopdepth--

	case OSWITCH:
		for _, cas := range n.List.Slice() { // cases
			if n.Left != nil && n.Left.Op == OTYPESW && cas.Rlist.Len() != 0 {
				// type switch variables have no ODCL.
				cv := cas.Rlist.First()
				k := e.dcl(cv)
				// TODO(mdempsky): Implicit ODOTTYPE.
				if types.Haspointers(cv.Type) {
					e.value(k.copy(n, "switch case"), n.Left.Right)
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
		// Filter out some no-op assignments for escape analysis.
		// TODO(mdempsky): Move into (*EscState).assign.
		if e.isSelfAssign(n.Left, n.Right) {
			if Debug['m'] != 0 {
				Warnl(n.Pos, "%v ignoring self-assignment in %S", e.curfnSym(n), n)
			}
			return
		}

		if debugLevel(3) {
			Dump("esc2 assignment", n)
		}
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
			e.call(ks, n.List.First())
		} else {
			for i, v := range n.List.Slice() {
				e.value(ks[i], v)
			}
		}
	case OCALLFUNC, OCALLMETH, OCALLINTER:
		e.call(nil, n)
	case OGO, ODEFER:
		if n.Op == ODEFER && e.loopdepth == 1 {
			e.call(nil, n.Left)
			break
		}

		hole := e.heapHole()
		e.value(hole, n.Left.Left)

		// TODO(mdempsky): Do I need to handle ... here?

		args := n.Left.List.Slice()
		if len(args) == 1 && args[0].Type.IsFuncArgStruct() {
			var holes []EscHole
			for i, n := 0, args[0].Type.NumFields(); i < n; i++ {
				holes = append(holes, hole)
			}
			e.call(holes, args[0])
		} else {
			for _, arg := range args {
				e.value(hole, arg)
			}
		}

	case ORETJMP:
		// TODO(mdempsky): What do? esc.go just ignores it.

	case OCLOSE:
		e.discard(n.Left)
	case OPANIC:
		e.assignHeap(n.Left, "panic", n)
	case ODELETE, OPRINT, OPRINTN:
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

	case OPLUS, ONEG, OBITNOT:
		e.value(k, n.Left)
	case OADD, OSUB, OOR, OXOR, OMUL, ODIV, OMOD, OLSH, ORSH, OAND, OANDNOT:
		e.value(k, n.Left)
		e.value(k, n.Right)

	case ONOT:
		e.discard(n.Left)
	case OEQ, ONE, OLT, OLE, OGT, OGE, OANDAND, OOROR:
		e.discard(n.Left)
		e.discard(n.Right)

	case OADDR:
		e.value(k.addr(n, "address-of"), n.Left) // "address-of"
	case ODEREF:
		e.value(k.deref(n, "indirection"), n.Left) // "indirection"
	case ODOT, ODOTTYPE, ODOTTYPE2, ODOTMETH, ODOTINTER:
		// TODO(mdempsky): deref for !isdirectiface types.
		e.value(k.copy(n, "dot"), n.Left)
	case ODOTPTR:
		e.value(k.deref(n, "dot of pointer"), n.Left) // "dot of pointer"
	case OINDEX:
		if n.Left.Type.IsArray() {
			e.value(k.copy(n, "fixed-array-index-of"), n.Left)
		} else {
			// TODO(mdempsky): Fix why reason text.
			e.value(k.deref(n, "dot of pointer"), n.Left)
		}
		e.discard(n.Right)
	case OINDEXMAP:
		e.discard(n.Left)
		e.discard(n.Right)
	case OSLICE, OSLICEARR, OSLICE3, OSLICE3ARR, OSLICESTR:
		e.value(k.copy(n, "slice"), n.Left)
		low, high, max := n.SliceBounds()
		e.discard(low)
		e.discard(high)
		e.discard(max)

	case OCONV, OCONVNOP:
		e.value(k, n.Left)
	case OCONVIFACE:
		if !n.Left.Type.IsInterface() && !isdirectiface(n.Left.Type) {
			k = e.spill(k, n)
		}
		e.value(k.copy(n, "interface-converted"), n.Left)

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
		// e.spill(k, n)
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
		e.value(e.spill(k, n).copy(n, "pointer literal [assign]"), n.Left)

	case OARRAYLIT:
		for _, elt := range n.List.Slice() {
			if elt.Op == OKEY {
				elt = elt.Right
			}
			e.value(k.copy(n, "array literal element"), elt)
		}

	case OSLICELIT:
		// Slice is not leaked until proven otherwise
		k = e.spill(k, n)

		// Link values to slice
		for _, elt := range n.List.Slice() {
			if elt.Op == OKEY {
				elt = elt.Right
			}
			e.value(k.copy(n, "slice-literal-element"), elt)
		}

	case OSTRUCTLIT:
		for _, elt := range n.List.Slice() {
			if types.Haspointers(elt.Left.Type) {
				e.value(k.copy(n, "struct literal element"), elt.Left)
			}
		}

	case OMAPLIT:
		// e.spill(k, n) // TODO(mdempsky): Always leaks.

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

			// TODO(mdempsky): Sloppy typing.
			e.value(k.copy(n, "captured by a closure"), v.Name.Defn)
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
		// TODO(mdempsky): might be append(f())
		args := n.List.Slice()

		// TODO(mdempsky): This matches esc.go's semantics
		// (leaking the appendee slice's contents to heap),
		// but I think e.value(k, args[0]) would be correct.
		tee := e.newLoc(nil)
		e.flow(k, tee)
		e.flow(e.heapHole().deref(n, "appendee slice"), tee)
		e.value(EscHole{dst: tee}, args[0])

		if n.IsDDD() {
			e.assignHeapDeref(args[1], "appended slice...", n)
		} else {
			for _, arg := range args[1:] {
				e.assignHeap(arg, "appended to slice", n)
			}
		}

	case OCOPY:
		e.discard(n.Left)
		if !n.Right.Type.IsString() {
			e.assignHeapDeref(n.Right, "copied slice", n)
		}
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

	if !types.Haspointers(n.Type) && !isReflectHeaderDataField(n) {
		return e.discardHole()
	}

	switch n.Op {
	default:
		Fatalf("unexpected addr: %v", n)
	case ONAME:
		if n.Class() == PFUNC {
			Fatalf("bad")
		}
		if n.Class() == PEXTERN {
			return e.heapHole()
		}
		if n.IsClosureVar() {
			n = n.Name.Defn
		}
		return EscHole{dst: e.oldLoc(n)}
	case ODOT:
		return e.addr(n.Left)
	case OINDEX:
		e.discard(n.Right)
		if n.Left.Type.IsArray() {
			return e.addr(n.Left)
		} else {
			e.discard(n.Left)
		}
	case ODEREF, ODOTPTR:
		e.discard(n)
	case OINDEXMAP:
		e.discard(n.Left)
		e.assignHeap(n.Right, "key of map put", n)
	}
	return e.heapHole()
}

func (e *EscState) addrs(l Nodes) []EscHole {
	var ks []EscHole
	for _, n := range l.Slice() {
		ks = append(ks, e.addr(n))
	}
	return ks
}

func (e *EscState) assign(dst, src *Node, why string, where *Node) {
	if dst != nil && !types.Haspointers(dst.Type) && !isReflectHeaderDataField(dst) {
		return
	}

	e.value(e.addr(dst), src)
}

func (e *EscState) assignHeap(src *Node, why string, where *Node) {
	e.value(e.heapHole().copy(where, why), src)
}

func (e *EscState) assignHeapDeref(src *Node, why string, where *Node) {
	e.value(e.heapHole().deref(where, why), src)
}

func (e *EscState) call(ks []EscHole, call *Node) {
	if ks != nil && len(ks) != call.Left.Type.NumResults() {
		Warnl(call.Pos, "expect %v values, but %v has %v results", len(ks), call.Left, call.Left.Type.NumResults())
	}

	var indirect bool
	var fn *Node
	switch call.Op {
	default:
		Fatalf("esccall")

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

	// Warnl(call.Pos, "figuring out how to call %v", call)

	if !indirect && fn != nil && fn.Op == ONAME && fn.Class() == PFUNC &&
		fn.Name.Defn != nil && fn.Name.Defn.Nbody.Len() != 0 && fn.Name.Param.Ntype != nil && fn.Name.Defn.Esc < EscFuncTagged {

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
		} else if indirect { // indirect and OCALLFUNC = could be captured variables, too. (#14409)
			if len(ks) == 0 {
				e.value(e.discardHole(), fn)
			} else {
				// TODO(mdempsky): Evaluate fn into a
				// temporary location instead and flow
				// that to all of ks.
				for _, k := range ks {
					e.value(k.deref(call, "captured by called closure"), fn)
				}
			}
		}

		for _, param := range fntype.Params().FieldSlice() {
			paramKs = append(paramKs, e.tagHole(ks, indirect, param))
		}
	}

	if call.Op != OCALLFUNC {
		e.value(recvK, call.Left.Left)
	}

	if fntype.IsVariadic() && !call.IsDDD() {
		vi := fntype.NumParams() - 1

		nva := call.List.Len()
		if nva == 1 && call.List.First().Type.IsFuncArgStruct() {
			nva = call.List.First().Type.NumFields()
		}
		nva -= vi

		ddd := nod(ODDDARG, nil, nil)
		ddd.Pos = call.Pos
		ddd.Type = types.NewPtr(types.NewArray(fntype.Params().Field(vi).Type.Elem(), int64(nva)))
		call.Right = ddd
		// TODO(mdempsky): Better rationalize this deref.
		dddK := e.spill(paramKs[vi].deref(call, "ddd hack"), ddd)

		paramKs = paramKs[:vi]
		for i := 0; i < nva; i++ {
			paramKs = append(paramKs, dddK)
		}
	}

	// TODO(mdempsky): Handle implicit conversions?

	if len(paramKs) > 1 && call.List.Len() == 1 {
		e.call(paramKs, call.List.First())
	} else {
		for i, arg := range call.List.Slice() {
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
		e.flow(e.heapHole().shift(1, nil, ""), loc)
	}

	for i, k := range ks {
		x := int(esc>>uint(EscReturnBits+i*bitsPerOutputInTag)) & int(bitsMaskForTag)
		if x != 0 {
			e.flow(k.shift(int(x-1), nil, ""), loc)
		}
	}

	return EscHole{dst: loc}
}

type EscLocation struct {
	n         *Node
	edges     []EscEdge
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

// TODO(mdempsky): Better name than copy? I'm worried that suggests
// copying values, whereas this is really about just adding another
// breadcrumb to the EscHole trail without adjusting the derefs
// semantics.
func (k EscHole) copy(where *Node, why string) EscHole  { return k.shift(0, where, why) }
func (k EscHole) deref(where *Node, why string) EscHole { return k.shift(1, where, why) }
func (k EscHole) addr(where *Node, why string) EscHole  { return k.shift(-1, where, why) }

func (k EscHole) shift(delta int, where *Node, why string) EscHole {
	// k0 := k
	k.derefs += delta
	if k.derefs < -1 {
		Fatalf("derefs underflow: %v", k.derefs)
	}
	// fmt.Printf("shift(%v, %v, %v): %v -> %v\n", delta, where, why, k0, k)
	return k
}

func (e *EscState) dcl(n *Node) EscHole {
	return e.spill(e.discardHole(), n)
}

func (e *EscState) spill(k EscHole, n *Node) EscHole {
	// TODO(mdempsky): Cleanup. Maybe move to newLoc?
	if /*n.Esc != EscHeap &&*/ n.Type != nil &&
		(n.Type.Width > maxStackVarSize ||
			(n.Op == ONEW || n.Op == OPTRLIT) && n.Type.Elem().Width >= maxImplicitStackVarSize ||
			n.Op == OMAKESLICE && !isSmallMakeSlice(n)) {
		if debugLevel(2) {
			Warnl(n.Pos, "spilling %v directly to the heap", n)
		}
		k = e.heapHole()
	}

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
		loopDepth: int(e.loopdepth),
	}
	if n != nil {
		escLocs[n] = loc
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

	if k.derefs < 0 && dst.loopDepth < src_.loopDepth {
		if debugLevel(2) {
			Warnl(pos, "esc2: %v (%d) <~ %v (%d), derefs=%v (linked to heap)", dst, dst.loopDepth, src_, src_.loopDepth, k.derefs)
		}
		dst = &HeapLoc
	} else {
		if debugLevel(2) {
			Warnl(pos, "esc2: %v <~ %v, derefs=%v (emad)", dst, src_, k.derefs)
		}
	}

	// TODO(mdempsky): Deduplicate edges?

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
		for _, dcl := range fn.Func.Dcl {
			if dcl.Op == ONAME && (dcl.Class() == PPARAM || dcl.Class() == PPARAMOUT) {
				loc := e.newLoc(dcl)
				if dcl.Class() == PPARAM {
					if fn.Nbody.Len() == 0 && !fn.Noescape() {
						loc.paramEsc = EscHeap
					}
				}
			}
		}
	}
}

func (e *EscState) flood(all []*Node) {
	for _, fn := range all {
		if fn.Op != ODCLFUNC {
			Warnl(fn.Pos, "what is it? %v", fn)
			continue
		}
		for _, dcl := range fn.Func.Dcl {
			if dcl.Op == ONAME && dcl.Class() == PPARAMOUT {
				e.walk(e.oldLoc(dcl))
			}
		}
	}

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
			if !p.escapes && debugLevel(1) {
				var pos src.XPos
				if p.n != nil {
					pos = p.n.Pos
				}
				Warnl(pos, "esc2: found a path from %v to %v that escapes", root, p)
			}
			p.escapes = true
			if root != &HeapLoc {
				e.flow(EscHole{dst: &HeapLoc}, p)
			}
		}
		if p.n != nil && p.n.Op == ONAME && p.n.Class() == PPARAM && p.paramEsc != EscHeap {
			if root == &HeapLoc {
				if base > 0 {
					p.paramEsc |= EscContentEscapes
				} else {
					p.paramEsc = EscHeap
				}
			} else if root.n != nil && root.n.Op == ONAME && root.n.Class() == PPARAMOUT && root.n.Name.Curfn == p.n.Name.Curfn {
				x := 1 + uint16(base)
				if base > maxEncodedLevel {
					x = 1 + uint16(maxEncodedLevel)
				}

				shift := uint(EscReturnBits + (root.n.Name.Vargen-1)*bitsPerOutputInTag)
				if (x<<shift)>>shift != x {
					// Encoding spill.
					p.paramEsc = EscHeap
				} else if old := (p.paramEsc >> shift) & bitsMaskForTag; old == 0 || x < old {
					p.paramEsc = (p.paramEsc &^ (bitsMaskForTag << shift)) | (x << shift)
				}
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

func debugLevel(x int) bool {
	return Debug['m'] >= x && os.Getenv("ESC2") != ""
}

func (e *EscState) cleanup() {
	for n, loc := range escLocs {
		escaped := n.Op != ONAME && n.Esc == EscHeap || n.Op == ONAME && n.Class() == PAUTOHEAP
		if escaped != loc.escapes {
			Warnl(n.Pos, "noooo: %v is 0x%x, but %v", n, n.Esc, loc.escapes)
		}

		if n.Op == ONAME && n.Class() == PAUTOHEAP {
			n = n.Name.Param.Stackcopy
			if n == nil {
				continue
			}
		}
		if n.Op == ONAME && n.Class() == PPARAM && types.Haspointers(n.Type) {
			want := n.Esc
			if want == EscReturn|EscContentEscapes {
				// esc.go leaves EscReturn sometimes
				// when it doesn't matter.
				want = EscNone | EscContentEscapes
			}

			loc.paramEsc = finalizeEsc(loc.paramEsc)
			if want != loc.paramEsc {
				Warnl(n.Pos, "waahh: %v is 0x%x, but 0x%x", n, want, loc.paramEsc)
			}
		}
	}

	escLocs = map[*Node]*EscLocation{}

	HeapLoc = EscLocation{}
	BlankLoc = EscLocation{}
}

func finalizeEsc(esc uint16) uint16 {
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

	if esc>>EscReturnBits != 0 {
		esc |= EscReturn
	} else if esc&EscMask == 0 {
		esc |= EscNone
	}

	return esc
}
