// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Garbage collector liveness bitmap generation.

// The command line flag -live causes this code to print debug information.
// The levels are:
//
//	-live (aka -live=1): print liveness lists as code warnings at safe points
//	-live=2: print an assembly listing with liveness annotations
//	-live=3: print information during each computation phase (much chattier)
//
// Each level includes the earlier output as well.

package gc

import (
	"bytes"
	"cmd/compile/internal/ssa"
	"cmd/internal/obj"
	"cmd/internal/sys"
	"crypto/md5"
	"fmt"
	"strings"
)

const (
	UNVISITED = 0
	VISITED   = 1
)

type BlockEffect struct {
	succs []*BlockEffect
	preds []*BlockEffect

	lastbitmapindex int // for livenessepilogue

	// Summary sets of block effects.

	// Computed during livenessprologue using only the content of
	// individual blocks:
	//
	//	uevar: upward exposed variables (used before set in block)
	//	varkill: killed variables (set in block)
	//	avarinit: addrtaken variables set or used (proof of initialization)
	uevar    bvec
	varkill  bvec
	avarinit bvec

	// Computed during livenesssolve using control flow information:
	//
	//	livein: variables live at block entry
	//	liveout: variables live at block exit
	//	avarinitany: addrtaken variables possibly initialized at block exit
	//		(initialized in block or at exit from any predecessor block)
	//	avarinitall: addrtaken variables certainly initialized at block exit
	//		(initialized in block or at exit from all predecessor blocks)
	livein      bvec
	liveout     bvec
	avarinitany bvec
	avarinitall bvec
}

// A collection of global state used by liveness analysis.
type Liveness struct {
	fn   *Node
	ptxt *obj.Prog
	vars []*Node
	bes  []*BlockEffect

	f          *ssa.Func
	valueProgs map[*obj.Prog]*ssa.Value
	blockProgs map[*obj.Prog]*ssa.Block

	callpos map[*ssa.Value]int32

	// An array with a bit vector for each safe point tracking live pointers
	// in the arguments and locals area, indexed by bb.rpo.
	argslivepointers []bvec
	livepointers     []bvec

	cache progeffectscache
}

type progeffectscache struct {
	tailuevar    []int32
	retuevar     []int32
	textavarinit []int32
}

// ProgInfo holds information about the instruction for use
// by clients such as the compiler. The exact meaning of this
// data is up to the client and is not interpreted by the cmd/internal/obj/... packages.
type ProgInfo struct {
	_     struct{} // to prevent unkeyed literals. Trailing zero-sized field will take space.
	Flags uint32   // flag bits
}

// Inserts new after p.
func spliceafter(p, new *obj.Prog) {
	new.Link = p.Link
	p.Link = new
}

// livenessShouldTrack reports whether the liveness analysis
// should track the variable n.
// We don't care about variables that have no pointers,
// nor do we care about non-local variables,
// nor do we care about empty structs (handled by the pointer check),
// nor do we care about the fake PAUTOHEAP variables.
func livenessShouldTrack(n *Node) bool {
	return n.Op == ONAME && (n.Class == PAUTO || n.Class == PPARAM || n.Class == PPARAMOUT) && haspointers(n.Type)
}

// getvariables returns the list of on-stack variables that we need to track.
func getvariables(fn *Node) []*Node {
	var vars []*Node
	for _, n := range fn.Func.Dcl {
		if n.Op == ONAME {
			// The Node.opt field is available for use by optimization passes.
			// We use it to hold the index of the node in the variables array
			// (nil means the Node is not in the variables array).
			// The Node.curfn field is supposed to be set to the current function
			// already, but for some compiler-introduced names it seems not to be,
			// so fix that here.
			// Later, when we want to find the index of a node in the variables list,
			// we will check that n.Curfn == Curfn and n.Opt() != nil. Then n.Opt().(int32)
			// is the index in the variables list.
			n.SetOpt(nil)
			n.Name.Curfn = Curfn
		}

		if livenessShouldTrack(n) {
			n.SetOpt(int32(len(vars)))
			vars = append(vars, n)
		}
	}

	return vars
}

// A pattern matcher for call instructions. Returns true when the instruction
// is a call to a specific package qualified function name.
func iscall(prog *obj.Prog, name *obj.LSym) bool {
	if prog == nil {
		Fatalf("iscall: prog is nil")
	}
	if name == nil {
		Fatalf("iscall: function name is nil")
	}
	if prog.As != obj.ACALL {
		return false
	}
	return name == prog.To.Sym
}

var (
	newselect   *obj.LSym
	selectNames [4]*obj.LSym
	selectgo    *obj.LSym
)

var isdeferreturn_sym *obj.LSym

func isdeferreturn(prog *obj.Prog) bool {
	if isdeferreturn_sym == nil {
		isdeferreturn_sym = Linksym(Pkglookup("deferreturn", Runtimepkg))
	}
	return iscall(prog, isdeferreturn_sym)
}

// Returns true if the node names a variable that is otherwise uninteresting to
// the liveness computation.
func isfunny(n *Node) bool {
	return n.Sym != nil && (n.Sym.Name == ".fp" || n.Sym.Name == ".args")
}

func (lv *Liveness) initcache() {
	for i, node := range lv.vars {
		switch node.Class {
		case PPARAM:
			// A return instruction with a p.to is a tail return, which brings
			// the stack pointer back up (if it ever went down) and then jumps
			// to a new function entirely. That form of instruction must read
			// all the parameters for correctness, and similarly it must not
			// read the out arguments - they won't be set until the new
			// function runs.
			lv.cache.tailuevar = append(lv.cache.tailuevar, int32(i))

			if node.Addrtaken {
				lv.cache.textavarinit = append(lv.cache.textavarinit, int32(i))
			}

		case PPARAMOUT:
			// If the result had its address taken, it is being tracked
			// by the avarinit code, which does not use uevar.
			// If we added it to uevar too, we'd not see any kill
			// and decide that the variable was live entry, which it is not.
			// So only use uevar in the non-addrtaken case.
			// The p.to.type == obj.TYPE_NONE limits the bvset to
			// non-tail-call return instructions; see note below for details.
			if !node.Addrtaken {
				lv.cache.retuevar = append(lv.cache.retuevar, int32(i))
			}
		}
	}
}

// Computes the effects of an instruction on a set of
// variables. The vars argument is a slice of *Nodes.
//
// The output vectors give bits for variables:
//	uevar - used by this instruction
//	varkill - killed by this instruction
//		for variables without address taken, means variable was set
//		for variables with address taken, means variable was marked dead
//	avarinit - initialized or referred to by this instruction,
//		only for variables with address taken but not escaping to heap
//
// The avarinit output serves as a signal that the data has been
// initialized, because any use of a variable must come after its
// initialization.

type Effect int

const (
	Uevar Effect = 1 << iota
	Varkill
	Avarinit
)

func (lv *Liveness) progeffects(v *ssa.Value) (int32, Effect) {
	n, flags := valueEffect(v)
	pos := liveIndex(n, lv.vars)
	if pos < 0 {
		return -1, 0
	}

	if n.Addrtaken {
		if v.Op == ssa.OpVarKill {
			return pos, Varkill
		}
		if v.Op == ssa.OpVarDef {
			return pos, Varkill | Avarinit
		}
		return pos, Avarinit
	}

	var effect Effect
	if flags&MemRead != 0 {
		effect |= Uevar
	}
	if flags&MemWrite != 0 && (!isfat(n.Type) || v.Op == ssa.OpVarDef) {
		effect |= Varkill
	}
	return pos, effect
}

// liveIndex returns the index of n in the set of tracked vars.
// If n is not a tracked var, liveIndex returns -1.
// If n is not a tracked var but should be tracked, liveIndex crashes.
func liveIndex(n *Node, vars []*Node) int32 {
	if n == nil || n.Name.Curfn != Curfn || !livenessShouldTrack(n) {
		return -1
	}

	pos, ok := n.Opt().(int32) // index in vars
	if !ok {
		Fatalf("lost track of variable in liveness: %v (%p, %p)", n, n, n.Orig)
	}
	if pos >= int32(len(vars)) || vars[pos] != n {
		Fatalf("bad bookkeeping in liveness: %v (%p, %p)", n, n, n.Orig)
	}
	return pos
}

// Constructs a new liveness structure used to hold the global state of the
// liveness computation. The cfg argument is a slice of *BasicBlocks and the
// vars argument is a slice of *Nodes.
func newliveness(fn *Node, ptxt *obj.Prog, vars []*Node, f *ssa.Func, valueProgs map[*obj.Prog]*ssa.Value, blockProgs map[*obj.Prog]*ssa.Block) *Liveness {
	bes := make([]*BlockEffect, f.NumBlocks())

	result := Liveness{
		fn:   fn,
		ptxt: ptxt,
		bes:  bes,
		vars: vars,

		f:          f,
		valueProgs: valueProgs,
		blockProgs: blockProgs,

		callpos: make(map[*ssa.Value]int32),
	}

	nblocks := int32(len(f.Blocks))
	nvars := int32(len(vars))
	bulk := bvbulkalloc(nvars, nblocks*7)
	for _, b := range f.Blocks {
		// TODO(mdempsky): Bulk allocate BlockEffects.
		bb := new(BlockEffect)
		bes[b.ID] = bb

		bb.uevar = bulk.next()
		bb.varkill = bulk.next()
		bb.livein = bulk.next()
		bb.liveout = bulk.next()
		bb.avarinit = bulk.next()
		bb.avarinitany = bulk.next()
		bb.avarinitall = bulk.next()
	}

	for _, b := range f.Blocks {
		bb := bes[b.ID]
		for _, succ := range b.Succs {
			bb.succs = append(bb.succs, bes[succ.Block().ID])
		}
		for _, pred := range b.Preds {
			bb.preds = append(bb.preds, bes[pred.Block().ID])
		}
	}

	// Select statements are implemented with a setjmp / longjmp
	// mechanism: the select{send,recv,recv2,default} functions
	// are analogous to setjmp, and selectgo is analogous to
	// longjmp.
	//
	// In the SSA CFG, selectgo is represented as a function call
	// that never returns. A naive analysis would erroneously
	// infer that all local variables are dead at selectgo. To
	// correct that, we construct a new CFG that also includes
	// edges from selectgo calls to their corresponding selectfoo
	// calls' case body block.

	if newselect == nil {
		newselect = Linksym(Pkglookup("newselect", Runtimepkg))
		selectNames[0] = Linksym(Pkglookup("selectsend", Runtimepkg))
		selectNames[1] = Linksym(Pkglookup("selectrecv", Runtimepkg))
		selectNames[2] = Linksym(Pkglookup("selectrecv2", Runtimepkg))
		selectNames[3] = Linksym(Pkglookup("selectdefault", Runtimepkg))
		selectgo = Linksym(Pkglookup("selectgo", Runtimepkg))
	}

	for _, b := range f.Blocks {
		if !blockcallsany(b, newselect) {
			continue
		}
		var succIDs []ssa.ID
		for b1 := b; ; {
			if blockcallsany(b1, selectNames[:]...) {
				succIDs = append(succIDs, b1.Succs[0].Block().ID)
				b1 = b1.Succs[1].Block()
				continue
			}
			if blockcallsany(b1, selectgo) {
				// Add edges from b1 to each ID in succIDs.
				bb := bes[b1.ID]
				for _, succID := range succIDs {
					bbs := bes[succID]
					bb.succs = append(bb.succs, bbs)
					bbs.preds = append(bbs.preds, bb)
				}
				break
			}

			b1 = b1.Succs[0].Block()
		}
	}

	return &result
}

func blockcallsany(b *ssa.Block, syms ...*obj.LSym) bool {
	for _, v := range b.Values {
		if v.Op != ssa.OpAMD64CALLstatic {
			continue
		}
		for _, sym := range syms {
			if v.Aux.(*obj.LSym) == sym {
				return true
			}
		}
	}
	return false
}

func (lv *Liveness) printeffects(v *ssa.Value, npos int32, effect Effect) {
	var bv bvec
	if effect != 0 {
		bv = bvalloc(int32(len(lv.vars)))
		bv.Set(npos)
	}

	var uevar, varkill, avarinit bvec
	if effect&Uevar != 0 {
		uevar = bv
	}
	if effect&Varkill != 0 {
		varkill = bv
	}
	if effect&Avarinit != 0 {
		avarinit = bv
	}

	fmt.Printf("effects of %v\n", v)
	fmt.Println("uevar:", uevar)
	fmt.Println("varkill:", varkill)
	fmt.Println("avarinit:", avarinit)
}

// Pretty print a variable node. Uses Pascal like conventions for pointers and
// addresses to avoid confusing the C like conventions used in the node variable
// names.
func printnode(node *Node) {
	p := ""
	if haspointers(node.Type) {
		p = "^"
	}
	a := ""
	if node.Addrtaken {
		a = "@"
	}
	fmt.Printf(" %v%s%s", node, p, a)
}

// Pretty print a list of variables. The vars argument is a slice of *Nodes.
func printvars(name string, bv bvec, vars []*Node) {
	fmt.Printf("%s:", name)
	for i, node := range vars {
		if bv.Get(int32(i)) {
			printnode(node)
		}
	}
	fmt.Printf("\n")
}

func checkauto(fn *Node, p *obj.Prog, n *Node) {
	for _, ln := range fn.Func.Dcl {
		if ln.Op == ONAME && ln.Class == PAUTO && ln == n {
			return
		}
	}

	if n == nil {
		fmt.Printf("%v: checkauto %v: nil node in %v\n", p.Line(), Curfn, p)
		return
	}

	fmt.Printf("checkauto %v: %v (%p; class=%d) not found in %p %v\n", funcSym(Curfn), n, n, n.Class, p, p)
	for _, ln := range fn.Func.Dcl {
		fmt.Printf("\t%v (%p; class=%d)\n", ln, ln, ln.Class)
	}
	yyerror("checkauto: invariant lost")
}

func checkparam(fn *Node, p *obj.Prog, n *Node) {
	if isfunny(n) {
		return
	}
	for _, a := range fn.Func.Dcl {
		if a.Op == ONAME && (a.Class == PPARAM || a.Class == PPARAMOUT) && a == n {
			return
		}
	}

	fmt.Printf("checkparam %v: %v (%p; class=%d) not found in %v\n", Curfn, n, n, n.Class, p)
	for _, ln := range fn.Func.Dcl {
		fmt.Printf("\t%v (%p; class=%d)\n", ln, ln, ln.Class)
	}
	yyerror("checkparam: invariant lost")
}

func checkprog(fn *Node, p *obj.Prog) {
	if p.From.Name == obj.NAME_AUTO {
		checkauto(fn, p, p.From.Node.(*Node))
	}
	if p.From.Name == obj.NAME_PARAM {
		checkparam(fn, p, p.From.Node.(*Node))
	}
	if p.To.Name == obj.NAME_AUTO {
		checkauto(fn, p, p.To.Node.(*Node))
	}
	if p.To.Name == obj.NAME_PARAM {
		checkparam(fn, p, p.To.Node.(*Node))
	}
}

// Check instruction invariants. We assume that the nodes corresponding to the
// sources and destinations of memory operations will be declared in the
// function. This is not strictly true, as is the case for the so-called funny
// nodes and there are special cases to skip over that stuff. The analysis will
// fail if this invariant blindly changes.
func checkptxt(fn *Node, firstp *obj.Prog) {
	if debuglive == 0 {
		return
	}

	for p := firstp; p != nil; p = p.Link {
		if false {
			fmt.Printf("analyzing '%v'\n", p)
		}
		checkprog(fn, p)
	}
}

// NOTE: The bitmap for a specific type t should be cached in t after the first run
// and then simply copied into bv at the correct offset on future calls with
// the same type t. On https://rsc.googlecode.com/hg/testdata/slow.go, onebitwalktype1
// accounts for 40% of the 6g execution time.
func onebitwalktype1(t *Type, xoffset *int64, bv bvec) {
	if t.Align > 0 && *xoffset&int64(t.Align-1) != 0 {
		Fatalf("onebitwalktype1: invalid initial alignment, %v", t)
	}

	switch t.Etype {
	case TINT8,
		TUINT8,
		TINT16,
		TUINT16,
		TINT32,
		TUINT32,
		TINT64,
		TUINT64,
		TINT,
		TUINT,
		TUINTPTR,
		TBOOL,
		TFLOAT32,
		TFLOAT64,
		TCOMPLEX64,
		TCOMPLEX128:
		*xoffset += t.Width

	case TPTR32,
		TPTR64,
		TUNSAFEPTR,
		TFUNC,
		TCHAN,
		TMAP:
		if *xoffset&int64(Widthptr-1) != 0 {
			Fatalf("onebitwalktype1: invalid alignment, %v", t)
		}
		bv.Set(int32(*xoffset / int64(Widthptr))) // pointer
		*xoffset += t.Width

	case TSTRING:
		// struct { byte *str; intgo len; }
		if *xoffset&int64(Widthptr-1) != 0 {
			Fatalf("onebitwalktype1: invalid alignment, %v", t)
		}
		bv.Set(int32(*xoffset / int64(Widthptr))) //pointer in first slot
		*xoffset += t.Width

	case TINTER:
		// struct { Itab *tab;	void *data; }
		// or, when isnilinter(t)==true:
		// struct { Type *type; void *data; }
		if *xoffset&int64(Widthptr-1) != 0 {
			Fatalf("onebitwalktype1: invalid alignment, %v", t)
		}
		bv.Set(int32(*xoffset / int64(Widthptr)))   // pointer in first slot
		bv.Set(int32(*xoffset/int64(Widthptr) + 1)) // pointer in second slot
		*xoffset += t.Width

	case TSLICE:
		// struct { byte *array; uintgo len; uintgo cap; }
		if *xoffset&int64(Widthptr-1) != 0 {
			Fatalf("onebitwalktype1: invalid TARRAY alignment, %v", t)
		}
		bv.Set(int32(*xoffset / int64(Widthptr))) // pointer in first slot (BitsPointer)
		*xoffset += t.Width

	case TARRAY:
		for i := int64(0); i < t.NumElem(); i++ {
			onebitwalktype1(t.Elem(), xoffset, bv)
		}

	case TSTRUCT:
		var o int64
		for _, t1 := range t.Fields().Slice() {
			fieldoffset := t1.Offset
			*xoffset += fieldoffset - o
			onebitwalktype1(t1.Type, xoffset, bv)
			o = fieldoffset + t1.Type.Width
		}

		*xoffset += t.Width - o

	default:
		Fatalf("onebitwalktype1: unexpected type, %v", t)
	}
}

// Returns the number of words of local variables.
func localswords() int32 {
	return int32(stkptrsize / int64(Widthptr))
}

// Returns the number of words of in and out arguments.
func argswords() int32 {
	return int32(Curfn.Type.ArgWidth() / int64(Widthptr))
}

// Generates live pointer value maps for arguments and local variables. The
// this argument and the in arguments are always assumed live. The vars
// argument is a slice of *Nodes.
func onebitlivepointermap(lv *Liveness, liveout bvec, vars []*Node, args bvec, locals bvec) {
	var xoffset int64

	for i := int32(0); ; i++ {
		i = liveout.Next(i)
		if i < 0 {
			break
		}
		node := vars[i]
		switch node.Class {
		case PAUTO:
			xoffset = node.Xoffset + stkptrsize
			onebitwalktype1(node.Type, &xoffset, locals)

		case PPARAM, PPARAMOUT:
			xoffset = node.Xoffset
			onebitwalktype1(node.Type, &xoffset, args)
		}
	}
}

// Construct a disembodied instruction.
func unlinkedprog(as obj.As) *obj.Prog {
	p := Ctxt.NewProg()
	Clearp(p)
	p.As = as
	return p
}

// Construct a new PCDATA instruction associated with and for the purposes of
// covering an existing instruction.
func newpcdataprog(prog *obj.Prog, index int32) *obj.Prog {
	pcdata := unlinkedprog(obj.APCDATA)
	pcdata.Pos = prog.Pos
	pcdata.From.Type = obj.TYPE_CONST
	pcdata.From.Offset = obj.PCDATA_StackMapIndex
	pcdata.To.Type = obj.TYPE_CONST
	pcdata.To.Offset = int64(index)
	return pcdata
}

// Initializes the sets for solving the live variables. Visits all the
// instructions in each basic block to summarizes the information at each basic
// block
func livenessprologue(lv *Liveness) {
	lv.initcache()

	for _, b := range lv.f.Blocks {
		bb := lv.bes[b.ID]

		// Walk the block instructions backward and update the block
		// effects with the each prog effects.
		for i := len(b.Values) - 1; i >= 0; i-- {
			v := b.Values[i]
			pos, effect := lv.progeffects(v)
			if debuglive >= 3 {
				lv.printeffects(v, pos, effect)
			}
			if effect&Varkill != 0 {
				bb.varkill.Set(pos)
				bb.uevar.Unset(pos)
			}
			if effect&Uevar != 0 {
				bb.uevar.Set(pos)
			}
		}

		// Walk the block instructions forward to update avarinit bits.
		// avarinit describes the effect at the end of the block, not the beginning.
		for _, v := range b.Values {
			pos, effect := lv.progeffects(v)
			if debuglive >= 3 {
				lv.printeffects(v, pos, effect)
			}
			if effect&Varkill != 0 {
				bb.avarinit.Unset(pos)
			}
			if effect&Avarinit != 0 {
				bb.avarinit.Set(pos)
			}
		}
	}
}

// Solve the liveness dataflow equations.
func livenesssolve(lv *Liveness) {
	// These temporary bitvectors exist to avoid successive allocations and
	// frees within the loop.
	newlivein := bvalloc(int32(len(lv.vars)))

	newliveout := bvalloc(int32(len(lv.vars)))
	any := bvalloc(int32(len(lv.vars)))
	all := bvalloc(int32(len(lv.vars)))

	// Push avarinitall, avarinitany forward.
	// avarinitall says the addressed var is initialized along all paths reaching the block exit.
	// avarinitany says the addressed var is initialized along some path reaching the block exit.
	for _, b := range lv.f.Blocks {
		bb := lv.bes[b.ID]

		bb.avarinitall.Clear()
		bb.avarinitall.Not()
		bb.avarinitany.Copy(bb.avarinit)
	}

	for change := true; change; {
		change = false
		for _, b := range lv.f.Blocks {
			bb := lv.bes[b.ID]

			lv.entryvarinit(b, any, all)

			any.AndNot(any, bb.varkill)
			all.AndNot(all, bb.varkill)
			any.Or(any, bb.avarinit)
			all.Or(all, bb.avarinit)
			if !any.Eq(bb.avarinitany) {
				change = true
				bb.avarinitany.Copy(any)
			}

			if !all.Eq(bb.avarinitall) {
				change = true
				bb.avarinitall.Copy(all)
			}
		}
	}

	// Iterate through the blocks in reverse round-robin fashion. A work
	// queue might be slightly faster. As is, the number of iterations is
	// so low that it hardly seems to be worth the complexity.

	for change := true; change; {
		change = false

		// Walk blocks in the general direction of propagation. This
		// improves convergence.
		for i := len(lv.f.Blocks) - 1; i >= 0; i-- {
			b := lv.f.Blocks[i]
			bb := lv.bes[b.ID]

			// A variable is live on output from this block
			// if it is live on input to some successor.
			//
			// out[b] = \bigcup_{s \in succ[b]} in[s]
			newliveout.Clear()
			if uevar, ok := lv.exitblockuses(b); ok {
				for _, pos := range uevar {
					newliveout.Set(pos)
				}
			} else {
				for _, succ := range bb.succs {
					if succ == nil {
						fmt.Println(bb.succs)
					}
					newliveout.Or(newliveout, succ.livein)
				}
			}

			if !bb.liveout.Eq(newliveout) {
				change = true
				bb.liveout.Copy(newliveout)
			}

			// A variable is live on input to this block
			// if it is live on output from this block and
			// not set by the code in this block.
			//
			// in[b] = uevar[b] \cup (out[b] \setminus varkill[b])
			newlivein.AndNot(bb.liveout, bb.varkill)

			bb.livein.Or(newlivein, bb.uevar)
		}
	}

	// Useful sanity check: on entry to the function,
	// the only things that can possibly be live are the
	// input parameters.
	b := lv.f.Entry
	bb := lv.bes[b.ID]
	for j := int32(0); j < bb.livein.n; j++ {
		if !bb.livein.Get(j) {
			continue
		}
		n := lv.vars[j]
		if n.Class != PPARAM {
			yyerrorl(b.Pos, "internal error: %v %L recorded as live on entry", Curfn.Func.Nname, n)
		}
	}
}

func (lv *Liveness) entryvarinit(b *ssa.Block, any, all bvec) {
	if b == lv.f.Entry {
		any.Clear()
		for _, pos := range lv.cache.textavarinit {
			any.Set(pos)
		}
		all.Copy(any)
		return
	}

	bb := lv.bes[b.ID]
	any.Copy(bb.preds[0].avarinitany)
	all.Copy(bb.preds[0].avarinitall)
	for _, pred := range bb.preds[1:] {
		any.Or(any, pred.avarinitany)
		all.And(all, pred.avarinitall)
	}
}

func (lv *Liveness) exitblockuses(b *ssa.Block) ([]int32, bool) {
	switch b.Kind {
	case ssa.BlockRet:
		return lv.cache.retuevar, true
	case ssa.BlockRetJmp:
		// A return instruction with a p.to is a tail return, which brings
		// the stack pointer back up (if it ever went down) and then jumps
		// to a new function entirely. That form of instruction must read
		// all the parameters for correctness, and similarly it must not
		// read the out arguments - they won't be set until the new
		// function runs.
		return lv.cache.tailuevar, true
	}

	return nil, false
}

// This function is slow but it is only used for generating debug prints.
// Check whether n is marked live in args/locals.
func islive(n *Node, args bvec, locals bvec) bool {
	switch n.Class {
	case PPARAM, PPARAMOUT:
		for i := 0; int64(i) < n.Type.Width/int64(Widthptr); i++ {
			if args.Get(int32(n.Xoffset/int64(Widthptr) + int64(i))) {
				return true
			}
		}

	case PAUTO:
		for i := 0; int64(i) < n.Type.Width/int64(Widthptr); i++ {
			if locals.Get(int32((n.Xoffset+stkptrsize)/int64(Widthptr) + int64(i))) {
				return true
			}
		}
	}

	return false
}

// Visits all instructions in a basic block and computes a bit vector of live
// variables at each safe point locations.
func livenessepilogue(lv *Liveness) {
	nvars := int32(len(lv.vars))
	liveout := bvalloc(nvars)
	any := bvalloc(nvars)
	all := bvalloc(nvars)
	livedefer := bvalloc(nvars)

	// If there is a defer (that could recover), then all output
	// parameters are live all the time.  In addition, any locals
	// that are pointers to heap-allocated output parameters are
	// also always live (post-deferreturn code needs these
	// pointers to copy values back to the stack).
	// TODO: if the output parameter is heap-allocated, then we
	// don't need to keep the stack copy live?
	if hasdefer {
		for i, n := range lv.vars {
			if n.Class == PPARAMOUT {
				if n.IsOutputParamHeapAddr() {
					// Just to be paranoid.
					Fatalf("variable %v both output param and heap output param", n)
				}
				// Needzero not necessary, as the compiler
				// explicitly zeroes output vars at start of fn.
				livedefer.Set(int32(i))
			}
			if n.IsOutputParamHeapAddr() {
				n.Name.Needzero = true
				livedefer.Set(int32(i))
			}
		}
	}

	for _, b := range lv.f.Blocks {
		bb := lv.bes[b.ID]

		// Compute avarinitany and avarinitall for entry to block.
		// This duplicates information known during livenesssolve
		// but avoids storing two more vectors for each block.
		lv.entryvarinit(b, any, all)

		if b == lv.f.Entry {
			// Allocate a bit vector for each class and facet of
			// value we are tracking.

			// Live stuff first.
			args := bvalloc(argswords())

			lv.argslivepointers = append(lv.argslivepointers, args)
			locals := bvalloc(localswords())
			lv.livepointers = append(lv.livepointers, locals)

			if debuglive >= 3 {
				printvars("avarinitany", any, lv.vars)
			}

			// Record any values with an "address taken" reaching
			// this code position as live. Must do now instead of below
			// because the any/all calculation requires walking forward
			// over the block (as this loop does), while the liveout
			// requires walking backward (as the next loop does).
			onebitlivepointermap(lv, any, lv.vars, args, locals)
		}

		// Walk forward through the basic block instructions and
		// allocate liveness maps for those instructions that need them.
		// Seed the maps with information about the addrtaken variables.
		for _, v := range b.Values {
			pos, effect := lv.progeffects(v)
			if effect&Varkill != 0 {
				any.Unset(pos)
				all.Unset(pos)
			}
			if effect&Avarinit != 0 {
				any.Set(pos)
				all.Set(pos)
			}

			if iscallop(v.Op) {
				// Annotate ambiguously live variables so that they can
				// be zeroed at function entry.
				// liveout is dead here and used as a temporary.
				liveout.AndNot(any, all)
				if !liveout.IsEmpty() {
					for pos := int32(0); pos < liveout.n; pos++ {
						if !liveout.Get(pos) {
							continue
						}
						all.Set(pos) // silence future warnings in this block
						n := lv.vars[pos]
						if !n.Name.Needzero {
							n.Name.Needzero = true
							if debuglive >= 1 {
								Warnl(v.Pos, "%v: %L is ambiguously live", Curfn.Func.Nname, n)
							}
						}
					}
				}

				// Allocate a bit vector for each class and facet of
				// value we are tracking.

				// Live stuff first.
				args := bvalloc(argswords())

				lv.argslivepointers = append(lv.argslivepointers, args)
				locals := bvalloc(localswords())
				lv.livepointers = append(lv.livepointers, locals)

				if debuglive >= 3 {
					fmt.Printf("%v\n", v)
					printvars("avarinitany", any, lv.vars)
				}

				// Record any values with an "address taken" reaching
				// this code position as live. Must do now instead of below
				// because the any/all calculation requires walking forward
				// over the block (as this loop does), while the liveout
				// requires walking backward (as the next loop does).
				onebitlivepointermap(lv, any, lv.vars, args, locals)
			}
		}

		bb.lastbitmapindex = len(lv.livepointers) - 1
	}

	for _, b := range lv.f.Blocks {
		bb := lv.bes[b.ID]

		// walk backward, emit pcdata and populate the maps
		pos := int32(bb.lastbitmapindex)
		if pos < 0 {
			// the first block we encounter should have the ATEXT so
			// at no point should pos ever be less than zero.
			Fatalf("livenessepilogue")
		}

		liveout.Copy(bb.liveout)
		for i := len(b.Values) - 1; i >= 0; i-- {
			v := b.Values[i]

			if iscallop(v.Op) {
				// Found an interesting instruction, record the
				// corresponding liveness information.

				// Record live pointers.
				args := lv.argslivepointers[pos]
				locals := lv.livepointers[pos]
				onebitlivepointermap(lv, liveout, lv.vars, args, locals)

				// Mark pparamout variables (as described above)
				onebitlivepointermap(lv, livedefer, lv.vars, args, locals)

				lv.callpos[v] = pos
				pos--
			}

			// Propagate liveness information
			npos, effect := lv.progeffects(v)
			if effect&Varkill != 0 {
				liveout.Unset(npos)
			}
			if effect&Uevar != 0 {
				liveout.Set(npos)
			}

			if debuglive >= 3 && iscallop(v.Op) {
				bv0 := bvalloc(int32(len(lv.vars)))

				var bv bvec
				if effect != 0 {
					bv = bvalloc(int32(len(lv.vars)))
					bv.Set(npos)
				}

				uevar, varkill := bv0, bv0
				if effect&Uevar != 0 {
					uevar = bv
				}
				if effect&Varkill != 0 {
					varkill = bv
				}

				fmt.Printf("%v\n", v)
				printvars("uevar", uevar, lv.vars)
				printvars("varkill", varkill, lv.vars)

				// variable is called liveout, but at
				// this point it's the liveout for the
				// *next* instruction; i.e., this
				// instruction's livein.
				printvars("livein", liveout, lv.vars)
			}
		}

		if b == lv.f.Entry {
			if pos != 0 {
				Fatalf("oops")
			}

			// Record live pointers.
			args := lv.argslivepointers[pos]
			locals := lv.livepointers[pos]
			onebitlivepointermap(lv, liveout, lv.vars, args, locals)
		}
	}

	flusherrors()
}

// FNV-1 hash function constants.
const (
	H0 = 2166136261
	Hp = 16777619
)

func hashbitmap(h uint32, bv bvec) uint32 {
	n := int((bv.n + 31) / 32)
	for i := 0; i < n; i++ {
		w := bv.b[i]
		h = (h * Hp) ^ (w & 0xff)
		h = (h * Hp) ^ ((w >> 8) & 0xff)
		h = (h * Hp) ^ ((w >> 16) & 0xff)
		h = (h * Hp) ^ ((w >> 24) & 0xff)
	}

	return h
}

// Compact liveness information by coalescing identical per-call-site bitmaps.
// The merging only happens for a single function, not across the entire binary.
//
// There are actually two lists of bitmaps, one list for the local variables and one
// list for the function arguments. Both lists are indexed by the same PCDATA
// index, so the corresponding pairs must be considered together when
// merging duplicates. The argument bitmaps change much less often during
// function execution than the local variable bitmaps, so it is possible that
// we could introduce a separate PCDATA index for arguments vs locals and
// then compact the set of argument bitmaps separately from the set of
// local variable bitmaps. As of 2014-04-02, doing this to the godoc binary
// is actually a net loss: we save about 50k of argument bitmaps but the new
// PCDATA tables cost about 100k. So for now we keep using a single index for
// both bitmap lists.
func livenesscompact(lv *Liveness) {
	// Linear probing hash table of bitmaps seen so far.
	// The hash table has 4n entries to keep the linear
	// scan short. An entry of -1 indicates an empty slot.
	n := len(lv.livepointers)

	tablesize := 4 * n
	table := make([]int, tablesize)
	for i := range table {
		table[i] = -1
	}

	// remap[i] = the new index of the old bit vector #i.
	remap := make([]int, n)

	for i := range remap {
		remap[i] = -1
	}
	uniq := 0 // unique tables found so far

	// Consider bit vectors in turn.
	// If new, assign next number using uniq,
	// record in remap, record in lv.livepointers and lv.argslivepointers
	// under the new index, and add entry to hash table.
	// If already seen, record earlier index in remap and free bitmaps.
	for i := 0; i < n; i++ {
		local := lv.livepointers[i]
		arg := lv.argslivepointers[i]
		h := hashbitmap(hashbitmap(H0, local), arg) % uint32(tablesize)

		for {
			j := table[h]
			if j < 0 {
				break
			}
			jlocal := lv.livepointers[j]
			jarg := lv.argslivepointers[j]
			if local.Eq(jlocal) && arg.Eq(jarg) {
				remap[i] = j
				goto Next
			}

			h++
			if h == uint32(tablesize) {
				h = 0
			}
		}

		table[h] = uniq
		remap[i] = uniq
		lv.livepointers[uniq] = local
		lv.argslivepointers[uniq] = arg
		uniq++
	Next:
	}

	// We've already reordered lv.livepointers[0:uniq]
	// and lv.argslivepointers[0:uniq] and freed the bitmaps
	// we don't need anymore. Clear the pointers later in the
	// array so that we can tell where the coalesced bitmaps stop
	// and so that we don't double-free when cleaning up.
	for j := uniq; j < n; j++ {
		lv.livepointers[j] = bvec{}
		lv.argslivepointers[j] = bvec{}
	}

	// Rewrite PCDATA instructions to use new numbering.
	var prev, prev2, prev3 *obj.Prog
	for p := lv.ptxt; p != nil; p, prev, prev2, prev3 = p.Link, p, prev, prev2 {
		if p.As != obj.ATEXT && p.As != obj.ACALL {
			continue
		}

		var pos int32
		if p.As == obj.ACALL {
			pos = lv.callpos[lv.valueProgs[p]]
		}
		pos = int32(remap[pos])

		if p.As == obj.ACALL {
			after := prev
			if isdeferreturn(p) {
				// runtime.deferreturn modifies its return address to return
				// back to the CALL, not to the subsequent instruction.
				// Because the return comes back one instruction early,
				// the PCDATA must begin one instruction early too.
				// The instruction before a call to deferreturn is always a
				// no-op, to keep PC-specific data unambiguous.
				if Ctxt.Arch.Family == sys.PPC64 {
					// On ppc64 there is an additional instruction
					// (another no-op or reload of toc pointer) before
					// the call.
					after = prev3
				} else {
					after = prev2
				}
			}
			if after == nil {
				fmt.Println("hmm", p, prev, prev2, prev3)
			}
			spliceafter(after, newpcdataprog(p, pos))
		}

		// Show live pointer bitmaps.
		// We're interpreting the args and locals bitmap instead of liveout so that we
		// include the bits added by the avarinit logic in the
		// previous loop.
		if debuglive >= 1 && Curfn.Func.Nname.Sym.Name != "init" && Curfn.Func.Nname.Sym.Name[0] != '.' {
			var buf bytes.Buffer

			fmt.Fprintf(&buf, "%v: live at ", p.Line())
			if p.As == obj.ACALL && p.To.Sym != nil {
				name := p.To.Sym.Name
				i := strings.Index(name, ".")
				if i >= 0 {
					name = name[i+1:]
				}
				fmt.Fprintf(&buf, "call to %s:", name)
			} else if p.As == obj.ACALL {
				buf.WriteString("indirect call:")
			} else {
				fmt.Fprintf(&buf, "entry to %s:", ((p.From.Node).(*Node)).Sym.Name)
			}
			args, locals := lv.argslivepointers[pos], lv.livepointers[pos]
			anylive := false
			for _, n := range lv.vars {
				if islive(n, args, locals) {
					fmt.Fprintf(&buf, " %v", n)
					anylive = true
				}
			}
			if anylive {
				fmt.Println(buf.String())
			}
		}
	}
}

func printbitset(printed bool, name string, vars []*Node, bits bvec) bool {
	started := false
	for i, n := range vars {
		if !bits.Get(int32(i)) {
			continue
		}
		if !started {
			if !printed {
				fmt.Printf("\t")
			} else {
				fmt.Printf(" ")
			}
			started = true
			printed = true
			fmt.Printf("%s=", name)
		} else {
			fmt.Printf(",")
		}

		fmt.Printf("%s", n.Sym.Name)
	}

	return printed
}

// Dumps a slice of bitmaps to a symbol as a sequence of uint32 values. The
// first word dumped is the total number of bitmaps. The second word is the
// length of the bitmaps. All bitmaps are assumed to be of equal length. The
// remaining bytes are the raw bitmaps.
func onebitwritesymbol(arr []bvec, sym *Sym) {
	off := 4                                  // number of bitmaps, to fill in later
	off = duint32(sym, off, uint32(arr[0].n)) // number of bits in each bitmap
	var i int
	for i = 0; i < len(arr); i++ {
		// bitmap words
		bv := arr[i]

		if bv.b == nil {
			break
		}
		off = dbvec(sym, off, bv)
	}

	duint32(sym, 0, uint32(i)) // number of bitmaps
	ls := Linksym(sym)
	ls.Name = fmt.Sprintf("gclocals·%x", md5.Sum(ls.P))
	ls.Set(obj.AttrDuplicateOK, true)
	sv := obj.SymVer{Name: ls.Name, Version: 0}
	ls2, ok := Ctxt.Hash[sv]
	if ok {
		sym.Lsym = ls2
	} else {
		Ctxt.Hash[sv] = ls
		ggloblsym(sym, int32(off), obj.RODATA)
	}
}

func printprog(p *obj.Prog) {
	for p != nil {
		fmt.Printf("%v\n", p)
		p = p.Link
	}
}

// Entry pointer for liveness analysis. Constructs a complete CFG, solves for
// the liveness of pointer variables in the function, and emits a runtime data
// structure read by the garbage collector.
func liveness(fn *Node, firstp *obj.Prog, f *ssa.Func, valueProgs map[*obj.Prog]*ssa.Value, blockProgs map[*obj.Prog]*ssa.Block, argssym *Sym, livesym *Sym) {
	// Change name to dump debugging information only for a specific function.
	debugdelta := 0

	if Curfn.Func.Nname.Sym.Name == "!" {
		debugdelta = 2
	}

	debuglive += debugdelta
	if debuglive >= 3 {
		fmt.Printf("liveness: %s\n", Curfn.Func.Nname.Sym.Name)
		printprog(firstp)
	}

	checkptxt(fn, firstp)

	// Construct the global liveness state.
	vars := getvariables(fn)
	lv := newliveness(fn, firstp, vars, f, valueProgs, blockProgs)

	// Run the dataflow framework.
	livenessprologue(lv)
	livenesssolve(lv)
	livenessepilogue(lv)
	livenesscompact(lv)

	// Emit the live pointer map data structures
	onebitwritesymbol(lv.livepointers, livesym)
	onebitwritesymbol(lv.argslivepointers, argssym)

	// Free everything.
	for _, ln := range fn.Func.Dcl {
		if ln != nil {
			ln.SetOpt(nil)
		}
	}

	debuglive -= debugdelta
}

func auxSymNode(v *ssa.Value) *Node {
	switch a := v.Aux.(type) {
	case *ssa.ExternSymbol:
		return nil
	case *ssa.ArgSymbol:
		return a.Node.(*Node)
	case *ssa.AutoSymbol:
		return a.Node.(*Node)
	case nil:
		return nil
	default:
		Fatalf("bad value: %s", v.LongString())
		return nil
	}
}

const (
	MemRead = 1 << iota
	MemWrite
)

func valueEffect(v *ssa.Value) (*Node, uint32) {
	if v == nil {
		return nil, 0
	}

	switch v.Op {
	case ssa.OpLoadReg:
		n, _ := AutoVar(v.Args[0])
		return n, MemRead
	case ssa.OpStoreReg:
		n, _ := AutoVar(v)
		return n, MemWrite

	case ssa.OpVarLive:
		return v.Aux.(*Node), MemRead
	case ssa.OpVarDef, ssa.OpVarKill:
		return v.Aux.(*Node), MemWrite
	case ssa.OpKeepAlive:
		n, _ := AutoVar(v.Args[0])
		return n, MemRead

		// 386
	case ssa.Op386LEAL,
		ssa.Op386LEAL1,
		ssa.Op386LEAL2,
		ssa.Op386LEAL4,
		ssa.Op386LEAL8,
		ssa.Op386LoweredNilCheck,
		ssa.Op386MOVBload,
		ssa.Op386MOVBloadidx1,
		ssa.Op386MOVBLSXload,
		ssa.Op386MOVLload,
		ssa.Op386MOVLloadidx1,
		ssa.Op386MOVLloadidx4,
		ssa.Op386MOVSDload,
		ssa.Op386MOVSDloadidx1,
		ssa.Op386MOVSDloadidx8,
		ssa.Op386MOVSSload,
		ssa.Op386MOVSSloadidx1,
		ssa.Op386MOVSSloadidx4,
		ssa.Op386MOVWload,
		ssa.Op386MOVWloadidx1,
		ssa.Op386MOVWloadidx2,
		ssa.Op386MOVWLSXload:
		return auxSymNode(v), MemRead
	case ssa.Op386MOVLstoreconstidx1,
		ssa.Op386MOVLstoreconstidx4,
		ssa.Op386MOVWstoreconstidx1,
		ssa.Op386MOVWstoreconstidx2,
		ssa.Op386MOVBstoreconstidx1,
		ssa.Op386MOVLstoreconst,
		ssa.Op386MOVWstoreconst,
		ssa.Op386MOVBstoreconst,
		ssa.Op386MOVBstoreidx1,
		ssa.Op386MOVWstoreidx1,
		ssa.Op386MOVLstoreidx1,
		ssa.Op386MOVSSstoreidx1,
		ssa.Op386MOVSDstoreidx1,
		ssa.Op386MOVWstoreidx2,
		ssa.Op386MOVSSstoreidx4,
		ssa.Op386MOVLstoreidx4,
		ssa.Op386MOVSDstoreidx8,
		ssa.Op386MOVSSstore,
		ssa.Op386MOVSDstore,
		ssa.Op386MOVLstore,
		ssa.Op386MOVWstore,
		ssa.Op386MOVBstore:
		return auxSymNode(v), MemWrite

		// amd64
	case ssa.OpAMD64ADDLmem,
		ssa.OpAMD64ADDQmem,
		ssa.OpAMD64LEAL,
		ssa.OpAMD64LEAQ,
		ssa.OpAMD64LEAQ1,
		ssa.OpAMD64LEAQ2,
		ssa.OpAMD64LEAQ4,
		ssa.OpAMD64LEAQ8,
		ssa.OpAMD64LoweredNilCheck,
		ssa.OpAMD64MOVBload,
		ssa.OpAMD64MOVBloadidx1,
		ssa.OpAMD64MOVBQSXload,
		ssa.OpAMD64MOVLatomicload,
		ssa.OpAMD64MOVLload,
		ssa.OpAMD64MOVLloadidx1,
		ssa.OpAMD64MOVLloadidx4,
		ssa.OpAMD64MOVLQSXload,
		ssa.OpAMD64MOVOload,
		ssa.OpAMD64MOVQatomicload,
		ssa.OpAMD64MOVQload,
		ssa.OpAMD64MOVQloadidx1,
		ssa.OpAMD64MOVQloadidx8,
		ssa.OpAMD64MOVSDload,
		ssa.OpAMD64MOVSDloadidx1,
		ssa.OpAMD64MOVSDloadidx8,
		ssa.OpAMD64MOVSSload,
		ssa.OpAMD64MOVSSloadidx1,
		ssa.OpAMD64MOVSSloadidx4,
		ssa.OpAMD64MOVWload,
		ssa.OpAMD64MOVWloadidx1,
		ssa.OpAMD64MOVWloadidx2,
		ssa.OpAMD64MOVWQSXload,
		ssa.OpAMD64SUBLmem,
		ssa.OpAMD64SUBQmem,
		ssa.OpAMD64ANDQmem,
		ssa.OpAMD64ANDLmem,
		ssa.OpAMD64ORQmem,
		ssa.OpAMD64ORLmem,
		ssa.OpAMD64XORQmem,
		ssa.OpAMD64XORLmem,
		ssa.OpAMD64ADDSDmem,
		ssa.OpAMD64ADDSSmem,
		ssa.OpAMD64SUBSDmem,
		ssa.OpAMD64SUBSSmem,
		ssa.OpAMD64MULSDmem,
		ssa.OpAMD64MULSSmem:
		return auxSymNode(v), MemRead
	case ssa.OpAMD64MOVBstore,
		ssa.OpAMD64MOVBstoreconst,
		ssa.OpAMD64MOVBstoreconstidx1,
		ssa.OpAMD64MOVBstoreidx1,
		ssa.OpAMD64MOVLstore,
		ssa.OpAMD64MOVLstoreconst,
		ssa.OpAMD64MOVLstoreconstidx1,
		ssa.OpAMD64MOVLstoreconstidx4,
		ssa.OpAMD64MOVLstoreidx1,
		ssa.OpAMD64MOVLstoreidx4,
		ssa.OpAMD64MOVOstore,
		ssa.OpAMD64MOVQstore,
		ssa.OpAMD64MOVQstoreconst,
		ssa.OpAMD64MOVQstoreconstidx1,
		ssa.OpAMD64MOVQstoreconstidx8,
		ssa.OpAMD64MOVQstoreidx1,
		ssa.OpAMD64MOVQstoreidx8,
		ssa.OpAMD64MOVSDstore,
		ssa.OpAMD64MOVSDstoreidx1,
		ssa.OpAMD64MOVSDstoreidx8,
		ssa.OpAMD64MOVSSstore,
		ssa.OpAMD64MOVSSstoreidx1,
		ssa.OpAMD64MOVSSstoreidx4,
		ssa.OpAMD64MOVWstore,
		ssa.OpAMD64MOVWstoreconst,
		ssa.OpAMD64MOVWstoreconstidx1,
		ssa.OpAMD64MOVWstoreconstidx2,
		ssa.OpAMD64MOVWstoreidx1,
		ssa.OpAMD64MOVWstoreidx2:
		return auxSymNode(v), MemWrite
	case ssa.OpAMD64ANDBlock,
		ssa.OpAMD64CMPXCHGLlock,
		ssa.OpAMD64CMPXCHGQlock,
		ssa.OpAMD64ORBlock,
		ssa.OpAMD64XADDLlock,
		ssa.OpAMD64XADDQlock,
		ssa.OpAMD64XCHGL,
		ssa.OpAMD64XCHGQ:
		return auxSymNode(v), MemRead | MemWrite

		// arm64
	case ssa.OpARM64LDAR,
		ssa.OpARM64LDARW,
		ssa.OpARM64LoweredNilCheck,
		ssa.OpARM64FMOVDload,
		ssa.OpARM64FMOVSload,
		ssa.OpARM64MOVBload,
		ssa.OpARM64MOVBUload,
		ssa.OpARM64MOVDaddr,
		ssa.OpARM64MOVDload,
		ssa.OpARM64MOVHload,
		ssa.OpARM64MOVHUload,
		ssa.OpARM64MOVWload,
		ssa.OpARM64MOVWUload:
		return auxSymNode(v), MemRead

	case ssa.OpARM64MOVDstorezero,
		ssa.OpARM64MOVWstorezero,
		ssa.OpARM64MOVHstorezero,
		ssa.OpARM64MOVBstorezero,
		ssa.OpARM64FMOVDstore,
		ssa.OpARM64FMOVSstore,
		ssa.OpARM64MOVDstore,
		ssa.OpARM64MOVWstore,
		ssa.OpARM64MOVHstore,
		ssa.OpARM64MOVBstore,
		ssa.OpARM64STLRW,
		ssa.OpARM64STLR:
		return auxSymNode(v), MemWrite

		// arm
	case ssa.OpARMLoweredNilCheck,
		ssa.OpARMMOVBload,
		ssa.OpARMMOVBUload,
		ssa.OpARMMOVDload,
		ssa.OpARMMOVFload,
		ssa.OpARMMOVHload,
		ssa.OpARMMOVHUload,
		ssa.OpARMMOVWaddr,
		ssa.OpARMMOVWload:
		return auxSymNode(v), MemRead

	case ssa.OpARMMOVDstore,
		ssa.OpARMMOVFstore,
		ssa.OpARMMOVWstore,
		ssa.OpARMMOVHstore,
		ssa.OpARMMOVBstore:
		return auxSymNode(v), MemWrite

		// mips64
	case ssa.OpMIPS64LoweredNilCheck,
		ssa.OpMIPS64MOVBload,
		ssa.OpMIPS64MOVBUload,
		ssa.OpMIPS64MOVDload,
		ssa.OpMIPS64MOVFload,
		ssa.OpMIPS64MOVHload,
		ssa.OpMIPS64MOVHUload,
		ssa.OpMIPS64MOVVaddr,
		ssa.OpMIPS64MOVVload,
		ssa.OpMIPS64MOVWload,
		ssa.OpMIPS64MOVWUload:
		return auxSymNode(v), MemRead

	case ssa.OpMIPS64MOVVstorezero,
		ssa.OpMIPS64MOVWstorezero,
		ssa.OpMIPS64MOVHstorezero,
		ssa.OpMIPS64MOVBstorezero,
		ssa.OpMIPS64MOVDstore,
		ssa.OpMIPS64MOVFstore,
		ssa.OpMIPS64MOVVstore,
		ssa.OpMIPS64MOVWstore,
		ssa.OpMIPS64MOVHstore,
		ssa.OpMIPS64MOVBstore:
		return auxSymNode(v), MemWrite

		// mips
	case ssa.OpMIPSLoweredNilCheck,
		ssa.OpMIPSMOVBload,
		ssa.OpMIPSMOVBUload,
		ssa.OpMIPSMOVDload,
		ssa.OpMIPSMOVFload,
		ssa.OpMIPSMOVHload,
		ssa.OpMIPSMOVHUload,
		ssa.OpMIPSMOVWaddr,
		ssa.OpMIPSMOVWload:
		return auxSymNode(v), MemRead

	case ssa.OpMIPSMOVWstorezero,
		ssa.OpMIPSMOVHstorezero,
		ssa.OpMIPSMOVBstorezero,
		ssa.OpMIPSMOVDstore,
		ssa.OpMIPSMOVFstore,
		ssa.OpMIPSMOVWstore,
		ssa.OpMIPSMOVHstore,
		ssa.OpMIPSMOVBstore:
		return auxSymNode(v), MemWrite

		// ppc64
	case ssa.OpPPC64FMOVDload,
		ssa.OpPPC64FMOVSload,
		ssa.OpPPC64LoweredNilCheck,
		ssa.OpPPC64MOVBZload,
		ssa.OpPPC64MOVDaddr,
		ssa.OpPPC64MOVDload,
		ssa.OpPPC64MOVHload,
		ssa.OpPPC64MOVHZload,
		ssa.OpPPC64MOVWload,
		ssa.OpPPC64MOVWZload:
		return auxSymNode(v), MemRead

	case ssa.OpPPC64FMOVDstore,
		ssa.OpPPC64FMOVSstore,
		ssa.OpPPC64MOVDstore,
		ssa.OpPPC64MOVWstore,
		ssa.OpPPC64MOVHstore,
		ssa.OpPPC64MOVBstore,
		ssa.OpPPC64MOVDstorezero,
		ssa.OpPPC64MOVWstorezero,
		ssa.OpPPC64MOVHstorezero,
		ssa.OpPPC64MOVBstorezero:
		return auxSymNode(v), MemWrite

		// s390x
	case ssa.OpS390XADDload,
		ssa.OpS390XADDWload,
		ssa.OpS390XANDload,
		ssa.OpS390XANDWload,
		ssa.OpS390XFMOVDload,
		ssa.OpS390XFMOVDloadidx,
		ssa.OpS390XFMOVSload,
		ssa.OpS390XFMOVSloadidx,
		ssa.OpS390XLoweredNilCheck,
		ssa.OpS390XMOVBload,
		ssa.OpS390XMOVBZload,
		ssa.OpS390XMOVBZloadidx,
		ssa.OpS390XMOVDaddr,
		ssa.OpS390XMOVDaddridx,
		ssa.OpS390XMOVDatomicload,
		ssa.OpS390XMOVDBRload,
		ssa.OpS390XMOVDBRloadidx,
		ssa.OpS390XMOVDload,
		ssa.OpS390XMOVDloadidx,
		ssa.OpS390XMOVHBRload,
		ssa.OpS390XMOVHBRloadidx,
		ssa.OpS390XMOVHload,
		ssa.OpS390XMOVHZload,
		ssa.OpS390XMOVHZloadidx,
		ssa.OpS390XMOVWBRload,
		ssa.OpS390XMOVWBRloadidx,
		ssa.OpS390XMOVWload,
		ssa.OpS390XMOVWZatomicload,
		ssa.OpS390XMOVWZload,
		ssa.OpS390XMOVWZloadidx,
		ssa.OpS390XMULLDload,
		ssa.OpS390XMULLWload,
		ssa.OpS390XORload,
		ssa.OpS390XORWload,
		ssa.OpS390XSUBload,
		ssa.OpS390XSUBWload,
		ssa.OpS390XXORload,
		ssa.OpS390XXORWload:
		return auxSymNode(v), MemRead

	case ssa.OpS390XLoweredAtomicExchange32,
		ssa.OpS390XLoweredAtomicExchange64:
		return auxSymNode(v), MemRead | MemWrite

	case ssa.OpS390XLoweredAtomicCas32,
		ssa.OpS390XLoweredAtomicCas64,
		ssa.OpS390XLAA,
		ssa.OpS390XLAAG,
		ssa.OpS390XMOVWatomicstore,
		ssa.OpS390XMOVDatomicstore,
		ssa.OpS390XSTM2,
		ssa.OpS390XSTM3,
		ssa.OpS390XSTM4,
		ssa.OpS390XSTMG2,
		ssa.OpS390XSTMG3,
		ssa.OpS390XSTMG4,
		ssa.OpS390XCLEAR,
		ssa.OpS390XMOVDstoreconst,
		ssa.OpS390XMOVWstoreconst,
		ssa.OpS390XMOVHstoreconst,
		ssa.OpS390XMOVBstoreconst,
		ssa.OpS390XFMOVSstoreidx,
		ssa.OpS390XFMOVDstoreidx,
		ssa.OpS390XMOVHBRstoreidx,
		ssa.OpS390XMOVWBRstoreidx,
		ssa.OpS390XMOVDBRstoreidx,
		ssa.OpS390XMOVBstoreidx,
		ssa.OpS390XMOVHstoreidx,
		ssa.OpS390XMOVWstoreidx,
		ssa.OpS390XMOVDstoreidx,
		ssa.OpS390XFMOVSstore,
		ssa.OpS390XFMOVDstore,
		ssa.OpS390XMOVHBRstore,
		ssa.OpS390XMOVWBRstore,
		ssa.OpS390XMOVDBRstore,
		ssa.OpS390XMOVBstore,
		ssa.OpS390XMOVHstore,
		ssa.OpS390XMOVWstore,
		ssa.OpS390XMOVDstore:
		return auxSymNode(v), MemWrite
	}

	return nil, 0
}

func iscallop(op ssa.Op) bool {
	switch op {
	case ssa.OpAMD64CALLstatic,
		ssa.OpAMD64CALLclosure,
		ssa.OpAMD64CALLdefer,
		ssa.OpAMD64CALLgo,
		ssa.OpAMD64CALLinter:
		return true
	}

	return false
}
