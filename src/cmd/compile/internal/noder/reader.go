// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package noder

import (
	"fmt"
	"go/constant"
	"io"
	"strings"

	"cmd/compile/internal/base"
	"cmd/compile/internal/deadcode"
	"cmd/compile/internal/dwarfgen"
	"cmd/compile/internal/inline"
	"cmd/compile/internal/ir"
	"cmd/compile/internal/typecheck"
	"cmd/compile/internal/types"
	"cmd/internal/obj"
	"cmd/internal/src"
)

// TODO: Next steps in cleaning things up.
//
// - Densely number labels within each function body.
//
// - More eagerly call typecheck.Stmt as we go.
//
// - Prune localNames list when scopes close.
//
// - Change API to return an *ir.Package instead of filling an
// existing one.

// TODO(mdempsky): Key bodyIndex on the *ir.Name instead, so we don't
// need to create an ir.Func for imported functions?
var bodyIndex = map[*ir.Func]readerBody{}

type pkgReaderIndex struct {
	pr  *pkgReader
	idx int
}

var pkgBits = map[*types.Pkg]pkgReaderIndex{}

var objBits = map[*types.Sym]pkgReaderIndex{}

var todoBodies = map[*ir.Func]bool{}

var importData = map[string]*pkgReader{}

func readPkgBits(pr0 pkgDecoder, self *types.Pkg, target *ir.Package) {

	typecheck.TypecheckAllowed = true

	pr := newPkgReader(pr0, self)

	r := pr.newReader(relocMeta, privateRootIdx)
	r.curpkg = self
	r.top = true
	r.pack(target)
}

func newPkgReader(pr0 pkgDecoder, self *types.Pkg) *pkgReader {
	pr := pkgReader{
		pkgDecoder: pr0,
	}

	pr.curpkg = self

	pr.posBases = make([]*src.PosBase, pr.numElems(relocPosBase))
	pr.pkgs = make([]*types.Pkg, pr.numElems(relocPkg))
	pr.typs = make([]*types.Type, pr.numElems(relocType))
	pr.objs = make([]*ir.Name, pr.numElems(relocObj))

	// For linker.
	pr.newindex = make([]int, len(pr.elemEnds))
	importData[self.Path] = &pr

	return &pr
}

type readerData interface {
	io.ByteReader
	io.Reader
}

func (pr *pkgReader) newReader(k reloc, idx int) *reader {
	return &reader{
		decoder: pr.newDecoder(k, idx),
		p:       pr,
	}
}

func (r *reader) pack(target *ir.Package) {
	r.curpkg.Name = r.string()
	r.curpkg.Height = r.len()

	for _, path := range r.strings() {
		ipkg := types.NewPkg(path, "")
		assert(ipkg.Direct) // already loaded by importer
		target.Imports = append(target.Imports, ipkg)
	}

	cgoPragmas := make([][]string, r.len())
	for i := range cgoPragmas {
		cgoPragmas[i] = r.strings()
	}
	target.CgoPragmas = cgoPragmas

	if quirksMode() {
		for i, n := 0, r.len(); i < n; i++ {
			// Eagerly register position bases, so their filenames are
			// assigned stable indices.
			posBase := r.posBase()
			_ = base.Ctxt.PosTable.XPos(src.MakePos(posBase, 0, 0))
		}

		for i, n := 0, r.len(); i < n; i++ {
			// Eagerly resolve imported objects, so any filenames registered
			// in the process are assigned stable indices too.
			sym := r.sym()
			typecheck.Resolve(ir.NewIdent(src.NoXPos, sym))
			assert(sym.Def != nil)
		}
	}

	var decls ir.Nodes
	r.decls(&decls)
	assert(target.Decls == nil)
	target.Decls = decls

	for i, n := 0, r.len(); i < n; i++ {
		name := r.doObj(nil, true).(*ir.Name)
		sym := name.Sym()
		assert(!sym.IsBlank())

		if name.Class == ir.PEXTERN {
			target.Externs = append(target.Externs, name)
		}

		// TODO(mdempsky): Cleaner way to recognize init?
		if name.Class == ir.PFUNC && name.Type().Recv() == nil && strings.HasPrefix(sym.Name, "init.") {
			target.Inits = append(target.Inits, name.Func)
		}

		if types.IsExported(sym.Name) {
			assert(!sym.OnExportList())
			target.Exports = append(target.Exports, name)
			sym.SetOnExportList(true)
		}

		if base.Flag.AsmHdr != "" {
			assert(!sym.Asm())
			target.Asms = append(target.Asms, name)
			sym.SetAsm(true)
		}
	}

	embeds := make([]*ir.Name, r.len())
	for i := range embeds {
		name := r.doObj(nil, true).(*ir.Name)
		embeds[i] = name

		pragmas := make([]ir.Embed, r.len())
		for j := range pragmas {
			pos := r.pos()
			patterns := r.strings()
			pragmas[j] = ir.Embed{Pos: pos, Patterns: patterns}
		}
		name.Embed = &pragmas
	}
	target.Embeds = embeds

	r.sync(syncEOF)

	// For now, we need to enforce that target is the typecheck
	// target, because typecheck.Stmt will append closures there. But
	// eventually, we should handle those details ourself.
	// TODO(mdempsky): Remove assertion.
	assert(target == typecheck.Target)

	// Don't use range--typecheck can add closures to Target.Decls.
	for i := 0; i < len(target.Decls); i++ {
		target.Decls[i] = typecheck.Stmt(target.Decls[i])
	}

	flushBodies(true)

	// Don't use range--typecheck can add closures to Target.Decls.
	for i := 0; i < len(target.Decls); i++ {
		if fn, ok := target.Decls[i].(*ir.Func); ok {
			if base.Flag.W > 1 {
				s := fmt.Sprintf("\nbefore typecheck %v", fn)
				ir.Dump(s, fn)
			}
			ir.CurFunc = fn
			typecheck.Stmts(fn.Body)
			if base.Flag.W > 1 {
				s := fmt.Sprintf("\nafter typecheck %v", fn)
				ir.Dump(s, fn)
			}

		}
	}

	assert(len(todoBodies) == 0)

	base.ExitIfErrors() // just in case
}

type pkgReader struct {
	pkgDecoder

	curpkg *types.Pkg

	posBases []*src.PosBase
	pkgs     []*types.Pkg
	typs     []*types.Type
	objs     []*ir.Name // TODO: only used for inits currently

	// offset for rewriting the given index into the output,
	// but +1e6 so we can detect if we're missing the entry or not.
	newindex []int
}

type readerBody struct {
	pr    *pkgReader
	idx   int
	targs []*types.Type
}

type reader struct {
	decoder

	p *pkgReader

	bside *reader

	top bool

	curpkg *types.Pkg
	targs  []*types.Type

	curfn  *ir.Func
	locals []*ir.Name

	funarghack bool

	// scopeVars is a stack tracking the number of variables declared in
	// the current function at the moment each open scope was opened.
	scopeVars         []int
	marker            dwarfgen.ScopeMarker
	lastCloseScopePos src.XPos

	// === details for handling inline body expansion ===

	// If we're reading in a function body because of inlining, this is
	// the call that we're inlining for.
	inlCaller    *ir.Func
	inlCall      *ir.CallExpr
	inlFunc      *ir.Func
	inlTreeIndex int
	inlPosBases  map[*src.PosBase]*src.PosBase

	delayResults bool

	// Label to return to.
	retlabel *types.Sym

	inlvars, retvars ir.Nodes
}

func (r *reader) setType(n ir.Node, typ *types.Type) {
	n.SetType(typ)
	n.SetTypecheck(1)

	if name, ok := n.(*ir.Name); ok {
		name.SetWalkdef(1)
		name.Ntype = ir.TypeNode(name.Type())
	}
}

func (r *reader) setValue(name *ir.Name, val constant.Value) {
	name.SetVal(val)
	name.Defn = nil
}

func (r *reader) pos() src.XPos {
	return base.Ctxt.PosTable.XPos(r.pos0())
}

func (r *reader) pos0() src.Pos {
	r.sync(syncPos)
	if !r.bool() {
		return src.NoPos
	}

	posBase := r.posBase()
	line := r.uint()
	col := r.uint()
	return src.MakePos(posBase, line, col)
}

func (r *reader) posBase() *src.PosBase {
	return r.updatePosBase(r.p.posBaseIdx(r.reloc(relocPosBase)))
}

func (r *reader) updatePosBase(oldBase *src.PosBase) *src.PosBase {
	if r.inlCall == nil {
		return oldBase
	}

	if newBase, ok := r.inlPosBases[oldBase]; ok {
		return newBase
	}

	newBase := src.NewInliningBase(oldBase, r.inlTreeIndex)
	r.inlPosBases[oldBase] = newBase
	return newBase
}

func (r *reader) updatePos(xpos src.XPos) src.XPos {
	pos := base.Ctxt.PosTable.Pos(xpos)
	pos.SetBase(r.updatePosBase(pos.Base()))
	return base.Ctxt.PosTable.XPos(pos)
}

func (pr *pkgReader) posBaseIdx(idx int) *src.PosBase {
	if b := pr.posBases[idx]; b != nil {
		return b
	}

	r := pr.newReader(relocPosBase, idx)

	fn := r.string()
	absfn := fileh(fn)

	var b *src.PosBase

	if r.bool() {
		b = src.NewFileBase(fn, absfn)
	} else {
		pos := r.pos0()
		line := r.uint()
		col := r.uint()
		b = src.NewLinePragmaBase(pos, fn, absfn, line, col)
	}

	pr.posBases[idx] = b
	return b
}

func (r *reader) pragmaFlag() ir.PragmaFlag {
	r.sync(syncPragma)
	return ir.PragmaFlag(r.int())
}

func (r *reader) decls(out *ir.Nodes) {
	assert(r.curfn == nil)

	r.sync(syncDecls)
	for {
		switch tag := r.int(); tag {
		default:
			panic(fmt.Sprintf("unhandled decl: %v", tag))

		case 0:
			return

		case 1:
			r.declName(ir.PEXTERN)

		case 2:
			pos := r.pos()
			names := r.declNames(ir.PEXTERN)
			values := r.exprList()

			if len(names) > 1 && len(values) == 1 {
				as := ir.NewAssignListStmt(pos, ir.OAS2, nil, values)
				for _, name := range names {
					as.Lhs.Append(name)
					name.Defn = as
				}
				out.Append(as)
				continue
			}

			for i, name := range names {
				as := ir.NewAssignStmt(pos, name, nil)
				if i < len(values) {
					as.Y = values[i]
				}
				name.Defn = as
				out.Append(as)
			}

		case 5:
			name := r.declName(ir.PFUNC)
			out.Append(r.expandFunc(name))

		case 6:
			typ := r.typ()
			sym := r.selector()

			method := typecheck.Lookdot1(nil, sym, typ, typ.Methods(), 0)
			out.Append(r.expandFunc(method.Nname.(*ir.Name)))

		case 7: // blank methods
			method := r.method()
			out.Append(r.expandFunc(method.Nname.(*ir.Name)))
		}
	}
}

func (r *reader) expandFunc(name *ir.Name) *ir.Func {
	fn := name.Func
	assert(fn != nil)

	assert(todoBodies[fn])
	delete(todoBodies, fn)

	b, ok := bodyIndex[fn]
	assert(ok)
	b.pr.bodyIdx(fn, b.idx, nil)

	return fn
}

func flushBodies(check bool) {
	for len(todoBodies) != 0 {
		for fn := range todoBodies {
			delete(todoBodies, fn)

			b, ok := bodyIndex[fn]
			assert(ok)
			b.pr.bodyIdx(fn, b.idx, b.targs)

			// May need to flush instantiated generic bodies.
			if fn.OClosure == nil && len(b.targs) != 0 {
				typecheck.Target.Decls = append(typecheck.Target.Decls, fn)
				typecheck.Func(fn)
				outerfn := ir.CurFunc
				ir.CurFunc = fn
				typecheck.Stmts(fn.Body)
				ir.CurFunc = outerfn
			}
		}
	}
}

func (r *reader) declNames(ctxt ir.Class) []*ir.Name {
	r.sync(syncDeclNames)
	nodes := make([]*ir.Name, r.len())
	for i := range nodes {
		nodes[i] = r.declName(ctxt)
	}
	return nodes
}

func (r *reader) useLocal() *ir.Name {
	r.sync(syncUseObjLocal)
	return r.locals[r.len()]
}

func (r *reader) useObj() ir.Node {
	r.sync(syncUseObj)

	targs := make([]*types.Type, r.len())
	for i := range targs {
		targs[i] = r.typ()
	}

	return r.doObj(targs, true)
}

func (r *reader) value() (*types.Type, constant.Value) {
	r.sync(syncValue)
	typ := r.typ()

	val := r.rawValue()

	return typ, FixValue(typ, val)
}

func (r *reader) exprList() []ir.Node {
	r.sync(syncExprList)
	return r.exprs()
}

func (r *reader) exprs() []ir.Node {
	r.sync(syncExprs)
	nodes := make([]ir.Node, r.len())
	if len(nodes) == 0 {
		return nil // TODO(mdempsky): Unclear if this matters.
	}
	for i := range nodes {
		nodes[i] = r.expr()
	}
	return nodes
}

func (r *reader) pkg() *types.Pkg {
	r.sync(syncPkg)
	return r.p.pkgIdx(r.reloc(relocPkg))
}

func (pr *pkgReader) pkgIdx(idx int) *types.Pkg {
	if pkg := pr.pkgs[idx]; pkg != nil {
		return pkg
	}

	var pkg *types.Pkg

	{
		r := pr.newReader(relocPkg, idx)
		r.sync(syncPkgDef)
		if path := r.string(); path == "builtin" {
			pkg = types.BuiltinPkg
		} else {
			if path == "" {
				pkg = pr.curpkg
			} else {
				pkg = types.NewPkg(path, "")
			}
			name := r.string()
			height := r.len()
			if pkg.Name != "" && pkg.Name != name {
				base.Fatalf("import %q: name %v != %v", path, pkg.Name, name)
			}
			if pkg.Height != 0 && pkg.Height != height {
				base.Fatalf("import %q: height %v != %v", path, pkg.Height, height)
			}
			pkg.Name = name
			pkg.Height = height
		}
	}

	pr.pkgs[idx] = pkg
	return pkg
}

func (r *reader) sym() *types.Sym {
	r.sync(syncSym)
	name := r.string()
	if name == "" {
		return nil
	}
	pkg := r.pkg()
	return pkg.Lookup(name)
}

func (r *reader) selector() *types.Sym {
	r.sync(syncSelector)
	name := r.string()
	pkg := types.LocalPkg
	if !types.IsExported(name) {
		pkg = r.pkg()
	}
	return pkg.Lookup(name)
}

func (r *reader) expr() (result ir.Node) {
	switch tag := codeExpr(r.code(syncExpr)); tag {
	default:
		panic("unhandled expression")

	case exprNone:
		return nil

	case exprBlank:
		return ir.BlankNode

	case exprLocal:
		return r.useLocal()

	case exprName:
		return r.useObj()

	case exprType:
		//		pos := r.pos()
		typ := r.typ()
		//		return ir.TypeNodeAt(pos, typ)
		return ir.TypeNode(typ)

	case exprConst:
		pos := r.pos()
		typ, val := r.value()
		op := r.op()
		orig := r.string()
		return OrigConst(pos, typ, val, op, orig)

	case exprCompLit:
		return r.compLit()

	case exprFuncLit:
		return r.funcLit()

	case exprSelector:
		x := r.expr()
		pos := r.pos()
		sym := r.selector()
		return ir.NewSelectorExpr(pos, ir.OXDOT, x, sym)

	case exprIndex:
		x := r.expr()
		pos := r.pos()
		index := r.expr()
		return ir.NewIndexExpr(pos, x, index)

	case exprSlice:
		x := r.expr()
		pos := r.pos()
		var index [3]ir.Node
		for i := range index {
			index[i] = r.expr()
		}
		op := ir.OSLICE
		if index[2] != nil {
			op = ir.OSLICE3
		}
		return ir.NewSliceExpr(pos, op, x, index[0], index[1], index[2])

	case exprAssert:
		x := r.expr()
		pos := r.pos()
		typ := r.expr().(ir.Ntype)
		return ir.NewTypeAssertExpr(pos, x, typ)

	case exprUnaryOp:
		op := r.op()
		pos := r.pos()
		x := r.expr()

		switch op {
		case ir.OADDR:
			return typecheck.NodAddrAt(pos, x)
		case ir.ODEREF:
			return ir.NewStarExpr(pos, x)
		}
		return ir.NewUnaryExpr(pos, op, x)

	case exprBinaryOp:
		op := r.op()
		x := r.expr()
		pos := r.pos()
		y := r.expr()

		switch op {
		case ir.OANDAND, ir.OOROR:
			return ir.NewLogicalExpr(pos, op, x, y)
		}
		return ir.NewBinaryExpr(pos, op, x, y)

	case exprCall:
		fun := r.expr()
		pos := r.pos()
		args := r.exprs()
		dots := r.bool()
		n := ir.NewCallExpr(pos, ir.OCALL, fun, args)
		n.IsDDD = dots
		return n

	case exprTypeSwitchGuard:
		pos := r.pos()
		var tag *ir.Ident
		if r.bool() {
			pos := r.pos()
			sym := typecheck.Lookup(r.string())
			tag = ir.NewIdent(pos, sym)
		}
		x := r.expr()
		return ir.NewTypeSwitchGuard(pos, tag, x)
	}
}

func (r *reader) stmt() ir.Node {
	switch stmts := r.stmts(); len(stmts) {
	case 0:
		return nil
	case 1:
		return stmts[0]
	default:
		return ir.NewBlockStmt(stmts[0].Pos(), stmts)
	}
}

func (r *reader) stmts() []ir.Node {
	var res ir.Nodes

	r.sync(syncStmts)
	for {
		tag := codeStmt(r.code(syncStmt1))
		if tag == stmtEnd {
			r.sync(syncStmtsEnd)
			return res
		}

		if n := r.stmt1(tag, &res); n != nil {
			res.Append(n)
		}
	}
}

func (r *reader) stmt1(tag codeStmt, out *ir.Nodes) ir.Node {
	switch tag {
	default:
		panic("unhandled statement")

	case stmtLabel:
		pos := r.pos()
		sym := r.label()
		return ir.NewLabelStmt(pos, sym)

	case stmtBlock:
		out.Append(r.blockStmt()...)
		return nil

	case stmtExpr:
		return r.expr()

	case stmtSend:
		pos := r.pos()
		ch := r.expr()
		value := r.expr()
		return ir.NewSendStmt(pos, ch, value)

	case stmtAssign:
		pos := r.pos()
		names, lhs := r.assignList()
		rhs := r.exprList()

		if len(rhs) == 0 {
			for _, name := range names {
				as := ir.NewAssignStmt(pos, name, nil)
				as.PtrInit().Append(ir.NewDecl(pos, ir.ODCL, name))
				out.Append(as)
			}
			return nil
		}

		if len(lhs) == 1 && len(rhs) == 1 {
			n := ir.NewAssignStmt(pos, lhs[0], rhs[0])
			n.Def = r.initDefn(n, names)
			return n
		}

		n := ir.NewAssignListStmt(pos, ir.OAS2, lhs, rhs)
		n.Def = r.initDefn(n, names)
		return n

	case stmtAssignOp:
		op := r.op()
		lhs := r.expr()
		pos := r.pos()
		rhs := r.expr()
		return ir.NewAssignOpStmt(pos, op, lhs, rhs)

	case stmtIncDec:
		op := r.op()
		lhs := r.expr()
		pos := r.pos()
		n := ir.NewAssignOpStmt(pos, op, lhs, ir.NewBasicLit(pos, one))
		n.IncDec = true
		return n

	case stmtBranch:
		pos := r.pos()
		op := r.op()
		sym := r.optLabel()
		return ir.NewBranchStmt(pos, op, sym)

	case stmtCall:
		pos := r.pos()
		op := r.op()
		call := r.expr()
		return ir.NewGoDeferStmt(pos, op, call)

	case stmtReturn:
		pos := r.pos()
		results := r.exprList()
		return ir.NewReturnStmt(pos, results)

	case stmtIf:
		return r.ifStmt()

	case stmtFor:
		return r.forStmt()

	case stmtSwitch:
		return r.switchStmt()

	case stmtSelect:
		return r.selectStmt()

	case stmtTypeDeclHack:
		// fake "type _ = int" declaration to prevent inlining
		assert(quirksMode())

		name := ir.NewDeclNameAt(src.NoXPos, ir.OTYPE, ir.BlankNode.Sym())
		name.SetAlias(true)
		r.setType(name, types.Types[types.TINT])

		n := ir.NewDecl(src.NoXPos, ir.ODCLTYPE, name)
		n.SetTypecheck(1)
		return n
	}
}

func (r *reader) compLit() ir.Node {
	r.sync(syncCompLit)
	pos := r.pos()
	typ := r.typ()

	isPtrLit := typ.IsPtr()
	if isPtrLit {
		typ = typ.Elem()
	}
	if typ.Kind() == types.TFORW {
		base.FatalfAt(pos, "dont know the kind of %v", typ)
	}
	isStruct := typ.Kind() == types.TSTRUCT

	elems := make([]ir.Node, r.len())
	for i := range elems {
		var elem ir.Node
		if isStruct {
			pos := r.pos()
			field := typ.Field(r.len())
			value := r.wrapname(r.expr())
			kv := ir.NewStructKeyExpr(pos, field.Sym, value)
			kv.Selection = field
			elem = kv
		} else if r.bool() {
			pos := r.pos()
			key := r.expr()
			value := r.wrapname(r.expr())
			elem = ir.NewKeyExpr(pos, key, value)
		} else {
			elem = r.wrapname(r.expr())
		}
		elems[i] = elem
	}

	lit := ir.NewCompLitExpr(pos, ir.OCOMPLIT, ir.TypeNode(typ), elems)
	if isPtrLit {
		return typecheck.NodAddrAt(pos, lit)
	}
	return lit
}

func (r *reader) wrapname(x ir.Node) ir.Node {
	r.sync(syncWrapname)
	pos := r.pos()

	// These nodes do not carry line numbers.
	// Introduce a wrapper node to give them the correct line.
	switch ir.Orig(x).Op() {
	case ir.OTYPE, ir.OLITERAL:
		if x.Sym() == nil {
			break
		}
		fallthrough
	case ir.ONAME, ir.ONONAME, ir.OPACK, ir.ONIL:
		p := ir.NewParenExpr(pos, x)
		p.SetImplicit(true)
		return p
	}
	return x
}

func (r *reader) assignList() ([]*ir.Name, []ir.Node) {
	lhs := make([]ir.Node, r.len())
	var names []*ir.Name

	for i := range lhs {
		if r.bool() {
			pos := r.pos()
			sym := r.sym()
			typ := r.typ()

			name := ir.NewNameAt(pos, sym)
			lhs[i] = name
			names = append(names, name)
			r.setType(name, typ)
			r.addLocal(name, ir.PAUTO)
			continue
		}

		lhs[i] = r.expr()
	}

	return names, lhs
}

func (r *reader) addLocal(name *ir.Name, ctxt ir.Class) {
	assert(ctxt == ir.PAUTO || ctxt == ir.PPARAM || ctxt == ir.PPARAMOUT)

	r.sync(syncAddLocal)
	if debug {
		want := r.int()
		if have := len(r.locals); have != want {
			base.FatalfAt(name.Pos(), "locals table has desynced")
		}
	}

	name.SetUsed(true)
	r.locals = append(r.locals, name)

	// TODO(mdempsky): Move earlier.
	if ir.IsBlank(name) {
		return
	}

	if r.inlCall != nil {
		if ctxt == ir.PAUTO {
			name.SetInlLocal(true)
		} else {
			name.SetInlFormal(true)
			ctxt = ir.PAUTO
		}

		// TODO(mdempsky): Rethink this hack.
		if strings.HasPrefix(name.Sym().Name, "~") || base.Flag.GenDwarfInl == 0 {
			name.SetPos(r.inlCall.Pos())
			name.SetInlFormal(false)
			name.SetInlLocal(false)
		}
	}

	name.Class = ctxt
	name.Curfn = r.curfn

	r.curfn.Dcl = append(r.curfn.Dcl, name)

	if ctxt == ir.PAUTO {
		name.SetFrameOffset(0)
	}
}

// initDefn marks the given names as declared by defn and populates
// its Init field with ODCL nodes. It then reports whether any names
// were so declared, which can be used to initialize defn.Def.
func (r *reader) initDefn(defn ir.InitNode, names []*ir.Name) bool {
	if len(names) == 0 {
		return false
	}

	init := make([]ir.Node, len(names))
	for i, name := range names {
		name.Defn = defn
		init[i] = ir.NewDecl(name.Pos(), ir.ODCL, name)
	}
	defn.SetInit(init)
	return true
}

func (r *reader) blockStmt() []ir.Node {
	r.sync(syncBlockStmt)
	r.openScope()
	stmts := r.stmts()
	r.closeScope()
	return stmts
}

func (r *reader) ifStmt() ir.Node {
	r.sync(syncIfStmt)
	r.openScope()
	pos := r.pos()
	init := r.stmts()
	cond := r.expr()
	then := r.blockStmt()
	els := r.stmts()
	n := ir.NewIfStmt(pos, cond, then, els)
	n.SetInit(init)
	r.closeAnotherScope()
	return n
}

func (r *reader) forStmt() ir.Node {
	r.sync(syncForStmt)
	label := r.optLabel()

	r.openScope()

	if r.bool() {
		pos := r.pos()
		names, lhs := r.assignList()
		x := r.expr()
		body := r.blockStmt()
		r.closeAnotherScope()

		rang := ir.NewRangeStmt(pos, nil, nil, x, body)
		if len(lhs) >= 1 {
			rang.Key = lhs[0]
			if len(lhs) >= 2 {
				rang.Value = lhs[1]
			}
		}
		rang.Def = r.initDefn(rang, names)
		rang.Label = label
		return rang
	}

	pos := r.pos()
	init := r.stmt()
	cond := r.expr()
	post := r.stmt()
	body := r.blockStmt()
	r.closeAnotherScope()

	stmt := ir.NewForStmt(pos, init, cond, post, body)
	stmt.Label = label
	return stmt
}

func (r *reader) switchStmt() ir.Node {
	r.sync(syncSwitchStmt)
	label := r.optLabel()

	r.openScope()
	pos := r.pos()
	init := r.stmt()
	tag := r.expr()

	tswitch, ok := tag.(*ir.TypeSwitchGuard)
	if ok && tswitch.Tag == nil {
		tswitch = nil
	}

	clauses := make([]*ir.CaseClause, r.len())
	for i := range clauses {
		if i > 0 {
			r.closeScope()
		}
		r.openScope()

		pos := r.pos()
		cases := r.exprList()

		clause := ir.NewCaseStmt(pos, cases, nil)
		if tswitch != nil {
			pos := r.pos()
			typ := r.typ()

			name := ir.NewNameAt(pos, tswitch.Tag.Sym())
			r.setType(name, typ)
			r.addLocal(name, ir.PAUTO)
			clause.Var = name
			name.Defn = tswitch
		}

		clause.Body = r.stmts()
		clauses[i] = clause
	}
	if len(clauses) > 0 {
		r.closeScope()
	}
	r.closeScope()

	n := ir.NewSwitchStmt(pos, tag, clauses)
	n.Label = label
	if init != nil {
		n.SetInit([]ir.Node{init})
	}
	return n
}

func (r *reader) selectStmt() ir.Node {
	r.sync(syncSelectStmt)
	label := r.optLabel()

	pos := r.pos()
	clauses := make([]*ir.CommClause, r.len())
	for i := range clauses {
		if i > 0 {
			r.closeScope()
		}
		r.openScope()

		pos := r.pos()
		comm := r.stmt()
		body := r.stmts()

		clauses[i] = ir.NewCommStmt(pos, comm, body)
	}
	if len(clauses) > 0 {
		r.closeScope()
	}
	n := ir.NewSelectStmt(pos, clauses)
	n.Label = label
	return n
}

func (r *reader) label() *types.Sym {
	r.sync(syncLabel)
	name := r.string()
	if r.inlCall != nil {
		name = fmt.Sprintf(".%s·%d", name, inlgen)
	}
	return typecheck.Lookup(name)
}

func (r *reader) optLabel() *types.Sym {
	r.sync(syncOptLabel)
	if r.bool() {
		return r.label()
	}
	return nil
}

func (r *reader) op() ir.Op {
	r.sync(syncOp)
	return ir.Op(r.len())
}

func (r *reader) origPos(xpos src.XPos) src.XPos {
	if r.inlCall == nil {
		return xpos
	}

	pos := base.Ctxt.PosTable.Pos(xpos)
	for old, new := range r.inlPosBases {
		if pos.Base() == new {
			pos.SetBase(old)
			return base.Ctxt.PosTable.XPos(pos)
		}
	}

	base.FatalfAt(xpos, "pos base missing from inlPosBases")
	panic("unreachable")
}

func (r *reader) funcLit() ir.Node {
	r.sync(syncFuncLit)

	pos := r.pos()
	typPos := r.pos()
	xtype2 := r.signature(r.curpkg, nil)

	opos := pos
	if quirksMode() {
		opos = r.origPos(pos)
	}

	// TODO(mdempsky): See if this can be rationalized better.
	outerfn := r.inlCaller
	if outerfn == nil {
		outerfn = r.curfn
	}

	fn := ir.NewFunc(opos)
	fn.SetIsHiddenClosure(outerfn != nil)

	// TODO(mdempsky): Consider turning pure closures into globals in
	// writer, and also deferring naming closures until walk when adding
	// them to Func.Closures.
	fn.Nname = ir.NewNameAt(opos, typecheck.ClosureName(outerfn))
	ir.MarkFunc(fn.Nname)
	fn.Nname.Func = fn
	fn.Nname.Defn = fn
	r.setType(fn.Nname, xtype2)
	if quirksMode() {
		fn.Nname.Ntype = ir.TypeNodeAt(typPos, xtype2)
	}

	fn.OClosure = ir.NewClosureExpr(pos, fn)

	fn.ClosureVars = make([]*ir.Name, r.len())
	for i := range fn.ClosureVars {
		pos := r.pos()
		outer := r.useLocal()

		cv := ir.NewNameAt(pos, outer.Sym())
		r.setType(cv, outer.Type())
		cv.Curfn = fn
		cv.Class = ir.PAUTOHEAP
		cv.SetIsClosureVar(true)
		cv.Defn = outer.Canonical()
		cv.Outer = outer

		fn.ClosureVars[i] = cv
	}

	r.addBody(fn)

	return fn.OClosure
}

func (r *reader) addBody(fn *ir.Func) {
	r.sync(syncAddBody)
	idx := r.reloc(relocBody)

	bodyIndex[fn] = readerBody{r.p, idx, r.targs}

	if r.curfn != nil {
		r.p.bodyIdx(fn, idx, r.targs)
	} else {
		todoBodies[fn] = true
	}
}

func (pr *pkgReader) bodyIdx(fn *ir.Func, idx int, targs []*types.Type) {
	r := pr.newReader(relocBody, idx)
	r.curpkg = fn.Sym().Pkg
	r.curfn = fn
	r.targs = targs
	r.locals = append([]*ir.Name(nil), r.curfn.ClosureVars...)

	r.funcBody(fn)
}

func (r *reader) funcBody(fn *ir.Func) {
	r.sync(syncFuncBody)

	outerCurFunc := ir.CurFunc
	ir.CurFunc = fn

	r.funcargs(fn)

	if r.bool() {
		body := r.stmts()
		if body == nil {
			pos := src.NoXPos
			if quirksMode() {
				pos = funcParamsEndPos(fn)
			}
			body = []ir.Node{ir.NewBlockStmt(pos, nil)}
		}
		fn.Body = body
		fn.Endlineno = r.pos()
	}

	ir.CurFunc = outerCurFunc
	r.marker.WriteTo(fn)
}

func (r *reader) funcargs(fn *ir.Func) {
	sig := fn.Nname.Type()

	if recv := sig.Recv(); recv != nil {
		r.funcarg(recv, recv.Sym, ir.PPARAM)
	}
	for _, param := range sig.Params().FieldSlice() {
		r.funcarg(param, param.Sym, ir.PPARAM)
	}

	for i, param := range sig.Results().FieldSlice() {
		sym := types.OrigSym(param.Sym)

		if sym == nil || sym.IsBlank() {
			prefix := "~r"
			if r.inlCall != nil {
				prefix = "~R"
			} else if sym != nil {
				prefix = "~b"
			}
			sym = typecheck.LookupNum(prefix, i)
		}

		r.funcarg(param, sym, ir.PPARAMOUT)
	}
}

func (r *reader) funcarg(param *types.Field, sym *types.Sym, ctxt ir.Class) {
	if sym == nil {
		assert(ctxt == ir.PPARAM)
		if r.inlCall != nil {
			r.inlvars.Append(ir.BlankNode)
		}
		return
	}

	name := ir.NewNameAt(r.updatePos(param.Pos), sym)
	r.setType(name, param.Type)
	r.addLocal(name, ctxt)

	if r.inlCall == nil {
		if !r.funarghack {
			param.Sym = sym
			param.Nname = name
		}
	} else {
		if ctxt == ir.PPARAMOUT {
			r.retvars.Append(name)
		} else {
			r.inlvars.Append(name)
		}
	}
}

func (r *reader) openScope() {
	r.sync(syncOpenScope)
	pos := r.pos()

	if base.Flag.Dwarf {
		r.scopeVars = append(r.scopeVars, len(r.curfn.Dcl))
		r.marker.Push(pos)
	}
}

func (r *reader) closeScope() {
	r.sync(syncCloseScope)
	r.lastCloseScopePos = r.pos()

	r.closeAnotherScope()
}

// closeAnotherScope is like closeScope, but it reuses the same mark
// position as the last closeScope call. This is useful for "for" and
// "if" statements, as their implicit blocks always end at the same
// position as an explicit block.
func (r *reader) closeAnotherScope() {
	r.sync(syncCloseAnotherScope)

	if base.Flag.Dwarf {
		scopeVars := r.scopeVars[len(r.scopeVars)-1]
		r.scopeVars = r.scopeVars[:len(r.scopeVars)-1]

		if scopeVars == len(r.curfn.Dcl) {
			// no variables were declared in this scope, so we can retract it.
			r.marker.Unpush()
		} else {
			r.marker.Pop(r.lastCloseScopePos)
		}
	}
}

func (r *reader) declName(ctxt ir.Class) *ir.Name {
	r.sync(syncDeclName)

	assert(ctxt == ir.PEXTERN || ctxt == ir.PFUNC)

	return r.doObj(nil, true).(*ir.Name)
}

func (r *reader) mangle(sym *types.Sym, targs []*types.Type) *types.Sym {
	if len(targs) == 0 {
		return sym
	}

	// TODO(mdempsky): Double check this mangling scheme. We need type
	// identity for the type arguments here (i.e., full package path and
	// vargen for each type argument).
	return sym.Pkg.Lookup(fmt.Sprintf("%s%v", sym.Name, targs))
}

func (r *reader) doObj(targs []*types.Type, must bool) ir.Node {
	r.sync(syncObject)

	return r.p.globalIdx(r.reloc(relocObj), r.targs, targs, must)
}

func (pr *pkgReader) globalIdx(idx int, implicit, targs []*types.Type, must bool) ir.Node {
	r := pr.newReader(relocObj, idx)
	r.bside = pr.newReader(relocObjExt, idx)
	r.curpkg = pr.curpkg
	r.bside.curpkg = pr.curpkg

	r.sync(syncObject1)

	sym := r.sym()
	origSym := sym

	// Middle dot indicates function-scoped defined type. See writer.sym.
	if strings.Contains(sym.Name, "·") {
		if n := len(implicit); n != 0 {
			targs = append(implicit[:n:n], targs...)
		}
	}

	sym = r.mangle(sym, targs)
	if !sym.IsBlank() && sym.Def != nil {
		return sym.Def.(ir.Node)
	}

	if sym.Name == "init" {
		if obj := pr.objs[idx]; obj != nil {
			return obj
		}
	}

	tag := codeObj(r.code(syncCodeObj))
	if tag != objStub {
		objBits[origSym] = pkgReaderIndex{r.p, idx}
	}

	do := func(op ir.Op, hasTParams bool) *ir.Name {
		pos := r.pos()
		if hasTParams {
			if !r.typeParams(sym, targs, must) {
				return nil
			}
		} else {
			assert(len(targs) == 0)
		}

		name := ir.NewDeclNameAt(pos, op, sym)
		name.Class = ir.PEXTERN // may be overridden later
		if !sym.IsBlank() {
			if sym.Def != nil {
				base.FatalfAt(name.Pos(), "already have a definition for %v", name)
			}
			assert(sym.Def == nil)
			sym.Def = name
		}
		if origSym.Name == "init" {
			r.p.objs[idx] = name
		}
		return name
	}

	switch tag {
	default:
		panic("unexpected decl kind")

	case objStub:
		assert(len(targs) != 0)
		b, ok := objBits[origSym]
		assert(ok)
		return b.pr.globalIdx(b.idx, nil, targs, true)

	case objAlias:
		if r.bool() {
			if !must {
				return nil
			}
			assert(len(targs) != 0)
			if len(targs) != 0 {
				ta := r.targs
				ta = ta[:len(ta):len(ta)]
				ta = append(ta, targs...)
				r.targs = ta
				r.bside.targs = ta
			}
		}

		name := do(ir.OTYPE, false)
		r.setType(name, r.typ())
		name.SetAlias(true)
		return name

	case objConst:
		name := do(ir.OLITERAL, false)
		typ, val := r.value()
		r.setType(name, typ)
		r.setValue(name, val)
		return name

	case objFunc:
		if sym.Name == "init" {
			sym = renameinit()
		}
		name := do(ir.ONAME, true)
		if name == nil {
			return nil
		}
		r.setType(name, r.signature(sym.Pkg, nil))

		name.Func = ir.NewFunc(r.pos())
		name.Func.Nname = name

		r.ext().funcExt(name)
		return name

	case objType:
		name := do(ir.OTYPE, true)
		if name == nil {
			return nil
		}
		typ := types.NewNamed(name)
		r.setType(name, typ)

		// Mark as an instantiated type, so we write out its type
		// descriptor as DUPOK.
		typ.SetInstance(len(r.targs) != 0)

		// Important: We need to do this before SetUnderlying.
		r.ext().typeExt(name)

		// We need to defer CheckSize until we've called SetUnderlying to
		// handle recursive types.
		types.DeferCheckSize()
		typ.SetUnderlying(r.typ())
		types.ResumeCheckSize()

		methods := make([]*types.Field, r.len())
		for i := range methods {
			methods[i] = r.method()
		}
		if len(methods) != 0 {
			typ.Methods().Set(methods)
		}

		return name

	case objVar:
		name := do(ir.ONAME, false)
		r.setType(name, r.typ())
		r.ext().varExt(name)
		return name
	}
}

func (r *reader) ext() *reader {
	if r.bside == nil {
		assert(r.top)
		return r
	}

	return r.bside
}

func (r *reader) typeExt(name *ir.Name) {
	r.sync(syncTypeExt)

	typ := name.Type()

	name.SetPragma(r.pragmaFlag())
	if name.Pragma()&ir.NotInHeap != 0 {
		// Important: this needs to happen before SetUnderlying.
		typ.SetNotInHeap(true)
	}

	if r.bool() {
		i, pi := r.int64(), r.int64()
		if i != -1 && pi != -1 {
			typecheck.TypeSymIdx[typ] = [2]int64{i, pi}
		}
	}
}

func (r *reader) varExt(name *ir.Name) {
	r.sync(syncVarExt)
	r.linkname(name)
}

func (r *reader) typeParams(sym *types.Sym, targs []*types.Type, must bool) bool {
	r.sync(syncTypeParams)

	if len(targs) != 0 {
		ta := r.targs
		ta = ta[:len(ta):len(ta)]
		ta = append(ta, targs...)
		r.targs = ta
		r.bside.targs = ta
	}

	n := r.len()
	if n != 0 && len(targs) == 0 && !must {
		return false
	}

	if len(r.targs) != n {
		base.Fatalf("have %v targs, but want %v for %v", len(r.targs), n, sym)
	}
	assert(len(r.targs) == n)

	for i := 0; i < n; i++ {
		// For now, we can just skip over all of the type parameter
		// data. Maybe eventually we want to use the bounds info for
		// something.
		r.pos()
		r.sym()
		r.typ() // bounds
	}

	return true
}

func (r *reader) funcExt(name *ir.Name) {
	r.sync(syncFuncExt)

	name.Class = 0 // so MarkFunc doesn't complain
	ir.MarkFunc(name)

	fn := name.Func

	// XXX: Workaround because linker doesn't know how to copy Pos.
	if !fn.Pos().IsKnown() {
		fn.SetPos(name.Pos())
	}

	if name.Sym().Pkg == types.LocalPkg || len(r.targs) != 0 {
		name.Defn = fn
	}

	fn.Pragma = r.pragmaFlag()
	r.linkname(name)

	if r.bool() {
		fn.ABI = obj.ABI(r.uint64())

		// Escape analysis.
		for _, fs := range &types.RecvsParams {
			for _, f := range fs(name.Type()).FieldSlice() {
				f.Note = r.string()
			}
		}

		if r.bool() {
			fn.Inl = &ir.Inline{
				Cost:            int32(r.len()),
				CanDelayResults: r.bool(),
			}
			r.addBody(name.Func)
		}
	} else {
		r.addBody(name.Func)
	}
	r.sync(syncEOF)
}

func (r *reader) linkname(name *ir.Name) {
	assert(name.Op() == ir.ONAME)
	sym := name.Sym()

	r.sync(syncLinkname)
	sym.Linkname = r.string()

	if r.bool() {
		lsym := sym.Linksym()
		idx := int32(r.int64())
		if idx != -1 {
			if sym.Linkname != "" {
				base.Fatalf("bad index for linknamed symbol: %v %d\n", lsym, idx)
			}
			lsym.SymIdx = idx
			lsym.Set(obj.AttrIndexed, true)
		}
	}
}

func (r *reader) method() *types.Field {
	r.sync(syncMethod)
	pos := r.pos()
	sym := r.selector()
	recv := r.param(r.curpkg)
	typ := r.signature(r.curpkg, recv)

	fnsym := sym
	if !fnsym.IsBlank() {
		fnsym = ir.MethodSym(recv.Type, fnsym)
	}
	name := ir.NewNameAt(pos, fnsym)
	r.setType(name, typ)

	name.Func = ir.NewFunc(r.pos())
	name.Func.Nname = name

	// TODO(mdempsky): Make sure we're handling //go:nointerface
	// correctly. I don't think this is exercised within the Go repo.

	r.ext().funcExt(name)

	meth := types.NewField(name.Func.Pos(), sym, typ)
	meth.Nname = name
	return meth
}

func (r *reader) typ() *types.Type {
	r.sync(syncType)

	if r.bool() {
		assert(len(r.targs) != 0)
		return r.doTyp()
	}

	return r.p.typIdx(r.reloc(relocType), r.curpkg)
}

func (pr *pkgReader) typIdx(idx int, curpkg *types.Pkg) *types.Type {
	r := pr.newReader(relocType, idx)

	r.curpkg = curpkg

	typ := r.doTyp()
	assert(typ != nil)

	if r.p.typs[idx] != nil {
		return r.p.typs[idx]
	}
	r.p.typs[idx] = typ

	if !typ.IsUntyped() && typ.Kind() != types.TUNION {
		types.CheckSize(typ)
	}
	return typ
}

func (r *reader) doTyp() (res *types.Type) {
	r.sync(syncTypeIdx)

	switch tag := codeType(r.code(syncType)); tag {
	case typeBasic:
		switch kind := r.uint64(); kind {
		case 100:
			return types.ByteType
		case 101:
			return types.RuneType
		case 200:
			return types.ErrorType.Underlying()
		case 201, 401: // comparable
			return nil // XXX: Shouldn't matter in practice anyway.
		case 400:
			return types.ErrorType
		default:
			return *basics[kind]
		}

	case typeNamed:
		obj := r.useObj()
		assert(obj.Op() == ir.OTYPE)
		assert(obj.Type() != nil)
		return obj.Type()

	case typeTypeParam:
		idx := r.len()
		return r.targs[idx]

	case typeArray:
		len := int64(r.uint64())
		elem := r.typ()
		return types.NewArray(elem, len)
	case typeChan:
		dir := dirs[r.uint64()]
		elem := r.typ()
		return types.NewChan(elem, dir)
	case typeMap:
		key := r.typ()
		elem := r.typ()
		return types.NewMap(key, elem)
	case typePointer:
		elem := r.typ()
		return types.NewPtr(elem)
	case typeSignature:
		tpkg := r.tpkg()
		return r.signature(tpkg, nil)
	case typeSlice:
		elem := r.typ()
		return types.NewSlice(elem)

	case typeStruct:
		tpkg := r.tpkg()
		fields := make([]*types.Field, r.len())
		for i := range fields {
			pos := r.pos()
			sym := r.selector()
			ftyp := r.typ()
			tag := r.string()
			embedded := r.bool()

			f := types.NewField(pos, sym, ftyp)
			f.Note = tag
			if embedded {
				f.Embedded = 1
			}
			fields[i] = f
		}
		return types.NewStruct(tpkg, fields)

	case typeInterface:
		tpkg := r.tpkg()
		nmethods, nembeddeds := r.len(), r.len()
		fields := make([]*types.Field, nmethods+nembeddeds)
		methods, embeddeds := fields[:nmethods], fields[nmethods:]
		for i := range methods {
			pos := r.pos()
			sym := r.selector()
			mtyp := r.signature(tpkg, typecheck.FakeRecv())
			methods[i] = types.NewField(pos, sym, mtyp)
		}
		for i := range embeddeds {
			embed := r.typ()
			embeddeds[i] = types.NewField(src.NoXPos, nil, embed)
		}

		if len(fields) == 0 {
			return types.Types[types.TINTER] // empty interface
		}
		return types.NewInterface(tpkg, fields)

	case typeUnion:
		terms := make([]*types.Type, r.len())
		tildes := make([]bool, len(terms))
		for i := range terms {
			terms[i] = r.typ()
			tildes[i] = r.bool()
		}
		return types.NewUnion(terms, tildes)

	default:
		base.FatalfAt(src.NoXPos, "unhandled type tag: %v", tag)
		panic("unreachable")
	}
}

func (r *reader) signature(tpkg *types.Pkg, recv *types.Field) *types.Type {
	r.sync(syncSignature)

	params := r.params(tpkg)
	results := r.params(tpkg)
	if r.bool() { // variadic
		params[len(params)-1].SetIsDDD(true)
	}

	return types.NewSignature(tpkg, recv, nil, params, results)
}

func (r *reader) params(tpkg *types.Pkg) []*types.Field {
	r.sync(syncParams)
	fields := make([]*types.Field, r.len())
	for i := range fields {
		fields[i] = r.param(tpkg)
	}
	return fields
}

func (r *reader) param(tpkg *types.Pkg) *types.Field {
	r.sync(syncParam)

	pos := r.pos()
	sym := r.sym()
	typ := r.typ()

	return types.NewField(pos, sym, typ)
}

func (r *reader) tpkg() *types.Pkg {
	r.sync(syncTypePkg)
	return r.pkg()
}

var inlgen = 0

func init() {
	inline.NewInline = InlineCall
}

func InlineCall(call *ir.CallExpr, fn *ir.Func, inlIndex int) *ir.InlinedCallExpr {
	// TODO(mdempsky): Make into a parameter?
	callerfn := ir.CurFunc

	bi, ok := bodyIndex[fn]
	if !ok {
		// Assume it's an imported function or something that we don't
		// have access to in quirks mode.
		if quirksMode() {
			return nil
		}

		// TODO: For -G=1 through -G=3 mode, fallback too.

		base.FatalfAt(call.Pos(), "missing function body index for call to %v", fn)
	}

	if fn.Inl.Body == nil {
		ExpandInline(fn)
	}

	r := bi.pr.newReader(relocBody, bi.idx)
	r.curpkg = fn.Sym().Pkg

	tmpfn := ir.NewFunc(fn.Pos())
	tmpfn.Nname = ir.NewNameAt(fn.Nname.Pos(), fn.Sym())
	r.setType(tmpfn.Nname, fn.Type())
	r.curfn = tmpfn

	r.targs = bi.targs

	r.inlCaller = ir.CurFunc
	r.inlCall = call
	r.inlFunc = fn
	r.inlTreeIndex = inlIndex
	r.inlPosBases = make(map[*src.PosBase]*src.PosBase)

	for _, cv := range r.inlFunc.ClosureVars {
		r.locals = append(r.locals, cv.Outer)
	}

	r.sync(syncFuncBody)

	init := ir.TakeInit(call)

	// For normal function calls, the function callee expression
	// may contain side effects (e.g., added by addinit during
	// inlconv2expr or inlconv2list). Make sure to preserve these,
	// if necessary (#42703).
	if call.Op() == ir.OCALLFUNC {
		callee := call.X
		for callee.Op() == ir.OCONVNOP {
			conv := callee.(*ir.ConvExpr)
			init.Append(ir.TakeInit(conv)...)
			callee = conv.X
		}
		if callee.Op() != ir.ONAME && callee.Op() != ir.OCLOSURE && callee.Op() != ir.OMETHEXPR {
			base.Fatalf("unexpected callee expression: %v", callee)
		}
	}

	var args ir.Nodes
	if call.Op() == ir.OCALLMETH {
		assert(call.X.Op() == ir.ODOTMETH)
		args.Append(call.X.(*ir.SelectorExpr).X)
	}
	args.Append(call.Args...)

	r.funcargs(fn)

	assert(r.bool()) // have body
	r.delayResults = fn.Inl.CanDelayResults

	// Create assignment to declare and initialize inlvars.
	as2 := ir.NewAssignListStmt(call.Pos(), ir.OAS2, r.inlvars, args)
	as2.Def = true
	var as2init ir.Nodes
	for _, name := range r.inlvars {
		if ir.IsBlank(name) {
			continue
		}
		// TODO(mdempsky): Use inlined position of name.Pos() instead?
		name := name.(*ir.Name)
		as2init.Append(ir.NewDecl(call.Pos(), ir.ODCL, name))
		name.Defn = as2
	}
	if len(as2.Rhs) > len(as2.Lhs) {
		base.FatalfAt(call.Pos(), "what why: %v is calling %v", call, fn)
	}
	as2.SetInit(as2init)
	init.Append(typecheck.Stmt(as2))

	if !r.delayResults {
		// If not delaying retvars, declare and zero initialize the
		// result variables now.
		for _, name := range r.retvars {
			// TODO(mdempsky): Use inlined position of name.Pos() instead?
			name := name.(*ir.Name)
			init.Append(ir.NewDecl(call.Pos(), ir.ODCL, name))
			ras := ir.NewAssignStmt(call.Pos(), name, nil)
			init.Append(typecheck.Stmt(ras))
		}
	}

	r.retlabel = typecheck.AutoLabel(".i")

	inlgen++

	// Add an inline mark just before the inlined body.
	// This mark is inline in the code so that it's a reasonable spot
	// to put a breakpoint. Not sure if that's really necessary or not
	// (in which case it could go at the end of the function instead).
	// Note issue 28603.
	init.Append(ir.NewInlineMarkStmt(call.Pos().WithIsStmt(), int64(r.inlTreeIndex)))

	nparams := len(r.curfn.Dcl)

	oldcurfn := ir.CurFunc
	ir.CurFunc = r.curfn

	r.curfn.Body = r.stmts()
	r.curfn.Endlineno = r.pos()

	typecheck.DirtyAddrtaken = true

	typecheck.Stmts(r.curfn.Body)

	deadcode.Func(r.curfn)

	{
		var edit func(ir.Node) ir.Node
		edit = func(n ir.Node) ir.Node {
			if ret, ok := n.(*ir.ReturnStmt); ok {
				n = typecheck.Stmt(r.editReturn(ret))
			}
			ir.EditChildren(n, edit)
			return n
		}
		edit(r.curfn)
	}

	ir.CurFunc = oldcurfn

	body := ir.Nodes(r.curfn.Body)

	if quirksMode() && len(body) == 1 {
		if block, ok := body[0].(*ir.BlockStmt); ok && len(block.List) == 0 {
			block.SetPos(r.updatePos(src.NoXPos))
		}
	}

	// Eagerly prune variables added during inlining, but removed by
	// deadcode.FuncBody above. Unused variables will get removed
	// during stack frame layout anyway, but len(fn.Dcl) ends up
	// influencing things like autotmp naming.

	var used ir.NameSet
	ir.VisitList(body, func(n ir.Node) {
		if n, ok := n.(*ir.Name); ok && n.Op() == ir.ONAME && n.Class == ir.PAUTO {
			used.Add(n)
		}
	})

	for i, name := range r.curfn.Dcl {
		if i < nparams || used.Has(name) {
			name.Curfn = callerfn
			callerfn.Dcl = append(callerfn.Dcl, name)

			if name.AutoTemp() {
				name.SetEsc(ir.EscUnknown)

				if base.Flag.GenDwarfInl != 0 {
					name.SetInlLocal(true)
				} else {
					name.SetPos(r.inlCall.Pos())
				}
			}
		}
	}

	body.Append(ir.NewLabelStmt(call.Pos(), r.retlabel))

	res := ir.NewInlinedCallExpr(call.Pos(), body, append([]ir.Node(nil), r.retvars...))
	res.SetInit(init)
	res.SetType(call.Type())
	res.SetTypecheck(1)

	return res
}

func (r *reader) editReturn(ret *ir.ReturnStmt) ir.Node {
	pos := r.inlCall.Pos()

	block := ir.TakeInit(ret)

	if results := ret.Results; len(results) != 0 {
		assert(len(r.retvars) == len(results))

		as2 := ir.NewAssignListStmt(pos, ir.OAS2, append([]ir.Node(nil), r.retvars...), ret.Results)

		if r.delayResults {
			for _, name := range r.retvars {
				// TODO(mdempsky): Use inlined position of name.Pos() instead?
				name := name.(*ir.Name)
				block.Append(ir.NewDecl(pos, ir.ODCL, name))
				name.Defn = as2
			}
		}

		block.Append(as2)
	}

	block.Append(ir.NewBranchStmt(pos, ir.OGOTO, r.retlabel))
	return ir.NewBlockStmt(pos, block)
}

func ExpandInline(fn *ir.Func) {
	if quirksMode() {
		return
	}

	bi, ok := bodyIndex[fn]
	if !ok {
		if fn.Sym().Name == "init" || strings.HasSuffix(fn.Sym().Name, "-fm") {
			return
		}

		base.FatalfAt(fn.Pos(), "missing bodyIndex entry for %v", fn)
	}
	assert(ok)

	// Inflate an extra copy to save as fn.Inl.{Dcl,Body}.
	// Currently dwarfgen relies on this.

	fndcls := len(fn.Dcl)

	tmpfn := ir.NewFunc(fn.Pos())
	tmpfn.Nname = ir.NewNameAt(fn.Nname.Pos(), fn.Sym())

	{
		r := bi.pr.newReader(relocBody, bi.idx)
		r.curpkg = fn.Sym().Pkg

		r.setType(tmpfn.Nname, fn.Type())
		r.curfn = tmpfn
		r.targs = bi.targs

		r.locals = append(r.locals, fn.ClosureVars...)

		r.funarghack = true

		r.funcBody(tmpfn)
	}

	oldcurfn := ir.CurFunc
	ir.CurFunc = tmpfn

	typecheck.DirtyAddrtaken = true

	ndcls := len(typecheck.Target.Decls)
	typecheck.Stmts(tmpfn.Body)
	typecheck.Target.Decls = typecheck.Target.Decls[:ndcls]

	deadcode.Func(tmpfn)

	ir.CurFunc = oldcurfn

	var used ir.NameSet
	ir.VisitList(tmpfn.Body, func(n ir.Node) {
		if n, ok := n.(*ir.Name); ok && n.Op() == ir.ONAME && n.Class == ir.PAUTO {
			used.Add(n)
		}
	})

	for _, name := range tmpfn.Dcl {
		if name.Class != ir.PAUTO || used.Has(name) {
			name.Curfn = fn
			fn.Inl.Dcl = append(fn.Inl.Dcl, name)
		}
	}
	fn.Inl.Body = tmpfn.Body

	assert(fndcls == len(fn.Dcl))
}
