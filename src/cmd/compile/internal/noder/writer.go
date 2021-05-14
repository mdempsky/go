// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package noder

import (
	"bytes"
	"fmt"
	"go/constant"
	"io"

	"cmd/compile/internal/base"
	"cmd/compile/internal/ir"
	"cmd/compile/internal/syntax"
	"cmd/compile/internal/types2"
	"cmd/internal/src"
)

func writePkgBits(data io.Writer, noders []*noder) {
	importer := &importer2{
		packages: make(map[string]*types2.Package),
	}

	m, pkg, info := checkFiles(noders, importer)

	pw := newPkgWriter(m, pkg, info)

	publicRootWriter := pw.newWriter(relocMeta)
	privateRootWriter := pw.newWriter(relocMeta)

	assert(publicRootWriter.idx == publicRootIdx)
	assert(privateRootWriter.idx == privateRootIdx)

	{
		// TODO(mdempsky): Turn into a b-side of the public index.
		w := privateRootWriter
		w.top = true
		w.pack(noders)
		w.flush()
	}

	{
		w := publicRootWriter
		w.sync(syncPublic)
		w.pkg(pkg)
		w.bool(false) // has init; XXX

		scope := pkg.Scope()
		names := scope.Names()
		w.len(len(names))
		for _, name := range scope.Names() {
			w.rawObj(scope.Lookup(name))
		}

		w.sync(syncEOF)
		w.flush()
	}

	pw.dump(data)
}

func newPkgWriter(m posMap, pkg *types2.Package, info *types2.Info) *pkgWriter {
	return &pkgWriter{
		pkgEncoder: newPkgEncoder(),

		m:      m,
		curpkg: pkg,
		info:   info,

		pkgsIdx:    make(map[*types2.Package]int),
		globalsIdx: make(map[types2.Object]int),
		typsIdx:    make(map[types2.Type]int),

		posBasesIdx: make(map[*syntax.PosBase]int),

		funDecls: make(map[*types2.Func]*syntax.FuncDecl),
		typDecls: make(map[*types2.TypeName]typeDeclGen),

		linknames: make(map[types2.Object]string),
	}
}

func (pw *pkgWriter) newWriter(k reloc) *writer {
	return &writer{
		encoder: pw.newEncoder(k),
		p:       pw,
	}
}

func (w *writer) checkPragmas(p syntax.Pragma, allowed ir.PragmaFlag, embedOK bool) {
	if p == nil {
		return
	}
	pragma := p.(*pragmas)

	for _, pos := range pragma.Pos {
		if pos.Flag&^allowed != 0 {
			w.p.errorf(pos.Pos, "misplaced compiler directive")
		}
	}

	if !embedOK {
		for _, e := range pragma.Embeds {
			w.p.errorf(e.Pos, "misplaced go:embed directive")
		}
	}
}

func (w *writer) pack(noders []*noder) {
	// Import all packages ahead of time.
	seenImport := make(map[string]bool)
	var importPaths []string
	var cgoPragmas [][]string
	var typegen int
	for _, p := range noders {
		var importedEmbed, importedUnsafe bool
		cgoPragmas = append(cgoPragmas, p.pragcgobuf...)

		syntax.Walk(p.file, func(n syntax.Node) bool {
			switch n := n.(type) {
			case *syntax.File:
				w.checkPragmas(n.Pragma, ir.GoBuildPragma, false)

			case *syntax.ImportDecl:
				w.checkPragmas(n.Pragma, 0, false)

				path := pkgNameOf(w.p.info, n).Imported().Path()

				switch path {
				case "embed":
					importedEmbed = true
				case "unsafe":
					importedUnsafe = true
				}

				if !seenImport[path] {
					seenImport[path] = true
					importPaths = append(importPaths, path)
				}

			case *syntax.ConstDecl:
				w.checkPragmas(n.Pragma, 0, false)

			case *syntax.FuncDecl:
				w.checkPragmas(n.Pragma, funcPragmas, false)
				obj := w.p.info.Defs[n.Name].(*types2.Func)
				w.p.funDecls[obj] = n

			case *syntax.TypeDecl:
				if n.Alias {
					w.checkPragmas(n.Pragma, 0, false)
				} else {
					w.checkPragmas(n.Pragma, typePragmas, false)
				}

				obj := w.p.info.Defs[n.Name].(*types2.TypeName)
				d := typeDeclGen{TypeDecl: n}
				if !n.Alias && !isGlobal(obj) {
					// Local defined types need unique IDs.
					typegen++
					d.gen = typegen
				}
				w.p.typDecls[obj] = d

			case *syntax.VarDecl:
				w.checkPragmas(n.Pragma, 0, true)

				if p, ok := n.Pragma.(*pragmas); ok && len(p.Embeds) > 0 {
					obj := w.p.info.Defs[n.NameList[0]].(*types2.Var)
					// TODO(mdempsky): isGlobal(obj) gives false positive errors
					// for //go:embed directives on package-scope blank
					// variables.
					if err := checkEmbed(n, importedEmbed, !isGlobal(obj)); err == nil {
						w.p.embeds = append(w.p.embeds, writerEmbed{obj, p.Embeds})
					} else {
						w.p.errorf(p.Embeds[0].Pos, "%s", err)
					}
				}

				// Workaround for #46208.
				if quirksMode() && n.Type != nil {
					tv, ok := w.p.info.Types[n.Type]
					assert(ok)
					assert(tv.IsType())
					for _, name := range n.NameList {
						obj := w.p.info.Defs[name].(*types2.Var)
						w.p.dups.add(obj.Type(), tv.Type)
					}
				}
			}
			return false
		})

		for _, l := range p.linknames {
			if !importedUnsafe {
				w.p.errorf(l.pos, "//go:linkname only allowed in Go files that import \"unsafe\"")
				continue
			}

			switch obj := w.p.curpkg.Scope().Lookup(l.local).(type) {
			case *types2.Func, *types2.Var:
				if _, ok := w.p.linknames[obj]; !ok {
					w.p.linknames[obj] = l.remote
				} else {
					w.p.errorf(l.pos, "duplicate //go:linkname for %s", l.local)
				}

			default:
				// TODO(mdempsky): Enable after #42938 is fixed.
				if false {
					w.p.errorf(l.pos, "//go:linkname must refer to declared function or variable")
				}
			}
		}
	}

	w.string(w.p.curpkg.Name())
	w.len(w.p.curpkg.Height())

	w.strings(importPaths)

	w.len(len(cgoPragmas))
	for _, cgoPragma := range cgoPragmas {
		w.strings(cgoPragma)
	}

	if quirksMode() {
		posBases := posBasesOf(noders)
		w.len(len(posBases))
		for _, posBase := range posBases {
			w.posBase(posBase)
		}

		objs := importedObjsOf(w.p.curpkg, w.p.info, noders)
		w.len(len(objs))
		for _, obj := range objs {
			w.sym(obj)
		}
	}

	var decls []syntax.Decl
	for _, p := range noders {
		decls = append(decls, p.file.DeclList...)
	}
	w.decls(decls)

	w.len(len(w.p.externs))
	for _, extern := range w.p.externs {
		w.rawObj(extern)
	}

	// TODO(mdempsky): Fuse into the externs loop?
	w.len(len(w.p.embeds))
	for _, embed := range w.p.embeds {
		w.rawObj(embed.obj)

		// TODO(mdempsky): These variable names are terrible.
		w.len(len(embed.embeds))
		for _, embed := range embed.embeds {
			w.pos(embed.Pos)
			w.strings(embed.Patterns)
		}
	}

	w.sync(syncEOF)
}

type pkgWriter struct {
	pkgEncoder

	m      posMap
	curpkg *types2.Package
	info   *types2.Info

	data0 bytes.Buffer

	pkgsIdx    map[*types2.Package]int
	globalsIdx map[types2.Object]int
	typsIdx    map[types2.Type]int

	posBasesIdx map[*syntax.PosBase]int

	funDecls map[*types2.Func]*syntax.FuncDecl
	typDecls map[*types2.TypeName]typeDeclGen

	externs   []types2.Object
	embeds    []writerEmbed
	linknames map[types2.Object]string

	dups dupTypes
}

type writerEmbed struct {
	obj    *types2.Var
	embeds []pragmaEmbed
}

type writerBody struct {
	sig  *types2.Signature
	body *syntax.BlockStmt
}

type writer struct {
	p *pkgWriter

	encoder

	// TODO(mdempsky): This is a little hacky, but works easiest with
	// the way things are currently.
	bside *writer

	top bool

	curfn      *types2.Signature
	tparamsIdx map[*types2.TypeParam]int

	// variables declared within this function
	localsIdx map[types2.Object]int
}

type typeDeclGen struct {
	*syntax.TypeDecl
	gen int
}

func (pw *pkgWriter) errorf(p poser, msg string, args ...interface{}) {
	base.ErrorfAt(pw.m.pos(p), msg, args...)
}

func (pw *pkgWriter) fatalf(p poser, msg string, args ...interface{}) {
	base.FatalfAt(pw.m.pos(p), msg, args...)
}

func (w *writer) pos(pos syntax.Pos) {
	w.sync(syncPos)
	if !w.bool(pos.IsKnown()) {
		// TODO(mdempsky): Track these cases down and fix them.
		return
	}

	// TODO(mdempsky): Delta encoding. Also, if there's a b-side, update
	// its position base too (but not vice versa!).
	w.posBase(pos.Base())
	w.uint(pos.Line())
	w.uint(pos.Col())
}

func (w *writer) posBase(b *syntax.PosBase) {
	w.reloc(relocPosBase, w.p.posBaseIdx(b))
}

func (pw *pkgWriter) posBaseIdx(b *syntax.PosBase) int {
	if idx, ok := pw.posBasesIdx[b]; ok {
		return idx
	}

	w := pw.newWriter(relocPosBase)
	w.p.posBasesIdx[b] = w.idx

	w.string(b.Filename())
	if !w.bool(b.IsFileBase()) {
		w.pos(b.Pos())
		w.uint(b.Line())
		w.uint(b.Col())
	}

	return w.flush()
}

func (w *writer) pragmaFlag(p ir.PragmaFlag) {
	w.sync(syncPragma)
	w.int(int(p))
}

func getPragma(p syntax.Pragma) ir.PragmaFlag {
	if p == nil {
		return 0
	}
	return p.(*pragmas).Flag
}

func (w *writer) decls(decls []syntax.Decl) {
	w.sync(syncDecls)
	for _, decl := range decls {
		switch decl := decl.(type) {
		default:
			panic("unhandled Decl")

		case *syntax.ImportDecl:

		case *syntax.ConstDecl:
			for _, name := range decl.NameList {
				if name.Value == "_" {
					continue
				}
				//				w.int(1)
				w.declName(name, false)
			}

		case *syntax.TypeDecl:
			if len(decl.TParamList) != 0 {
				continue // skip generic type decls
			}
			if decl.Name.Value == "_" {
				continue
			}

			// Skip generic alias.
			if decl.Alias {
				named, ok := w.p.info.Defs[decl.Name].(*types2.TypeName).Type().(*types2.Named)
				if ok && len(named.TParams()) != 0 && len(named.TArgs()) == 0 {
					continue
				}
			}

			//			w.int(1)
			w.declName(decl.Name, false)

		case *syntax.VarDecl:
			w.int(2)
			w.pos(decl.Pos())
			w.declNames(decl.NameList, true)
			w.exprList(decl.Values)

		case *syntax.FuncDecl:
			obj := w.p.info.Defs[decl.Name].(*types2.Func)
			sig := obj.Type().(*types2.Signature)

			if sig.RParams() != nil || sig.TParams() != nil {
				continue // skip generic func decls
			}

			if decl.Recv == nil || decl.Name.Value == "_" {
				w.int(5)
				w.declName(decl.Name, true)
				continue
			}

			w.int(6)
			w.typ(recvBase(sig))
			w.selector(obj)
		}
	}
	w.int(0)
}

func (w *writer) declNames(names []*syntax.Name, do bool) {
	if do {
		w.sync(syncDeclNames)
		w.len(len(names))
	}
	for _, name := range names {
		w.declName(name, do)
	}
}

func (w *writer) declName(name *syntax.Name, do bool) {
	if do {
		w.sync(syncDeclName)
	}

	obj, ok := w.p.info.Defs[name]
	assert(ok)
	assert(obj.Pos() == name.Pos())
	assert(!isMethod(obj) || obj.Name() == "_")
	assert(obj.Name() != "")

	if do {
		w.rawObj(obj)
	}

	if obj.Name() != "_" {
		assert(isGlobal(obj))
		w.p.externs = append(w.p.externs, obj)
	}
}

func (w *writer) useLocal(obj types2.Object) {
	w.sync(syncUseObjLocal)
	idx, ok := w.localsIdx[obj]
	assert(ok)
	w.len(idx)
}

func (w *writer) useObj(obj types2.Object, targs []types2.Type) {
	w.sync(syncUseObj)
	assert(obj.Name() != "_")
	assert(!isMethod(obj))

	switch obj.(type) {
	case *types2.Var, *types2.Func, *types2.TypeName, *types2.Builtin, *types2.Nil:
		// ok
	default:
		w.p.fatalf(obj, "huh, what is this: %v", obj)
	}

	if !(isGlobal(obj) || isDefinedType(obj)) {
		w.p.fatalf(obj.Pos(), "what is this: %v", obj)
	}

	// TODO(mdempsky): Storing the number of type arguments here is
	// redundant, because the decoder can see how many type parameters
	// the object has. However, currently the stenciling reader uses the
	// type arguments while instancing the object. This should be
	// revisited at some point though.
	w.len(len(targs))
	for _, targ := range targs {
		w.typ(targ)
	}

	assert(isGlobal(obj) || isDefinedType(obj))

	w.rawObj(obj)
}

func (w *writer) value(typ types2.Type, val constant.Value) {
	w.sync(syncValue)
	w.typ(typ)
	w.rawValue(val)
}

func (w *writer) exprList(expr syntax.Expr) {
	w.sync(syncExprList)
	w.exprs(unpackListExpr(expr))
}

func (w *writer) exprs(exprs []syntax.Expr) {
	if len(exprs) == 0 {
		assert(exprs == nil)
	}

	w.sync(syncExprs)
	w.len(len(exprs))
	for _, expr := range exprs {
		w.expr(expr)
	}
}

func (w *writer) pkg(pkg *types2.Package) {
	w.sync(syncPkg)
	w.reloc(relocPkg, w.p.pkgIdx(pkg))
}

func (pw *pkgWriter) pkgIdx(pkg *types2.Package) int {
	if idx, ok := pw.pkgsIdx[pkg]; ok {
		return idx
	}

	w := pw.newWriter(relocPkg)
	pw.pkgsIdx[pkg] = w.idx

	w.sync(syncPkgDef)

	if pkg == nil {
		w.string("builtin")
	} else {
		var path string
		if pkg != w.p.curpkg {
			path = pkg.Path()
		}
		w.string(path)
		w.string(pkg.Name())
		w.len(pkg.Height())

		w.len(len(pkg.Imports()))
		for _, imp := range pkg.Imports() {
			w.pkg(imp)
		}
	}

	return w.flush()
}

func (w *writer) sym(obj types2.Object) {
	w.sync(syncSym)
	name := obj.Name()
	if isDefinedType(obj) && !isGlobal(obj) {
		// XXX: This is a bit hacky.
		decl, ok := w.p.typDecls[obj.(*types2.TypeName)]
		assert(ok)
		name = fmt.Sprintf("%s·%v", name, decl.gen)
	}
	w.string(name)
	if name != "" {
		w.pkg(obj.Pkg())
	}
}

func (w *writer) selector(obj types2.Object) {
	w.sync(syncSelector)
	w.string(obj.Name())
	if !obj.Exported() {
		w.pkg(obj.Pkg())
	}
}

func (w writer) lookupName(expr syntax.Expr) (types2.Object, []types2.Type, bool) {
	var targs []types2.Type

	if index, ok := expr.(*syntax.IndexExpr); ok {
		if inf, ok := w.p.info.Inferred[index]; ok {
			targs = inf.Targs
		} else {
			args := unpackListExpr(index.Index)
			if len(args) == 1 {
				tv, ok := w.p.info.Types[args[0]]
				assert(ok)
				if tv.IsValue() {
					return nil, nil, false // normal index expression
				}
			}
			targs = make([]types2.Type, len(args))
			for i, arg := range args {
				tv, ok := w.p.info.Types[arg]
				assert(ok)
				assert(tv.IsType())
				targs[i] = tv.Type
			}
		}
		expr = index.X
	}

	// Strip package qualifier, if present.
	if sel, ok := expr.(*syntax.SelectorExpr); ok {
		if !w.p.isPkgQual(sel) {
			return nil, nil, false // normal selector expression
		}
		expr = sel.Sel
	}

	if name, ok := expr.(*syntax.Name); ok {
		obj, ok := w.p.info.Uses[name]
		return obj, targs, ok
	}
	assert(targs == nil)
	return nil, nil, false
}

func (pw *pkgWriter) isPkgQual(sel *syntax.SelectorExpr) bool {
	if name, ok := sel.X.(*syntax.Name); ok {
		if _, isPkgName := pw.info.Uses[name].(*types2.PkgName); isPkgName {
			return true
		}
	}
	return false
}

func (w *writer) expr(expr syntax.Expr) {
	expr = unparen(expr) // skip parens; unneeded after typecheck

	obj, targs, isName := w.lookupName(expr)

	if tv, ok := w.p.info.Types[expr]; ok {
		if tv.IsType() {
			w.code(exprType)
			//			w.pos(expr.Pos())
			w.typ(tv.Type)
			return
		}

		if tv.Value != nil {
			pos := expr.Pos()
			if quirksMode() {
				if isName {
					// Quirk: IR (and thus iexport) doesn't track position
					// information for uses of declared objects.
					pos = syntax.Pos{}
				} else if tv.Value.Kind() == constant.String {
					// Quirk: noder.sum picks a particular position for certain
					// string concatenations.
					pos = sumPos(expr)
				}
			}

			w.code(exprConst)
			w.pos(pos)
			w.value(tv.Type, tv.Value)

			// TODO(mdempsky): These details are only important for backend
			// diagnostics. Explore writing them out separately.
			w.op(constExprOp(expr))
			w.string(syntax.String(expr))
			return
		}
	}

	if isName {
		if _, ok := w.localsIdx[obj]; ok {
			assert(len(targs) == 0)
			w.code(exprLocal)
			w.useLocal(obj)
			return
		}

		w.code(exprName)
		w.useObj(obj, targs)
		return
	}

	switch expr := expr.(type) {
	default:
		panic("unhandled expression")

	case nil: // absent slice index, for condition, or switch tag
		w.code(exprNone)

	case *syntax.Name:
		assert(expr.Value == "_")
		w.code(exprBlank)

	case *syntax.CompositeLit:
		w.code(exprCompLit)
		w.compLit(expr)

	case *syntax.FuncLit:
		w.code(exprFuncLit)
		w.funcLit(expr)

	case *syntax.SelectorExpr:
		sel, ok := w.p.info.Selections[expr]
		assert(ok)

		w.code(exprSelector)
		w.expr(expr.X)
		w.pos(expr.Pos())
		w.selector(sel.Obj())

	case *syntax.IndexExpr:
		tv, ok := w.p.info.Types[expr.Index]
		assert(ok && tv.IsValue())

		w.code(exprIndex)
		w.expr(expr.X)
		w.pos(expr.Pos())
		w.expr(expr.Index)

	case *syntax.SliceExpr:
		w.code(exprSlice)
		w.expr(expr.X)
		w.pos(expr.Pos())
		for _, n := range &expr.Index {
			w.expr(n)
		}

	case *syntax.AssertExpr:
		w.code(exprAssert)
		w.expr(expr.X)
		w.pos(expr.Pos())
		w.expr(expr.Type)

	case *syntax.Operation:
		if expr.Y == nil {
			w.code(exprUnaryOp)
			w.op(unOps[expr.Op])
			w.pos(expr.Pos())
			w.expr(expr.X)
			break
		}

		w.code(exprBinaryOp)
		w.op(binOps[expr.Op])
		w.expr(expr.X)
		w.pos(expr.Pos())
		w.expr(expr.Y)

	case *syntax.CallExpr:
		w.code(exprCall)

		if inf, ok := w.p.info.Inferred[expr]; ok {
			obj, _, ok := w.lookupName(expr.Fun)
			assert(ok)

			// As if w.expr(expr.Fun), but using inf.Targs instead.
			w.code(exprName)
			w.useObj(obj, inf.Targs)
		} else {
			w.expr(expr.Fun)
		}

		w.pos(expr.Pos())
		w.exprs(expr.ArgList)
		w.bool(expr.HasDots)

	case *syntax.TypeSwitchGuard:
		w.code(exprTypeSwitchGuard)
		w.pos(expr.Pos())
		if tag := expr.Lhs; w.bool(tag != nil) {
			w.pos(tag.Pos())
			w.string(tag.Value)
		}
		w.expr(expr.X)
	}
}

func (w *writer) compLit(lit *syntax.CompositeLit) {
	tv, ok := w.p.info.Types[lit]
	assert(ok)

	w.sync(syncCompLit)
	w.pos(lit.Pos())
	w.typ(tv.Type)

	typ := tv.Type
	if ptr, ok := typ.Underlying().(*types2.Pointer); ok {
		typ = ptr.Elem()
	}
	str, isStruct := typ.Underlying().(*types2.Struct)

	w.len(len(lit.ElemList))
	for i, elem := range lit.ElemList {
		if isStruct {
			idx := i
			if kv, ok := elem.(*syntax.KeyValueExpr); ok {
				// use position of expr.Key rather than of expr (which has position of ':')
				w.pos(kv.Key.Pos())

				idx = -1
				field := w.p.info.Uses[kv.Key.(*syntax.Name)].(*types2.Var)
				for j := 0; j < str.NumFields(); j++ {
					if str.Field(j) == field {
						idx = j
						break
					}
				}

				elem = kv.Value
			} else {
				w.pos(elem.Pos()) // implicit?
			}
			w.len(idx)
		} else {
			if kv, ok := elem.(*syntax.KeyValueExpr); w.bool(ok) {
				// use position of expr.Key rather than of expr (which has position of ':')
				w.pos(kv.Key.Pos())
				w.expr(kv.Key)
				elem = kv.Value
			}
		}
		w.expr(elem)
		w.wrapname(elem)
	}
}

func (w *writer) wrapname(n syntax.Node) {
	w.sync(syncWrapname)
	w.pos(n.Pos())
}

func (w *writer) stmt(stmt syntax.Stmt) {
	var stmts []syntax.Stmt
	if stmt != nil {
		stmts = []syntax.Stmt{stmt}
	}
	w.stmts(stmts)
}

func (w *writer) stmts(stmts []syntax.Stmt) {
	w.sync(syncStmts)
	for _, stmt := range stmts {
		w.stmt1(stmt, nil)
	}
	w.code(stmtEnd)
	w.sync(syncStmtsEnd)
}

func (w *writer) stmtDecls(decls []syntax.Decl) {
	for _, decl := range decls {
		switch decl := decl.(type) {
		default:
			w.p.fatalf(decl, "unexpected decl: %v", decl)

		case *syntax.ConstDecl:

		case *syntax.TypeDecl:
			if quirksMode() {
				// Write out a "type _ = int" type declaration, simply to
				// prevent inlining for toolstash -cmp compatibility.
				w.code(stmtTypeDeclHack)
			}

		case *syntax.VarDecl:
			values := unpackListExpr(decl.Values)

			if quirksMode() {
				if len(decl.NameList) == len(values) {
					for i, name := range decl.NameList {
						w.code(stmtAssign)
						w.pos(decl.Pos())
						w.assignList(name)
						w.exprList(values[i])
					}
					continue
				}
			}

			w.code(stmtAssign)
			w.pos(decl.Pos())
			w.assignList(namesAsExpr(decl.NameList))
			w.exprList(decl.Values)
		}
	}
}

func namesAsExpr(names []*syntax.Name) syntax.Expr {
	if len(names) == 1 {
		return names[0]
	}

	exprs := make([]syntax.Expr, len(names))
	for i, name := range names {
		exprs[i] = name
	}
	return &syntax.ListExpr{ElemList: exprs}
}

func (w *writer) stmt1(stmt syntax.Stmt, label *syntax.Name) {
	// Handle empty statements and declarations specially, so they don't
	// add extra sync markers.
	switch stmt := stmt.(type) {
	case nil, *syntax.EmptyStmt:
		return
	case *syntax.DeclStmt:
		w.stmtDecls(stmt.DeclList)
		return
	}

	switch stmt := stmt.(type) {
	default:
		panic("unhandled statement")

	case *syntax.LabeledStmt:
		w.code(stmtLabel)
		w.pos(stmt.Pos())
		w.label(stmt.Label)
		w.stmt1(stmt.Stmt, stmt.Label)

	case *syntax.BlockStmt:
		w.code(stmtBlock)
		w.blockStmt(stmt)

	case *syntax.ExprStmt:
		w.code(stmtExpr)
		w.expr(stmt.X)

	case *syntax.SendStmt:
		w.code(stmtSend)
		w.pos(stmt.Pos())
		w.expr(stmt.Chan)
		w.expr(stmt.Value)

	case *syntax.AssignStmt:
		if stmt.Rhs == nil {
			w.code(stmtIncDec)
			w.op(binOps[stmt.Op])
			w.expr(stmt.Lhs)
			w.pos(stmt.Pos())
			return
		}

		if stmt.Op != 0 && stmt.Op != syntax.Def {
			w.code(stmtAssignOp)
			w.op(binOps[stmt.Op])
			w.expr(stmt.Lhs)
			w.pos(stmt.Pos())
			w.expr(stmt.Rhs)
			return
		}

		w.code(stmtAssign)
		w.pos(stmt.Pos())
		w.assignList(stmt.Lhs)
		w.exprList(stmt.Rhs)

	case *syntax.BranchStmt:
		op := branchOps[stmt.Tok]

		w.code(stmtBranch)
		w.pos(stmt.Pos())
		w.op(op)
		w.optLabel(stmt.Label)

	case *syntax.CallStmt:
		op := callOps[stmt.Tok]

		w.code(stmtCall)
		w.pos(stmt.Pos())
		w.op(op)
		w.expr(stmt.Call)

	case *syntax.ReturnStmt:
		w.code(stmtReturn)
		w.pos(stmt.Pos())
		w.exprList(stmt.Results)

	case *syntax.IfStmt:
		w.code(stmtIf)
		w.ifStmt(stmt)

	case *syntax.ForStmt:
		w.code(stmtFor)
		w.forStmt(stmt, label)

	case *syntax.SwitchStmt:
		w.code(stmtSwitch)
		w.switchStmt(stmt, label)

	case *syntax.SelectStmt:
		w.code(stmtSelect)
		w.selectStmt(stmt, label)
	}
}

func (w *writer) label(label *syntax.Name) {
	// TODO(mdempsky): Densely number.
	w.sync(syncLabel)
	w.string(label.Value)
}

func (w *writer) optLabel(label *syntax.Name) {
	w.sync(syncOptLabel)
	if w.bool(label != nil) {
		w.label(label)
	}
}

func (w *writer) assignList(expr syntax.Expr) {
	exprs := unpackListExpr(expr)
	w.len(len(exprs))

	for _, expr := range exprs {
		if name, ok := expr.(*syntax.Name); ok && name.Value != "_" {
			if obj, ok := w.p.info.Defs[name]; ok {
				w.bool(true)
				w.pos(obj.Pos())
				w.sym(obj)
				w.typ(obj.Type())

				// TODO(mdempsky): Minimize locals index size by deferring
				// this until the variables actually come into scope.
				w.addLocal(obj)
				continue
			}
		}

		w.bool(false)
		w.expr(expr)
	}
}

func (w *writer) addLocal(obj types2.Object) {
	w.sync(syncAddLocal)
	idx := len(w.localsIdx)
	if debug {
		w.int(idx)
	}
	w.localsIdx[obj] = idx
}

func (w *writer) blockStmt(stmt *syntax.BlockStmt) {
	w.sync(syncBlockStmt)
	w.openScope(stmt.Pos())
	w.stmts(stmt.List)
	w.closeScope(stmt.Rbrace)
}

func (w *writer) ifStmt(stmt *syntax.IfStmt) {
	w.sync(syncIfStmt)
	w.openScope(stmt.Pos())
	w.pos(stmt.Pos())
	w.stmt(stmt.Init)
	w.expr(stmt.Cond)
	w.blockStmt(stmt.Then)
	w.stmt(stmt.Else)
	w.closeAnotherScope()
}

func (w *writer) forStmt(stmt *syntax.ForStmt, label *syntax.Name) {
	w.sync(syncForStmt)
	w.optLabel(label)
	w.openScope(stmt.Pos())

	if rang, ok := stmt.Init.(*syntax.RangeClause); w.bool(ok) {
		w.pos(rang.Pos())
		w.assignList(rang.Lhs)
		w.expr(rang.X)
	} else {
		w.pos(stmt.Pos())
		w.stmt(stmt.Init)
		w.expr(stmt.Cond)
		w.stmt(stmt.Post)
	}

	w.blockStmt(stmt.Body)
	w.closeAnotherScope()
}

func (w *writer) switchStmt(stmt *syntax.SwitchStmt, label *syntax.Name) {
	w.sync(syncSwitchStmt)
	w.optLabel(label)

	w.openScope(stmt.Pos())
	w.pos(stmt.Pos())
	w.stmt(stmt.Init)
	w.expr(stmt.Tag)

	w.len(len(stmt.Body))
	for i, clause := range stmt.Body {
		if i > 0 {
			w.closeScope(clause.Pos())
		}
		w.openScope(clause.Pos())

		w.pos(clause.Pos())
		w.exprList(clause.Cases)

		if obj, ok := w.p.info.Implicits[clause]; ok {
			// TODO(mdempsky): These pos details are hackish, but also
			// necessary so the variable's position is correct for DWARF
			// scope assignment later. It would probably be better for us to
			// instead just record the DWARF scoping info now so we can just
			// use obj.Pos().
			pos := clause.Pos()
			if typs := unpackListExpr(clause.Cases); len(typs) != 0 {
				pos = typeExprEndPos(typs[len(typs)-1])
			}
			w.pos(pos)

			obj := obj.(*types2.Var)
			w.typ(obj.Type())
			w.addLocal(obj)
		}

		w.stmts(clause.Body)
	}
	if len(stmt.Body) > 0 {
		w.closeScope(stmt.Rbrace)
	}

	w.closeScope(stmt.Rbrace)
}

func (w *writer) selectStmt(stmt *syntax.SelectStmt, label *syntax.Name) {
	w.sync(syncSelectStmt)
	w.optLabel(label)

	w.pos(stmt.Pos())
	w.len(len(stmt.Body))
	for i, clause := range stmt.Body {
		if i > 0 {
			w.closeScope(clause.Pos())
		}
		w.openScope(clause.Pos())

		w.pos(clause.Pos())
		w.stmt(clause.Comm)
		w.stmts(clause.Body)
	}
	if len(stmt.Body) > 0 {
		w.closeScope(stmt.Rbrace)
	}
}

func (w *writer) op(op ir.Op) {
	// TODO(mdempsky): Remove in favor of explicit codes?
	assert(op != 0)
	w.sync(syncOp)
	w.len(int(op))
}

type posObj struct {
	pos syntax.Pos
	obj types2.Object
}

func (w *writer) funcLit(expr *syntax.FuncLit) {
	tv, ok := w.p.info.Types[expr]
	assert(ok)
	sig := tv.Type.(*types2.Signature)

	w.sync(syncFuncLit)
	w.pos(expr.Pos())
	w.pos(expr.Type.Pos())
	w.signature(sig)

	closureVars, localsIdx := w.captureVars(expr)
	w.len(len(closureVars))
	for _, closureVar := range closureVars {
		w.pos(closureVar.pos)
		w.useLocal(closureVar.obj)
	}

	w.addBody(sig, expr.Body, localsIdx)
}

func (w *writer) captureVars(expr *syntax.FuncLit) (closureVars []posObj, localsIdx map[types2.Object]int) {
	scope, ok := w.p.info.Scopes[expr.Type]
	assert(ok)

	localsIdx = make(map[types2.Object]int)

	// TODO(mdempsky): Avoid repeatedly traversing nested function literals.

	var rbracePos syntax.Pos

	var visitor func(n syntax.Node) bool
	visitor = func(n syntax.Node) bool {

		// Constant expressions don't count towards capturing.
		if n, ok := n.(syntax.Expr); ok {
			if tv, ok := w.p.info.Types[n]; ok && tv.Value != nil {
				return true
			}
		}

		switch n := n.(type) {
		case *syntax.Name:
			if obj, ok := w.p.info.Uses[n].(*types2.Var); ok && !obj.IsField() && obj.Pkg() == w.p.curpkg && obj.Parent() != obj.Pkg().Scope() {
				// Found a local variable. See if it chains up to scope.
				parent := obj.Parent()
				for {
					if parent == scope {
						break
					}
					if parent == obj.Pkg().Scope() {
						if _, present := localsIdx[obj]; !present {
							pos := rbracePos
							if pos == (syntax.Pos{}) {
								pos = n.Pos()
							}

							idx := len(closureVars)
							closureVars = append(closureVars, posObj{pos, obj})
							localsIdx[obj] = idx
						}
						break
					}
					parent = parent.Parent()
				}
			}

		case *syntax.FuncLit:
			// Quirk: typecheck uses the rbrace position position of the
			// function literal as the position of the intermediary capture.
			if quirksMode() && rbracePos == (syntax.Pos{}) {
				rbracePos = n.Body.Rbrace
				syntax.Walk(n.Body, visitor)
				rbracePos = syntax.Pos{}
				return true
			}

		case *syntax.AssignStmt:
			// Quirk: typecheck visits (and thus captures) the RHS of
			// assignment statements before the LHS.
			if quirksMode() && (n.Op == 0 || n.Op == syntax.Def) {
				syntax.Walk(n.Rhs, visitor)
				syntax.Walk(n.Lhs, visitor)
				return true
			}
		case *syntax.RangeClause:
			// Quirk: Similarly, it visits the expression to be iterated
			// over before the iteration variables.
			if quirksMode() {
				syntax.Walk(n.X, visitor)
				if n.Lhs != nil {
					syntax.Walk(n.Lhs, visitor)
				}
				return true
			}
		}

		return false
	}
	syntax.Walk(expr.Body, visitor)

	return
}

func (w *writer) addBody(sig *types2.Signature, block *syntax.BlockStmt, localsIdx map[types2.Object]int) {
	w.sync(syncAddBody)
	w.reloc(relocBody, w.p.bodyIdx(w.p.curpkg, sig, block, w.tparamsIdx, localsIdx))
}

func (pw *pkgWriter) bodyIdx(pkg *types2.Package, sig *types2.Signature, block *syntax.BlockStmt, tparamsIdx map[*types2.TypeParam]int, localsIdx map[types2.Object]int) int {
	w := pw.newWriter(relocBody)
	w.curfn = sig
	w.tparamsIdx = tparamsIdx
	w.localsIdx = localsIdx

	w.funcBody(sig, block)
	return w.flush()
}

func (w *writer) funcBody(sig *types2.Signature, block *syntax.BlockStmt) {
	w.sync(syncFuncBody)
	w.funcargs(sig)
	if w.bool(block != nil) {
		w.stmts(block.List)
		w.pos(block.Rbrace)
	}
}

func (w *writer) funcargs(sig *types2.Signature) {
	do := func(params *types2.Tuple, result bool) {
		for i := 0; i < params.Len(); i++ {
			w.funcarg(params.At(i), result)
		}
	}

	if recv := sig.Recv(); recv != nil {
		w.funcarg(recv, false)
	}
	do(sig.Params(), false)
	do(sig.Results(), true)
}

func (w *writer) funcarg(param *types2.Var, result bool) {
	if param.Name() != "" || result {
		w.addLocal(param)
	}
}

func (w *writer) openScope(pos syntax.Pos) {
	w.sync(syncOpenScope)
	w.pos(pos)
}

func (w *writer) closeScope(pos syntax.Pos) {
	w.sync(syncCloseScope)
	w.pos(pos)
	w.closeAnotherScope()
}

func (w *writer) closeAnotherScope() {
	w.sync(syncCloseAnotherScope)
}

func (w *writer) rawObj(obj types2.Object) {
	assert(!isMethod(obj) || obj.Name() == "_")

	w.sync(syncObject)

	var tparamsIdx map[*types2.TypeParam]int
	if isDefinedType(obj) && !isGlobal(obj) {
		tparamsIdx = w.tparamsIdx
	}
	w.reloc(relocObj, w.p.globalIdx(obj, tparamsIdx))
}

func (pw *pkgWriter) globalIdx(obj types2.Object, tparamsIdx map[*types2.TypeParam]int) int {
	if idx, ok := pw.globalsIdx[obj]; ok {
		return idx
	}

	w := pw.newWriter(relocObj)
	w.bside = pw.newWriter(relocObjExt)
	assert(w.bside.idx == w.idx)

	pw.globalsIdx[obj] = w.idx

	w.tparamsIdx = tparamsIdx
	w.bside.tparamsIdx = tparamsIdx

	w.writeRawObj(obj)

	w.flush()
	w.bside.flush()

	return w.idx
}

func (w *writer) writeRawObj(obj types2.Object) {
	w.sync(syncObject1)

	// Sym goes first so importer can avoid unnecessary work if they've
	// already resolved this object.
	w.sym(obj)

	if obj.Pkg() != w.p.curpkg {
		w.code(objStub)
		return
	}

	switch obj := obj.(type) {
	default:
		w.p.fatalf(obj, "unexpected object: %v", obj)

	case *types2.Const:
		w.code(objConst)
		w.pos(obj.Pos())
		w.value(obj.Type(), obj.Val())

	case *types2.Func:
		decl, ok := w.p.funDecls[obj]
		assert(ok)
		sig := obj.Type().(*types2.Signature)

		// Rewrite blank methods into blank functions.
		if recv := sig.Recv(); recv != nil {
			assert(obj.Name() == "_")
			assert(sig.TParams() == nil)

			params := make([]*types2.Var, 1+sig.Params().Len())
			params[0] = recv
			for i := 0; i < sig.Params().Len(); i++ {
				params[1+i] = sig.Params().At(i)
			}
			sig = types2.NewSignature(nil, types2.NewTuple(params...), sig.Results(), sig.Variadic())
		}

		w.code(objFunc)
		w.pos(obj.Pos())
		w.typeParams(sig.TParams())
		w.signature(sig)
		w.pos(decl.Pos())
		w.ext().funcExt(obj)

	case *types2.TypeName:
		decl, ok := w.p.typDecls[obj]
		assert(ok)

		if obj.IsAlias() {
			w.code(objAlias)

			// Warn importer if this is an alias of an uninstantiated generic type.
			named, ok := obj.Type().(*types2.Named)
			w.bool(ok && len(named.TParams()) != 0 && len(named.TArgs()) == 0)

			w.pos(obj.Pos())
			w.typ(obj.Type())
			break
		}

		named := obj.Type().(*types2.Named)
		assert(named.TArgs() == nil)

		w.code(objType)
		w.pos(obj.Pos())
		w.typeParams(named.TParams())

		w.ext().typeExt(obj)
		w.typExpr(decl.Type)

		w.len(named.NumMethods())
		for i := 0; i < named.NumMethods(); i++ {
			w.method(named.Method(i))
		}

	case *types2.Var:
		w.code(objVar)
		w.pos(obj.Pos())
		w.typ(obj.Type())
		w.ext().varExt(obj)
	}
}

func (w *writer) ext() *writer {
	// TODO(mdempsky): Remove this fallback. This is only necessary
	// because of the hacks we use in decls.
	if w.bside == nil {
		assert(w.top)
		return w
	}

	return w.bside
}

func (w *writer) typeParams(tparams []*types2.TypeName) {
	w.sync(syncTypeParams)

	if len(tparams) != 0 {

		tparamsIdx := make(map[*types2.TypeParam]int)
		for k, v := range w.tparamsIdx {
			tparamsIdx[k] = v
		}
		for _, tparam := range tparams {
			tparamsIdx[tparam.Type().(*types2.TypeParam)] = len(tparamsIdx)
		}

		w.tparamsIdx = tparamsIdx
		w.bside.tparamsIdx = tparamsIdx
	}

	w.len(len(w.tparamsIdx))

	allTParams := make([]*types2.TypeName, len(w.tparamsIdx))
	for name, idx := range w.tparamsIdx {
		allTParams[idx] = name.Obj()
	}

	for _, tparam := range allTParams {
		w.pos(tparam.Pos())
		w.sym(tparam)
		w.typ(tparam.Type().(*types2.TypeParam).Bound())
	}
}

func (w *writer) varExt(obj *types2.Var) {
	w.sync(syncVarExt)
	w.linkname(obj)
}

func (w *writer) typeExt(obj *types2.TypeName) {
	decl, ok := w.p.typDecls[obj]
	assert(ok)

	w.sync(syncTypeExt)

	w.pragmaFlag(getPragma(decl.Pragma))

	w.bool(false)
}

func (w *writer) funcExt(obj *types2.Func) {
	decl, ok := w.p.funDecls[obj]
	assert(ok)

	// TODO(mdempsky): Extend these pragma validation flags to account
	// for generics.

	pragma := getPragma(decl.Pragma)
	if pragma&ir.Systemstack != 0 && pragma&ir.Nosplit != 0 {
		w.p.errorf(decl, "go:nosplit and go:systemstack cannot be combined")
	}

	if decl.Body != nil {
		if pragma&ir.Noescape != 0 {
			w.p.errorf(decl, "can only use //go:noescape with external func implementations")
		}
	} else {
		if base.Flag.Complete || decl.Name.Value == "init" {
			// Linknamed functions are allowed to have no body. Hopefully
			// the linkname target has a body. See issue 23311.
			if _, ok := w.p.linknames[obj]; !ok {
				w.p.errorf(decl, "missing function body")
			}
		}
	}

	w.sync(syncFuncExt)
	w.pragmaFlag(pragma)
	w.linkname(obj)
	w.bool(false) // raw extension
	w.addBody(obj.Type().(*types2.Signature), decl.Body, make(map[types2.Object]int))
	w.sync(syncEOF)
}

func (w *writer) linkname(obj types2.Object) {
	w.sync(syncLinkname)
	w.string(w.p.linknames[obj])
	w.bool(false)
}

func (w *writer) method(meth *types2.Func) {
	decl, ok := w.p.funDecls[meth]
	assert(ok)
	sig := meth.Type().(*types2.Signature)

	// Workaround for #45935.
	base := recvBase(sig)
	assert(len(base.TArgs()) == len(base.TParams()))
	targs := base.TArgs()
	for i, tparam := range base.TParams() {
		w.p.dups.add(targs[i], tparam.Type())
	}

	w.sync(syncMethod)
	w.pos(meth.Pos())
	w.selector(meth)
	w.param(sig.Recv())
	w.signature(sig)

	w.pos(decl.Pos())
	w.ext().funcExt(meth)
}

// typ writes the given type.
func (w *writer) typ(typ types2.Type) {
	w.sync(syncType)

	typ = w.p.dups.orig(typ)

	if w.bool(len(w.tparamsIdx) != 0) {
		w.doTyp(typ)
		return
	}

	w.reloc(relocType, w.p.typIdx(typ))
}

func (pw *pkgWriter) typIdx(typ types2.Type) int {
	if idx, ok := pw.typsIdx[typ]; ok {
		return idx
	}

	w := pw.newWriter(relocType)
	pw.typsIdx[typ] = w.idx

	w.doTyp(typ)
	return w.flush()
}

// typExpr writes the type represented by the given expression.
func (w *writer) typExpr(expr syntax.Expr) {
	tv, ok := w.p.info.Types[expr]
	assert(ok)
	assert(tv.IsType())
	w.typ(tv.Type)
}

func (w *writer) doTyp(typ types2.Type) {
	w.sync(syncTypeIdx)

	switch typ := typ.(type) {
	case *types2.Basic:
		w.code(typeBasic)
		// TODO(mdempsky): This is a gross hack, which should go away once
		// we use predeclared types.
		kind := typ.Kind()
		switch typ.Name() {
		case "byte":
			kind = 100
		case "rune":
			kind = 101
		}
		w.uint64(uint64(kind))

	case *types2.Named:
		// Apparently type aliases can refer to uninstantiated generic types.
		assert(len(typ.TParams()) == len(typ.TArgs()) || len(typ.TArgs()) == 0)

		switch typ {
		case errorType:
			w.code(typeBasic)
			w.uint64(400)
			return
		case comparableType:
			w.code(typeBasic)
			w.uint64(401)
			return
		}

		orig := typ
		for orig.TArgs() != nil {
			orig = orig.Orig()
		}

		w.code(typeNamed)
		w.useObj(orig.Obj(), typ.TArgs())

	case *types2.TypeParam:
		idx, ok := w.tparamsIdx[typ]
		assert(ok)
		w.code(typeTypeParam)
		w.len(idx)

	case *types2.Array:
		w.code(typeArray)
		w.uint64(uint64(typ.Len()))
		w.typ(typ.Elem())

	case *types2.Chan:
		w.code(typeChan)
		w.uint64(uint64(typ.Dir()))
		w.typ(typ.Elem())

	case *types2.Map:
		w.code(typeMap)
		w.typ(typ.Key())
		w.typ(typ.Elem())

	case *types2.Pointer:
		w.code(typePointer)
		w.typ(typ.Elem())

	case *types2.Signature:
		assert(typ.TParams() == nil)
		w.code(typeSignature)
		w.typPkg(typ)
		w.signature(typ)

	case *types2.Slice:
		w.code(typeSlice)
		w.typ(typ.Elem())

	case *types2.Struct:
		w.code(typeStruct)
		w.structType(typ)

	case *types2.Interface:
		switch typ {
		case errorUnderlyingType:
			w.code(typeBasic)
			w.uint64(200)
			return
		case comparableUnderlyingType:
			w.code(typeBasic)
			w.uint64(201)
			return
		}

		w.code(typeInterface)
		w.interfaceType(typ)

	case *types2.Union:
		w.code(typeUnion)
		w.len(typ.NumTerms())
		for i := 0; i < typ.NumTerms(); i++ {
			term, tilde := typ.Term(i)
			w.typ(term)
			w.bool(tilde)
		}

	default:
		base.FatalfAt(src.NoXPos, "unhandled type: %v (%T)", typ, typ)
		panic("unreachable")
	}
}

func (w *writer) structType(typ *types2.Struct) {
	w.typPkg(typ)
	w.len(typ.NumFields())
	for i := 0; i < typ.NumFields(); i++ {
		f := typ.Field(i)
		w.pos(f.Pos())
		w.selector(f)
		w.typ(f.Type())
		w.string(typ.Tag(i))
		w.bool(f.Embedded())
	}
}

func (w *writer) interfaceType(typ *types2.Interface) {
	w.typPkg(typ)

	w.len(typ.NumExplicitMethods())
	w.len(typ.NumEmbeddeds())

	for i := 0; i < typ.NumExplicitMethods(); i++ {
		m := typ.ExplicitMethod(i)
		sig := m.Type().(*types2.Signature)
		assert(sig.TParams() == nil)

		pos := m.Pos()
		w.pos(pos)
		w.selector(m)
		w.signature(sig)
	}

	for i := 0; i < typ.NumEmbeddeds(); i++ {
		w.typ(typ.EmbeddedType(i))
	}
}

func (w *writer) signature(sig *types2.Signature) {
	w.sync(syncSignature)
	w.params(sig.Params())
	w.params(sig.Results())
	w.bool(sig.Variadic())
}

func (w *writer) params(typ *types2.Tuple) {
	w.sync(syncParams)
	w.len(typ.Len())
	for i := 0; i < typ.Len(); i++ {
		w.param(typ.At(i))
	}
}

func (w *writer) param(param *types2.Var) {
	w.sync(syncParam)
	w.pos(param.Pos())
	w.sym(param)
	w.typ(param.Type())
}

var (
	errorType      = types2.Universe.Lookup("error").(*types2.TypeName).Type().(*types2.Named)
	comparableType = types2.Universe.Lookup("comparable").(*types2.TypeName).Type().(*types2.Named)

	errorUnderlyingType      = errorType.Underlying().(*types2.Interface)
	comparableUnderlyingType = comparableType.Underlying().(*types2.Interface)
)

func (w *writer) typPkg(typ types2.Type) {
	w.sync(syncTypePkg)

	pkg := w.p.curpkg
	obj := anyObj(typ)
	if obj != nil {
		pkg = obj.Pkg()
	}
	// Tihs is a change I made since the last gotry run.
	if pkg == nil {
		w.p.fatalf(syntax.Pos{}, "why is pkg nil for %v (%v)", typ, obj)
	}
	w.pkg(pkg)
}

func isGlobal(obj types2.Object) bool {
	// XXX: This isn't able to distinguish blank objects declared at
	// package vs function scope.
	if obj.Pkg() == nil {
		return obj.Parent() == types2.Universe
	}
	return obj.Parent() == obj.Pkg().Scope() || isMethod(obj)
}

func isDefinedType(obj types2.Object) bool {
	if obj, ok := obj.(*types2.TypeName); ok {
		return !obj.IsAlias()
	}
	return false
}

func isMethod(obj types2.Object) bool {
	if obj, ok := obj.(*types2.Func); ok {
		return obj.Type().(*types2.Signature).Recv() != nil
	}
	return false
}

func recvBase(sig *types2.Signature) *types2.Named {
	typ := sig.Recv().Type()
	if ptr, ok := typ.(*types2.Pointer); ok {
		typ = ptr.Elem()
	}
	return typ.(*types2.Named)
}
