// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package noder

import (
	"io"
	"sort"

	"cmd/compile/internal/base"
	"cmd/compile/internal/ir"
	"cmd/compile/internal/typecheck"
	"cmd/compile/internal/types"
	"cmd/internal/goobj"
)

func (pr *pkgDecoder) peekPkgPath(idx int) string {
	r := pr.newDecoder(relocPkg, idx)
	r.sync(syncPkgDef)
	path := r.string()
	if path == "" {
		path = pr.pkgPath
	}
	return path
}

func (pr *pkgDecoder) peekObj(idx int) (string, string, codeObj) {
	r := pr.newDecoder(relocObj, idx)
	r.sync(syncObject1)
	r.sync(syncSym)
	name := r.string()
	assert(name != "")
	r.sync(syncPkg)
	path := pr.peekPkgPath(r.reloc(relocPkg))
	tag := codeObj(r.code(syncCodeObj))

	return path, name, tag
}

func writeNewExport(out io.Writer) {
	l := linker{
		pw: newPkgEncoder(),

		pkgs:  make(map[string]int),
		decls: make(map[*types.Sym]int),
	}

	publicRootWriter := l.pw.newEncoder(relocMeta)
	assert(publicRootWriter.idx == publicRootIdx)

	var selfPkgIdx int

	{
		pr := importData[""]
		r := pr.newDecoder(relocMeta, publicRootIdx)
		r.sync(syncPublic)

		r.sync(syncPkg)
		selfPkgIdx = l.relocIdx(pr, relocPkg, r.reloc(relocPkg))

		r.bool() // has init

		for i, n := 0, r.len(); i < n; i++ {
			r.sync(syncObject)
			idx := r.reloc(relocObj)

			xpath, xname, xtag := pr.peekObj(idx)
			assert(xpath == pr.pkgPath)
			assert(xtag != objStub)

			if types.IsExported(xname) {
				l.relocIdx(pr, relocObj, idx)
			}
		}

		r.sync(syncEOF)
	}

	{
		var idxs []int
		for _, idx := range l.decls {
			idxs = append(idxs, idx)
		}
		sort.Ints(idxs)

		w := publicRootWriter
		w.sync(syncPublic)

		w.sync(syncPkg)
		w.reloc(relocPkg, selfPkgIdx)

		w.bool(typecheck.Lookup(".inittask").Def != nil)

		w.len(len(idxs))
		for _, idx := range idxs {
			w.sync(syncObject)
			w.reloc(relocObj, idx)
		}

		w.sync(syncEOF)
		w.flush()
	}

	l.pw.dump(out)
}

type linker struct {
	pw pkgEncoder

	pkgs  map[string]int
	decls map[*types.Sym]int
}

func (l *linker) relocAll(pr *pkgReader, relocs []relocEnt) []relocEnt {
	// TODO(mdempsky): It's probably safe to rewrite the relocs slice in
	// place, but for now I'm copying it to be safe.
	res := make([]relocEnt, len(relocs))
	for i, rent := range relocs {
		rent.idx = l.relocIdx(pr, rent.kind, rent.idx)
		res[i] = rent
	}
	return res
}

func (l *linker) relocIdx(pr *pkgReader, k reloc, idx int) int {
	assert(pr != nil)

	absIdx := pr.absIdx(k, idx)

	if newidx := pr.newindex[absIdx]; newidx != 0 {
		return newidx - 1e6
	}

	var newidx int
	switch k {
	case relocString:
		newidx = l.relocString(pr, idx)
	case relocPkg:
		newidx = l.relocPkg(pr, idx)
	case relocObj:
		newidx = l.relocObj(pr, idx)
	default:
		// Generic.
		w := l.pw.newEncoder(k)
		l.relocCommon(pr, &w, k, idx)
		newidx = w.idx
	}

	pr.newindex[absIdx] = newidx + 1e6

	return newidx
}

func (l *linker) relocString(pr *pkgReader, idx int) int {
	return l.pw.stringIdx(pr.stringIdx(idx))
}

func (l *linker) relocPkg(pr *pkgReader, idx int) int {
	path := pr.peekPkgPath(idx)

	if newidx, ok := l.pkgs[path]; ok {
		return newidx
	}

	r := pr.newDecoder(relocPkg, idx)
	r.sync(syncPkgDef)

	w := l.pw.newEncoder(relocPkg)
	l.pkgs[path] = w.idx
	w.sync(syncPkgDef)

	w.relocs = l.relocAll(pr, r.relocs)

	_ = r.string() // original path
	w.string(path)

	io.Copy(&w.data, &r.data)

	return w.flush()
}

func (l *linker) relocObj(pr *pkgReader, idx int) int {
	path, name, tag := pr.peekObj(idx)
	sym := types.NewPkg(path, "").Lookup(name)

	if newidx, ok := l.decls[sym]; ok {
		return newidx
	}

	if tag == objStub && path != "builtin" {
		x, ok := objBits[sym]
		if !ok {
			base.Fatalf("missing source for %q.%v\n\thave %v", path, name, objBits)
		}
		assert(ok)

		pr = x.pr
		idx = x.idx

		path2, name2, tag2 := pr.peekObj(idx)
		sym2 := types.NewPkg(path2, "").Lookup(name2)
		assert(sym == sym2)
		assert(tag2 != objStub)
	}

	// TODO(mdempsky): Handle rewriting extension data.

	w := l.pw.newEncoder(relocObj)
	bside := l.pw.newEncoder(relocObjExt)
	assert(bside.idx == w.idx)
	l.decls[sym] = w.idx

	l.relocCommon(pr, &w, relocObj, idx)

	var obj *ir.Name
	if path == "" {
		var ok bool
		obj, ok = sym.Def.(*ir.Name)

		// Generic types and functions won't have definitions.
		// For now, just generically copy their extension data.
		if !ok && base.Flag.G == 0 {
			base.Fatalf("missing definition for %v", sym)
		}
	}

	if obj != nil {
		switch tag {
		case objFunc:
			l.relocFuncExt(&bside, obj)
		case objType:
			l.relocTypeExt(&bside, obj)
		case objVar:
			l.relocVarExt(&bside, obj)
		}
		bside.flush()
	} else {
		l.relocCommon(pr, &bside, relocObjExt, idx)
	}

	return w.idx
}

func (l *linker) relocCommon(pr *pkgReader, w *encoder, k reloc, idx int) {
	r := pr.newDecoder(k, idx)
	w.relocs = l.relocAll(pr, r.relocs)
	io.Copy(&w.data, &r.data)
	w.flush()
}

func (l *linker) pragmaFlag(w *encoder, pragma ir.PragmaFlag) {
	w.sync(syncPragma)
	w.int(int(pragma))
}

func (l *linker) relocFuncExt(w *encoder, name *ir.Name) {
	w.sync(syncFuncExt)

	l.pragmaFlag(w, name.Func.Pragma)
	l.linkname(w, name.Sym())

	// Relocated extension data.
	w.bool(true)

	// Record definition ABI so cross-ABI calls can be direct.
	// This is important for the performance of calling some
	// common functions implemented in assembly (e.g., bytealg).
	w.uint64(uint64(name.Func.ABI))

	// Escape analysis.
	for _, fs := range &types.RecvsParams {
		for _, f := range fs(name.Type()).FieldSlice() {
			w.string(f.Note)
		}
	}

	if inl := name.Func.Inl; w.bool(inl != nil) {
		w.len(int(inl.Cost))
		w.bool(inl.CanDelayResults)

		bi, ok := bodyIndex[name.Func]
		assert(ok)
		w.sync(syncAddBody)
		w.reloc(relocBody, l.relocIdx(bi.pr, relocBody, bi.idx))
	}

	w.sync(syncEOF)
}

func (l *linker) relocTypeExt(w *encoder, name *ir.Name) {
	w.sync(syncTypeExt)

	typ := name.Type()

	l.pragmaFlag(w, name.Pragma())

	// For type T, export the index of type descriptor symbols of T and *T.
	w.bool(true)
	if i, ok := typecheck.TypeSymIdx[typ]; ok {
		w.int64(i[0])
		w.int64(i[1])
	} else {
		l.symIdx(w, types.TypeSym(typ))
		l.symIdx(w, types.TypeSym(typ.PtrTo()))
	}

	if typ.Kind() != types.TINTER {
		for _, method := range typ.Methods().Slice() {
			l.relocFuncExt(w, method.Nname.(*ir.Name))
		}
	}
}

func (l *linker) relocVarExt(w *encoder, name *ir.Name) {
	w.sync(syncVarExt)
	l.linkname(w, name.Sym())
	l.symIdx(w, name.Sym())
}

func (l *linker) linkname(w *encoder, s *types.Sym) {
	w.sync(syncLinkname)
	w.string(s.Linkname)
	w.bool(true)
	l.symIdx(w, s)
}

func (l *linker) symIdx(w *encoder, s *types.Sym) {
	lsym := s.Linksym()
	if lsym.PkgIdx > goobj.PkgIdxSelf || (lsym.PkgIdx == goobj.PkgIdxInvalid && !lsym.Indexed()) || s.Linkname != "" {
		// Don't export index for non-package symbols, linkname'd symbols,
		// and symbols without an index. They can only be referenced by
		// name.
		w.int64(-1)
	} else {
		// For a defined symbol, export its index.
		// For re-exporting an imported symbol, pass its index through.
		w.int64(int64(lsym.SymIdx))
	}
}
