// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package noder

import (
	"bytes"
	"errors"
	"fmt"
	"go/constant"
	"io"
	"io/ioutil"
	"strconv"
	"strings"

	"cmd/compile/internal/base"
	"cmd/compile/internal/importer"
	"cmd/compile/internal/ir"
	"cmd/compile/internal/syntax"
	"cmd/compile/internal/typecheck"
	"cmd/compile/internal/types"
	"cmd/compile/internal/types2"
	"cmd/internal/archive"
	"cmd/internal/bio"
	"cmd/internal/goobj"
	"cmd/internal/objabi"
	"cmd/internal/src"
)

func WriteExportData(out io.Writer) {
	var old, new bytes.Buffer
	typecheck.WriteExports(&old)

	if !quirksMode() {
		writeNewExport(&new)
	}

	oldsize := old.Len()
	newsize := new.Len()

	if !quirksMode() {
		fmt.Fprintf(out, "\nexportsizes %v %v\n", oldsize, newsize)
	}

	// The linker also looks for the $$ marker - use char after $$ to distinguish format.
	io.WriteString(out, "\n$$B\n") // indicate binary export format
	io.Copy(out, &old)
	io.WriteString(out, "\n$$\n")
	io.Copy(out, &new)

	if base.Debug.Export != 0 {
		fmt.Printf("BenchmarkExportSize:%s 1 %d bytes\n", base.Ctxt.Pkgpath, oldsize)
		if !quirksMode() {
			fmt.Printf("BenchmarkNewExportSize:%s 1 %d bytes\n", base.Ctxt.Pkgpath, newsize)
		}
	}
}

// Temporary import helper to get type2-based type-checking going.
type importer2 struct {
	packages map[string]*types2.Package
	checker  *types2.Checker
}

func (m *importer2) Import(path string) (*types2.Package, error) {
	return m.ImportFrom(path, "" /* no vendoring */, 0)
}

func (m *importer2) ImportFrom(path, srcDir string, mode types2.ImportMode) (pkg *types2.Package, err error) {
	if mode != 0 {
		panic("mode must be 0")
	}

	path, err = resolveImportPath(path)
	if err != nil {
		return nil, err
	}

	importpkg := types.NewPkg(path, "")
	importpkg.Direct = true

	// With custom lookup specified, assume that caller has
	// converted path to a canonical import path for use in the map.
	if path == "unsafe" {
		return types2.Unsafe, nil
	}

	// No need to re-import if the package was imported completely before.
	if pkg = m.packages[path]; pkg != nil && pkg.Complete() {
		return
	}

	f, err := openPackage(path)
	if err != nil {
		return nil, err
	}
	r := bio.NewReader(f)
	defer r.Close()
	file := f.Name()

	if base.Debug.Export != 0 {
		fmt.Printf("importing %s (%s)\n", path, file)
	}

	// Imports are always archive files.
	line, err := r.ReadString('\n')
	if err != nil {
		return nil, fmt.Errorf("reading input: %v", err)
	}
	if line != "!<arch>\n" {
		return nil, errors.New("not an archive file")
	}

	// Package definition file should be first within the archive.
	sz := int64(archive.ReadHeader(r.Reader, "__.PKGDEF"))
	if sz <= 0 {
		return nil, errors.New("not a package file")
	}
	start := r.Offset()
	line, err = r.ReadString('\n')
	if err != nil {
		return nil, fmt.Errorf("reading input: %v", err)
	}

	if !strings.HasPrefix(line, "go object ") {
		return nil, errors.New("not a Go object file")
	}
	if expect := objabi.HeaderString(); line != expect {
		return nil, fmt.Errorf("object is [%s] expected [%s]", line, expect)
	}

	// Skip over object header to export data.
	// Begins after first line starting with $$.
	var oldsize, newsize int64 = -1, -1
	for !strings.HasPrefix(line, "$$") {
		if strings.HasPrefix(line, "exportsizes ") {
			assert(!quirksMode())

			fields := strings.Fields(line)
			oldsize, err = strconv.ParseInt(fields[1], 10, 64)
			if err != nil {
				return nil, fmt.Errorf("old size: %v", err)
			}
			newsize, err = strconv.ParseInt(fields[2], 10, 64)
			if err != nil {
				return nil, fmt.Errorf("new size: %v", err)
			}
		}

		if line, err = r.ReadString('\n'); err != nil {
			return nil, fmt.Errorf("reading input: %v", err)
		}
	}
	if line != "$$B\n" {
		return nil, errors.New("old export format no longer supported (recompile library)")
	}

	pos := r.Offset()
	end := start + sz

	// Indexed format is distinguished by an 'i' byte,
	// whereas previous export formats started with 'c', 'd', or 'v'.
	c, err := r.ReadByte()
	if err != nil {
		return nil, fmt.Errorf("reading input: %v", err)
	}
	if c != 'i' {
		return nil, fmt.Errorf("unexpected package format byte: %v", c)
	}

	if quirksMode() {
		oldsize = (end - 4) - pos
		newsize = 0
	}

	olddata, err := ioutil.ReadAll(io.NewSectionReader(r.File(), pos, oldsize))
	if err != nil {
		return nil, fmt.Errorf("reading old data: %v", err)
	}
	newdata, err := ioutil.ReadAll(io.NewSectionReader(r.File(), end-newsize, newsize))
	if err != nil {
		return nil, fmt.Errorf("reading new data: %v", err)
	}

	pkg, err = m.readNewExport(importpkg, r, olddata, string(newdata))
	if err != nil {
		return
	}

	var fingerprint goobj.FingerprintType
	copy(fingerprint[:], olddata[len(olddata)-len(fingerprint):])

	// assume files move (get installed) so don't record the full path
	if base.Flag.Cfg.PackageFile != nil {
		// If using a packageFile map, assume path_ can be recorded directly.
		base.Ctxt.AddImport(path, fingerprint)
	} else {
		// For file "/Users/foo/go/pkg/darwin_amd64/math.a" record "math.a".
		base.Ctxt.AddImport(file[len(file)-len(path)-len(".a"):], fingerprint)
	}

	return
}

func (m *importer2) readNewExport(importpkg *types.Pkg, r *bio.Reader, olddata []byte, newdata string) (pkg *types2.Package, err error) {

	// In quirks mode, just use the legacy importers.
	if quirksMode() {
		_, pkg, err = importer.ImportData(m.packages, olddata[1:], importpkg.Path)
		if err == nil {
			typecheck.ReadImports(importpkg, r)
		}
		return
	}

	pr0 := pkgDecoder{pkgPath: importpkg.Path}
	pr0.init(newdata)

	pkg = m.addPayload(pr0)

	pr := newPkgReader(pr0, importpkg)

	{
		r := pr.newReader(relocMeta, publicRootIdx)
		r.curpkg = importpkg // XXX
		r.sync(syncPublic)

		pkg := r.pkg()

		if r.bool() {
			sym := pkg.Lookup(".inittask")
			task := ir.NewNameAt(src.NoXPos, sym)
			task.Class = ir.PEXTERN
			sym.Def = task
		}

		for i, n := 0, r.len(); i < n; i++ {
			r.doObj(nil, false)
		}
	}

	return
}

type pkgReader2 struct {
	pkgDecoder

	m *importer2

	posBases []*syntax.PosBase
	pkgs     []*types2.Package
	typs     []types2.Type
}

type reader2 struct {
	decoder
	p *pkgReader2

	tparams []*types2.TypeName
}

func (pr *pkgReader2) newReader(k reloc, idx int) *reader2 {
	return &reader2{
		decoder: pr.newDecoder(k, idx),
		p:       pr,
	}
}

func (m *importer2) addPayload(pr0 pkgDecoder) *types2.Package {
	pr := pkgReader2{
		pkgDecoder: pr0,
		m:          m,
	}

	pr.posBases = make([]*syntax.PosBase, pr.numElems(relocPosBase))
	pr.pkgs = make([]*types2.Package, pr.numElems(relocPkg))
	pr.typs = make([]types2.Type, pr.numElems(relocType))

	r := pr.newReader(relocMeta, publicRootIdx)
	r.sync(syncPublic)
	pkg := r.pkg()
	r.bool() // has init

	for i, n := 0, r.len(); i < n; i++ {
		r.sync(syncObject)
		pr.doObj(r.reloc(relocObj))
	}

	r.sync(syncEOF)

	pkg.MarkComplete()
	return pkg
}

func (pr *pkgReader2) doObj(idx int) (*types2.Package, string) {
	r := pr.newReader(relocObj, idx)
	r.sync(syncObject1)
	objPkg, objName := r.sym()
	assert(objName != "")

	tag := codeObj(r.code(syncCodeObj))
	if tag == objStub {
		assert(objPkg == nil)
		return objPkg, objName
	}

	objPkg.Scope().InsertLazy(objName, func() types2.Object {
		switch tag {
		default:
			panic("weird")

		case objAlias:
			_ = r.bool() // alias of uninstantiated type
			pos := r.pos()
			typ := r.typ()
			return types2.NewTypeName(pos, objPkg, objName, typ)

		case objConst:
			pos := r.pos()
			typ, val := r.value()
			return types2.NewConst(pos, objPkg, objName, typ, val)

		case objFunc:
			pos := r.pos()
			r.typeParams()
			sig := r.signature(objPkg, nil)
			sig.SetTParams(r.tparams)
			return types2.NewFunc(pos, objPkg, objName, sig)

		case objType:
			pos := r.pos()

			return types2.NewTypeNameLazy(pos, objPkg, objName, func(named *types2.Named) (tparams []*types2.TypeName, underlying types2.Type, methods []*types2.Func) {
				// TODO(mdempsky): Revisit how/when to handle type parameters
				// after golang.org/issue/46461 is resolved.
				tparams = r.typeParams()

				// TODO(mdempsky): Rewrite receiver types to underlying is an
				// Interface? The go/types importer does this (I think because
				// unit tests expected that), but cmd/compile doesn't care
				// about it, so maybe we can avoid worrying about that here.
				underlying = r.typ().Underlying()

				methods = make([]*types2.Func, r.len())
				for i := range methods {
					methods[i] = r.method(objPkg)
				}

				return
			})

		case objVar:
			pos := r.pos()
			typ := r.typ()
			return types2.NewVar(pos, objPkg, objName, typ)
		}
	})

	return objPkg, objName
}

func (r *reader2) typeParams() []*types2.TypeName {
	r.sync(syncTypeParams)
	tparams := make([]*types2.TypeName, r.len())
	if len(tparams) == 0 {
		return nil
	}
	r.tparams = tparams
	for i := range tparams {
		pos := r.pos()
		pkg, name := r.sym()
		bound := r.typ()

		obj := types2.NewTypeName(pos, pkg, name, nil)
		r.p.m.checker.NewTypeParam(obj, i, bound)
		tparams[i] = obj
	}
	return tparams
}

func (r *reader2) value() (types2.Type, constant.Value) {
	r.sync(syncValue)
	return r.typ(), r.rawValue()
}

func (r *reader2) method(tpkg *types2.Package) *types2.Func {
	r.sync(syncMethod)
	pos := r.pos()
	name := r.selector()
	recv := r.param(tpkg)

	// TODO(mdempsky): Here we're simply reusing the receiver type's
	// type parameters for the method receiver. This appears to work for
	// types2, but we should probably write out the original parameters
	// more properly.
	sig := r.signature(tpkg, recv)
	sig.SetRParams(r.tparams)

	_ = r.pos() // XXX: Get rid of.
	return types2.NewFunc(pos, tpkg, name, sig)
}

func (r *reader2) pos() syntax.Pos {
	r.sync(syncPos)
	if !r.bool() {
		return syntax.Pos{}
	}

	// TODO(mdempsky): Delta encoding.
	posBase := r.posBase()
	line := r.uint()
	col := r.uint()
	return syntax.MakePos(posBase, line, col)
}

func (r *reader2) posBase() *syntax.PosBase {
	return r.p.posBaseIdx(r.reloc(relocPosBase))
}

func (pr *pkgReader2) posBaseIdx(idx int) *syntax.PosBase {
	if b := pr.posBases[idx]; b != nil {
		return b
	}

	r := pr.newReader(relocPosBase, idx)

	var b *syntax.PosBase
	filename := r.string()
	if r.bool() {
		b = syntax.NewFileBase(filename)
	} else {
		pos := r.pos()
		line := r.uint()
		col := r.uint()
		b = syntax.NewLineBase(pos, filename, line, col)
	}

	pr.posBases[idx] = b
	return b
}

func (r *reader2) sym() (pkg *types2.Package, name string) {
	r.sync(syncSym)
	name = r.string()
	if name != "" {
		pkg = r.pkg()
	}
	return
}

func (r *reader2) selector() string {
	r.sync(syncSelector)
	name := r.string()
	if !types.IsExported(name) {
		r.pkg() // XXX: Use or validate somehow.
	}
	return name
}

func (r *reader2) pkg() *types2.Package {
	r.sync(syncPkg)
	return r.p.pkgIdx(r.reloc(relocPkg))
}

func (pr *pkgReader2) pkgIdx(idx int) *types2.Package {
	if pkg := pr.pkgs[idx]; pkg != nil {
		return pkg
	}

	var pkg *types2.Package

	r := pr.newReader(relocPkg, idx)
	r.sync(syncPkgDef)
	path := r.string()

	// TODO(mdempsky): Probably better to not need this.
	if path == "builtin" {
		return nil // universe
	}

	if path == "" {
		path = pr.pkgPath
	}

	pkg = pr.m.packages[path]
	if pkg == nil {
		name := r.string()
		height := r.len()

		pkg = types2.NewPackageHeight(path, name, height)
		pr.m.packages[path] = pkg

		// TODO(mdempsky): The list of imported packages is important for
		// go/types, but we could probably skip it for types2.
		imps := make([]*types2.Package, r.len())
		for i := range imps {
			imps[i] = r.pkg()
		}
		pkg.SetImports(imps)
	}

	pr.pkgs[idx] = pkg
	return pkg
}

func (r *reader2) typ() types2.Type {
	r.sync(syncType)

	if r.bool() {
		assert(len(r.tparams) != 0)
		return r.doTyp()
	}

	return r.p.typIdx(r.reloc(relocType))
}

func (pr *pkgReader2) typIdx(idx int) types2.Type {
	if pr.typs[idx] != nil {
		return pr.typs[idx]
	}

	r := pr.newReader(relocType, idx)

	typ := r.doTyp()
	assert(typ != nil)

	if r.p.typs[idx] != nil {
		return r.p.typs[idx]
	}
	r.p.typs[idx] = typ

	return typ
}

var (
	byteTypeName       = types2.Universe.Lookup("byte").(*types2.TypeName)
	runeTypeName       = types2.Universe.Lookup("rune").(*types2.TypeName)
	errorTypeName      = types2.Universe.Lookup("error").(*types2.TypeName)
	comparableTypeName = types2.Universe.Lookup("comparable").(*types2.TypeName)
)

func (r *reader2) doTyp() (res types2.Type) {
	r.sync(syncTypeIdx)

	switch tag := codeType(r.code(syncType)); tag {
	default:
		base.FatalfAt(src.NoXPos, "unhandled type tag: %v", tag)
		panic("unreachable")

	case typeBasic:
		switch kind := r.uint64(); kind {
		case 100:
			return byteTypeName.Type()
		case 101:
			return runeTypeName.Type()
		case 200:
			return errorTypeName.Type().Underlying()
		case 201:
			return comparableTypeName.Type().Underlying()
		case 400:
			return errorTypeName.Type()
		case 401:
			return comparableTypeName.Type()
		default:
			return types2.Typ[kind]
		}

	case typeNamed:
		r.sync(syncUseObj)

		targs := make([]types2.Type, r.len())
		for i := range targs {
			targs[i] = r.typ()
		}

		// doObj
		r.sync(syncObject)
		pkg, name := r.p.doObj(r.reloc(relocObj))

		obj := pkg.Scope().Lookup(name).(*types2.TypeName)

		if len(targs) == 0 {
			return obj.Type().(*types2.Named)
		}

		return types2.InstantiateLazy(r.p.m.checker, obj, targs)

	case typeTypeParam:
		idx := r.len()
		return r.tparams[idx].Type().(*types2.TypeParam)

	case typeArray:
		len := int64(r.uint64())
		elem := r.typ()
		return types2.NewArray(elem, len)
	case typeChan:
		dir := types2.ChanDir(r.uint64())
		elem := r.typ()
		return types2.NewChan(dir, elem)
	case typeMap:
		key := r.typ()
		elem := r.typ()
		return types2.NewMap(key, elem)
	case typePointer:
		elem := r.typ()
		return types2.NewPointer(elem)
	case typeSignature:
		tpkg := r.tpkg()
		return r.signature(tpkg, nil)
	case typeSlice:
		elem := r.typ()
		return types2.NewSlice(elem)

	case typeStruct:
		tpkg := r.tpkg()
		fields := make([]*types2.Var, r.len())
		var tags []string
		for i := range fields {
			pos := r.pos()
			sym := r.selector()
			ftyp := r.typ()
			tag := r.string()
			embedded := r.bool()

			fields[i] = types2.NewField(pos, tpkg, sym, ftyp, embedded)
			if tag != "" {
				for len(tags) < i {
					tags = append(tags, "")
				}
				tags = append(tags, tag)
			}
		}
		return types2.NewStruct(fields, tags)

	case typeInterface:
		tpkg := r.tpkg()
		methods := make([]*types2.Func, r.len())
		embeddeds := make([]types2.Type, r.len())

		for i := range methods {
			pos := r.pos()
			sym := r.selector()
			mtyp := r.signature(tpkg, nil)
			methods[i] = types2.NewFunc(pos, tpkg, sym, mtyp)
		}

		for i := range embeddeds {
			embeddeds[i] = r.typ()
		}

		typ := types2.NewInterfaceType(methods, embeddeds)
		typ.Complete()
		return typ

	case typeUnion:
		terms := make([]types2.Type, r.len())
		tildes := make([]bool, len(terms))
		for i := range terms {
			terms[i] = r.typ()
			tildes[i] = r.bool()
		}
		return types2.NewUnion(terms, tildes)
	}
}

func (r *reader2) signature(tpkg *types2.Package, recv *types2.Var) *types2.Signature {
	r.sync(syncSignature)

	params := r.params(tpkg)
	results := r.params(tpkg)
	variadic := r.bool()

	return types2.NewSignature(recv, params, results, variadic)
}

func (r *reader2) params(tpkg *types2.Package) *types2.Tuple {
	r.sync(syncParams)
	params := make([]*types2.Var, r.len())
	for i := range params {
		params[i] = r.param(tpkg)
	}
	return types2.NewTuple(params...)
}

func (r *reader2) param(tpkg *types2.Package) *types2.Var {
	r.sync(syncParam)

	pos := r.pos()
	_, name := r.sym()
	typ := r.typ()

	return types2.NewParam(pos, tpkg, name, typ)
}

func (r *reader2) tpkg() *types2.Package {
	r.sync(syncTypePkg)
	return r.pkg()
}
