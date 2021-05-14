// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package noder

type reloc int

type relocEnt struct {
	kind reloc
	idx  int
}

const (
	publicRootIdx  = 0
	privateRootIdx = 1
)

const (
	relocString reloc = iota
	relocMeta
	relocPosBase
	relocPkg
	relocType
	relocObj
	relocObjExt
	relocBody

	numRelocs = iota
)
