// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package noder

import (
	"cmd/compile/internal/typecheck"
	"cmd/compile/internal/types"
	"strings"
)

func doPkgBits(noders []*noder) {
	var sb strings.Builder
	writePkgBits(&sb, noders)
	data := sb.String()

	// TODO(mdempsky): At this point, we're done with types2. Check that
	// we're not still keeping it alive somehow (e.g., finalizers).

	pr0 := pkgDecoder{pkgPath: types.LocalPkg.Path}
	pr0.init(data)
	readPkgBits(pr0, types.LocalPkg, typecheck.Target)
}
