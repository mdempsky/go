package escschema

type Package struct {
	Tool   string   `json:"tool"`  // creator; e.g., "cmd/compile 1.14"
	Files  []string `json:"files"` // source file paths
	Graphs []Graph  `json:"graphs"`
}

type Pos struct {
	File   int `json:"file"`   // index into Top.Files
	Line   int `json:"line"`   // starting at 1
	Column int `json:"column"` // starting at 1 (byte count)
}

type Graph struct {
	Funcs []Func `json:"funcs"`
	Nodes []Node `json:"nodes"`
}

type Func struct {
	Pos     Pos    `json:"pos"`
	Name    string `json:"name"`    // linker name of function
	Params  []int  `json:"params"`  // indices into Graph.Nodes
	Results []int  `json:"results"` // indices into Graph.Nodes
}

type Node struct {
	Pos      Pos    `json:"pos"`
	Name     string `json:"name"` // user friendly description; not necessarily unique
	Func     int    `json:"func"` // index into Graph.Funcs
	Incoming []Edge `json:"incoming"`

	LoopDepth int  `json:"loopDepth"`
	Escapes   bool `json:"escapes"`
	Transient bool `json:"transient"`

	// ParamEsc summarizes the shortest dereference path from the
	// Node to the heap (ParamEsc[0]) or result parameter i
	// (ParamEsc[i]). -1 indicates no assignment path.
	ParamEsc []int `json:"paramEsc"`
}

type Edge struct {
	Pos    Pos    `json:"pos"`
	Why    string `json:"why"`    // compiler explanation for this edge
	Source int    `json:"source"` // index into Graph.Nodes

	Derefs int `json:"derefs"` // >= -1
}
