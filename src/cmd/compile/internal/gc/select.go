// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import "fmt"

// select
func typecheckselect(sel *Node) {
	var ncase *Node
	var n *Node

	var def *Node
	lno := setlineno(sel)
	count := 0
	typecheckslice(sel.Ninit.Slice(), Etop)
	for _, n1 := range sel.List.Slice() {
		count++
		ncase = n1
		setlineno(ncase)
		if ncase.Op != OXCASE {
			Fatalf("typecheckselect %v", ncase.Op)
		}

		if ncase.List.Len() == 0 {
			// default
			if def != nil {
				yyerror("multiple defaults in select (first at %v)", def.Line())
			} else {
				def = ncase
			}
		} else if ncase.List.Len() > 1 {
			yyerror("select cases cannot be lists")
		} else {
			ncase.List.SetFirst(typecheck(ncase.List.First(), Etop))
			n = ncase.List.First()
			ncase.Left = n
			ncase.List.Set(nil)
			setlineno(n)
			switch n.Op {
			default:
				yyerror("select case must be receive, send or assign recv")

			// convert x = <-c into OSELRECV(x, <-c).
			// remove implicit conversions; the eventual assignment
			// will reintroduce them.
			case OAS:
				if (n.Right.Op == OCONVNOP || n.Right.Op == OCONVIFACE) && n.Right.Implicit {
					n.Right = n.Right.Left
				}

				if n.Right.Op != ORECV {
					yyerror("select assignment must have receive on right hand side")
					break
				}

				n.Op = OSELRECV

				// convert x, ok = <-c into OSELRECV2(x, <-c) with ntest=ok
			case OAS2RECV:
				if n.Rlist.First().Op != ORECV {
					yyerror("select assignment must have receive on right hand side")
					break
				}

				n.Op = OSELRECV2
				n.Left = n.List.First()
				n.List.Set1(n.List.Second())
				n.Right = n.Rlist.First()
				n.Rlist.Set(nil)

				// convert <-c into OSELRECV(N, <-c)
			case ORECV:
				n = nod(OSELRECV, nil, n)

				n.Typecheck = 1
				ncase.Left = n

			case OSEND:
				break
			}
		}

		typecheckslice(ncase.Nbody.Slice(), Etop)
	}

	sel.Xoffset = int64(count)
	lineno = lno
}

func walkselect(sel *Node) {
	if sel.List.Len() == 0 && sel.Xoffset != 0 {
		Fatalf("double walkselect") // already rewrote
	}

	lno := setlineno(sel)
	i := sel.List.Len()

	// optimization: zero-case select
	if i == 0 {
		sel.Nbody.Set1(mkcall("block", nil, nil))
		goto out
	}

	// optimization: one-case select: single op.
	// TODO(rsc): Reenable optimization once order.go can handle it.
	// golang.org/issue/7672.
	if i == 1 {
		cas := sel.List.First()
		setlineno(cas)
		l := cas.Ninit.Slice()
		if cas.Left != nil { // not default:
			n := cas.Left
			l = append(l, n.Ninit.Slice()...)
			n.Ninit.Set(nil)
			var ch *Node
			switch n.Op {
			default:
				Fatalf("select %v", n.Op)

				// ok already
			case OSEND:
				ch = n.Left

			case OSELRECV, OSELRECV2:
				ch = n.Right.Left
				if n.Op == OSELRECV || n.List.Len() == 0 {
					if n.Left == nil {
						n = n.Right
					} else {
						n.Op = OAS
					}
					break
				}

				if n.Left == nil {
					nblank = typecheck(nblank, Erv|Easgn)
					n.Left = nblank
				}

				n.Op = OAS2
				n.List.Prepend(n.Left)
				n.Rlist.Set1(n.Right)
				n.Right = nil
				n.Left = nil
				n.Typecheck = 0
				n = typecheck(n, Etop)
			}

			// if ch == nil { block() }; n;
			a := nod(OIF, nil, nil)

			a.Left = nod(OEQ, ch, nodnil())
			var ln Nodes
			ln.Set(l)
			a.Nbody.Set1(mkcall("block", nil, &ln))
			l = ln.Slice()
			a = typecheck(a, Etop)
			l = append(l, a)
			l = append(l, n)
		}

		l = append(l, cas.Nbody.Slice()...)
		sel.Nbody.Set(l)
		goto out
	}

	// convert case value arguments to addresses.
	// this rewrite is used by both the general code and the next optimization.
	for _, cas := range sel.List.Slice() {
		setlineno(cas)
		n := cas.Left
		if n == nil {
			continue
		}
		switch n.Op {
		case OSEND:
			n.Right = nod(OADDR, n.Right, nil)
			n.Right = typecheck(n.Right, Erv)

		case OSELRECV, OSELRECV2:
			if n.Op == OSELRECV2 && n.List.Len() == 0 {
				n.Op = OSELRECV
			}
			if n.Op == OSELRECV2 {
				n.List.SetFirst(nod(OADDR, n.List.First(), nil))
				n.List.SetFirst(typecheck(n.List.First(), Erv))
			}

			if n.Left != nil {
				n.Left = nod(OADDR, n.Left, nil)
				n.Left = typecheck(n.Left, Erv)
			}
		}
	}

	// optimization: two-case select but one is default: single non-blocking op.
	if i == 2 && (sel.List.First().Left == nil || sel.List.Second().Left == nil) {
		var cas *Node
		var dflt *Node
		if sel.List.First().Left == nil {
			cas = sel.List.Second()
			dflt = sel.List.First()
		} else {
			dflt = sel.List.Second()
			cas = sel.List.First()
		}

		n := cas.Left
		setlineno(n)
		r := nod(OIF, nil, nil)
		r.Ninit.Set(cas.Ninit.Slice())
		switch n.Op {
		default:
			Fatalf("select %v", n.Op)

			// if selectnbsend(c, v) { body } else { default body }
		case OSEND:
			ch := n.Left

			r.Left = mkcall1(chanfn("selectnbsend", 2, ch.Type), Types[TBOOL], &r.Ninit, typename(ch.Type), ch, n.Right)

			// if c != nil && selectnbrecv(&v, c) { body } else { default body }
		case OSELRECV:
			r = nod(OIF, nil, nil)

			r.Ninit.Set(cas.Ninit.Slice())
			ch := n.Right.Left
			r.Left = mkcall1(chanfn("selectnbrecv", 2, ch.Type), Types[TBOOL], &r.Ninit, typename(ch.Type), n.Left, ch)

			// if c != nil && selectnbrecv2(&v, c) { body } else { default body }
		case OSELRECV2:
			r = nod(OIF, nil, nil)

			r.Ninit.Set(cas.Ninit.Slice())
			ch := n.Right.Left
			r.Left = mkcall1(chanfn("selectnbrecv2", 2, ch.Type), Types[TBOOL], &r.Ninit, typename(ch.Type), n.Left, n.List.First(), ch)
		}

		r.Left = typecheck(r.Left, Erv)
		r.Nbody.Set(cas.Nbody.Slice())
		r.Rlist.Set(append(dflt.Ninit.Slice(), dflt.Nbody.Slice()...))
		sel.Nbody.Set1(r)
		goto out
	}

	{
		defer func() {
			if err := recover(); err != nil {
				fmt.Println(linestr(sel.Pos), sel)
				panic(err)
			}
		}()

		init := sel.Ninit.Slice()
		sel.Ninit.Set(nil)

		// generate sel-struct
		setlineno(sel)
		typ := typArray(scasetype(), sel.Xoffset)
		selv := temp(typ)
		lockorderarr := temp(typArray(Types[TUINT16], sel.Xoffset))
		pollorderarr := temp(typArray(Types[TUINT16], sel.Xoffset))

		lit := nod(OCOMPLIT, nil, typenod(typ))
		for _, cas := range sel.List.Slice() {
			setlineno(cas)

			init = append(init, cas.Ninit.Slice()...)
			cas.Ninit.Set(nil)

			const (
				caseRecv    = 1
				caseSend    = 2
				caseDefault = 3
			)

			var elem, hchan, receivedp *Node
			var kind int64 = caseDefault

			if n := cas.Left; n != nil {
				init = append(init, n.Ninit.Slice()...)
				n.Ninit.Set(nil)

				switch n.Op {
				case OSEND:
					elem, hchan = n.Right, n.Left
					kind = caseSend
				case OSELRECV:
					elem, hchan = n.Left, n.Right.Left
					kind = caseRecv
				case OSELRECV2:
					elem, hchan, receivedp = n.Left, n.Right.Left, n.List.First()
					kind = caseRecv
				}
			}

			if elem != nil {
				elem = nod(OCONVNOP, elem, nil)
				elem.Type = Types[TUNSAFEPTR]
			} else {
				elem = nodnil()
			}

			hchan = nod(OCONVNOP, hchan, nil)
			hchan.Type = Types[TUNSAFEPTR]

			if receivedp != nil {
				receivedp = nod(OCONVNOP, receivedp, nil)
				receivedp.Type = ptrto(Types[TBOOL])
			} else {
				receivedp = nodnil()
			}

			x := nod(OCOMPLIT, nil, nil)
			x.List.Append(elem, hchan, receivedp, nodintconst(kind), nodintconst(0))
			lit.List.Append(x)
		}

		setlineno(sel)
		r := nod(OAS, selv, lit)
		r = typecheck(r, Etop)
		init = append(init, r)

		chosen := temp(Types[TINT])
		r = nod(OAS, chosen, mkcall("selectgo", Types[TINT], nil,
			convUnsafePointer(nod(OADDR, nod(OINDEX, selv, nodintconst(0)), nil)),
			nod(OADDR, nod(OINDEX, lockorderarr, nodintconst(0)), nil),
			nod(OADDR, nod(OINDEX, pollorderarr, nodintconst(0)), nil),
			nodintconst(sel.Xoffset),
		))
		r = typecheck(r, Etop)
		init = append(init, r)

		init = append(init,
			nod(OVARKILL, selv, nil),
			nod(OVARKILL, lockorderarr, nil),
			nod(OVARKILL, pollorderarr, nil),
		)

		// Dispatch cases.
		// TODO(mdempsky): Use a switch / jump table.
		for i, cas := range sel.List.Slice() {
			setlineno(cas)

			cond := nod(OEQ, chosen, nodintconst(int64(i)))
			cond = typecheck(cond, Erv)

			r = nod(OIF, cond, nil)
			r.Nbody.AppendNodes(&cas.Nbody)
			r.Nbody.Append(nod(OBREAK, nil, nil))
			init = append(init, r)
		}

		sel.Nbody.Set(init)
	}

out:
	sel.List.Set(nil)
	walkstmtlist(sel.Nbody.Slice())
	lineno = lno
}

func convUnsafePointer(n *Node) *Node {
	r := nod(OCONVNOP, n, nil)
	r.Type = ptrto(Types[TUINT8])
	return r
}

// Keep in sync with src/runtime/select.go.
func scasetype() *Type {
	scase := nod(OTSTRUCT, nil, nil)
	scase.List.Append(nod(ODCLFIELD, newname(lookup("elem")), typenod(Types[TUNSAFEPTR])))
	scase.List.Append(nod(ODCLFIELD, newname(lookup("chan")), typenod(Types[TUNSAFEPTR])))
	scase.List.Append(nod(ODCLFIELD, newname(lookup("receivedp")), typenod(ptrto(Types[TBOOL]))))
	scase.List.Append(nod(ODCLFIELD, newname(lookup("kind")), typenod(Types[TUINT16])))
	scase.List.Append(nod(ODCLFIELD, newname(lookup("releasetime")), typenod(Types[TINT64])))
	scase = typecheck(scase, Etype)
	scase.Type.Noalg = true
	scase.Type.Local = true

	return scase.Type
}
