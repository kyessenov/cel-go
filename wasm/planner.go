// Copyright 2018 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package wasm

import (
	"fmt"

	"github.com/go-interpreter/wagon/disasm"
	"github.com/go-interpreter/wagon/wasm"
	ops "github.com/go-interpreter/wagon/wasm/operators"

	"github.com/google/cel-go/common/overloads"
	"github.com/google/cel-go/common/types/ref"

	exprpb "google.golang.org/genproto/googleapis/api/expr/v1alpha1"
)

type Instructions = []disasm.Instr

func NewPlanner(
	adapter ref.TypeAdapter,
	checked *exprpb.CheckedExpr) *planner {
	return &planner{
		adapter: adapter,
		refMap:  checked.GetReferenceMap(),
		typeMap: checked.GetTypeMap(),
		strings: make(map[string]*String),
	}
}

type planner struct {
	adapter ref.TypeAdapter
	refMap  map[int64]*exprpb.Reference
	typeMap map[int64]*exprpb.Type

	strings map[string]*String
	data    int32
}

type String struct {
	val string
	off int32
}

func (p *planner) StringData(s string) *String {
	out, ok := p.strings[s]
	if !ok {
		out = &String{
			val: s,
			off: p.data,
		}
		p.data += int32(len(s))
		p.strings[s] = out
	}
	return out
}

func Plan(checked *exprpb.CheckedExpr) (Instructions, map[string]*String) {
	planner := NewPlanner(nil, checked)
	return planner.Plan(checked.Expr), planner.strings
}

// Plan implements the interpretablePlanner interface. This implementation of the Plan method also
// applies decorators to each Interpretable generated as part of the overall plan. Decorators are
// useful for layering functionality into the evaluation that is not natively understood by CEL,
// such as state-tracking, expression re-write, and possibly efficient thread-safe memoization of
// repeated expressions.
func (p *planner) Plan(expr *exprpb.Expr) Instructions {
	switch expr.ExprKind.(type) {
	case *exprpb.Expr_CallExpr:
		return p.planCall(expr)
	case *exprpb.Expr_IdentExpr:
		return p.planIdent(expr.GetIdentExpr().Name, p.typeMap[expr.Id])
	case *exprpb.Expr_SelectExpr:
		return p.planSelect(expr)
	case *exprpb.Expr_ConstExpr:
		return p.planConst(expr)
	}
	panic(fmt.Sprintf("unsupported expr: %v", expr))
}

// planIdent creates an Interpretable that resolves an identifier from an Activation.
func (p *planner) planIdent(name string, typ *exprpb.Type) Instructions {
	// TODO: only works for I64 and heap objects
	out := make(Instructions, 0)
	s := p.StringData(name)
	out = append(out, do(ops.I32Const, s.off))
	out = append(out, do(ops.I32Const, int32(len(s.val))))
	out = append(out, do(ops.Call, LoadIdent))
	return out
}

// planSelect creates an Interpretable with either:
//  a) selects a field from a map or proto.
//  b) creates a field presence test for a select within a has() macro.
//  c) resolves the select expression to a namespaced identifier.
func (p *planner) planSelect(expr *exprpb.Expr) Instructions {
	// If the Select id appears in the reference map from the CheckedExpr proto then it is either
	// a namespaced identifier or enum value.
	idRef, found := p.refMap[expr.Id]
	_ = idRef
	if found {
		return p.planIdent(idRef.Name, p.typeMap[expr.Id])
	}

	sel := expr.GetSelectExpr()
	out := make(Instructions, 0)
	out = append(out, p.Plan(sel.GetOperand())...)
	s := p.StringData(sel.Field)
	out = append(out, do(ops.I32Const, s.off))
	out = append(out, do(ops.I32Const, int32(len(s.val))))

	// If the Select was marked TestOnly, this is a presence test.
	//
	// Note: presence tests are defined for structured (e.g. proto) and dynamic values (map, json)
	// as follows:
	//  - True if the object field has a non-default value, e.g. obj.str != ""
	//  - True if the dynamic value has the field defined, e.g. key in map
	//
	// However, presence tests are not defined for qualified identifier names with primitive types.
	// If a string named 'a.b.c' is declared in the environment and referenced within `has(a.b.c)`,
	// it is not clear whether has should error or follow the convention defined for structured
	// values.
	if sel.TestOnly {
		out = append(out, do(ops.Call, TestSelect))
	} else {
		out = append(out, do(ops.Call, Select))
	}
	return out
}

// planCall creates a callable Interpretable while specializing for common functions and invocation
// patterns. Specifically, conditional operators &&, ||, ?:, and (in)equality functions result in
// optimized Interpretable values.
func (p *planner) planCall(expr *exprpb.Expr) Instructions {
	call := expr.GetCallExpr()
	args := call.GetArgs()

	var oName string
	if oRef, found := p.refMap[expr.Id]; found &&
		len(oRef.GetOverloadId()) == 1 {
		oName = oRef.GetOverloadId()[0]

		out := make(Instructions, 0)
		// generate raw code using the overload function
		switch oName {
		/*
			Triple-value boolean logic
			i32 data value
			0 false
			1 true
			2+ error code
		*/
		case overloads.Conditional:
			// TODO: add error case to br_table

			// else block
			out = append(out, do(ops.Block, wasm.BlockType(wasm.ValueTypeI32)))
			// then block
			out = append(out, do(ops.Block, wasm.BlockType(wasm.ValueTypeI32)))
			out = append(out, do(ops.I32Const, int32(0))) // popped by br_table
			// if block
			out = append(out, do(ops.Block, wasm.BlockTypeEmpty))
			cond := p.Plan(args[0])
			out = append(out, cond...)
			out = append(out, do(ops.BrTable, uint32(1), uint32(1), uint32(0)))
			out = append(out, do(ops.End))
			// end if block

			out = append(out, do(ops.Drop))
			truthy := p.Plan(args[1])
			out = append(out, truthy...)
			out = append(out, do(ops.Br, uint32(1)))
			out = append(out, do(ops.End))
			// end then block

			falsy := p.Plan(args[2])
			out = append(out, falsy...)
			out = append(out, do(ops.End))
			// end else block

			return out

		case overloads.LogicalAnd:
			out = append(out, do(ops.Block, wasm.BlockType(wasm.ValueTypeI32)))
			out = append(out, do(ops.Block, wasm.BlockType(wasm.ValueTypeI32)))
			out = append(out, do(ops.I32Const, int32(0)))
			out = append(out, do(ops.Block, wasm.BlockTypeEmpty))

			// short-circuit lhs.
			lhs := p.Plan(args[0])
			out = append(out, lhs...)

			// if value is 0, break, return false
			// if value is 1 return RHS
			// TODO:
			// if value is >=2, evaluate RHS return either false or error
			out = append(out, do(ops.BrTable, uint32(2), uint32(1), uint32(0), uint32(0)))
			out = append(out, do(ops.End))

			// short-circuit rhs
			out = append(out, do(ops.Drop))
			rhs := p.Plan(args[1])
			out = append(out, rhs...)
			out = append(out, do(ops.Br, uint32(1)))
			out = append(out, do(ops.End))

			// false value
			out = append(out, do(ops.I32Const, int32(0)))
			out = append(out, do(ops.End))

			return out

		case overloads.AddInt64:
			out = append(out, p.Plan(args[0])...)
			out = append(out, p.Plan(args[1])...)
			out = append(out, do(ops.I64Add))
			return out
		case overloads.AddDouble:
			out = append(out, p.Plan(args[0])...)
			out = append(out, p.Plan(args[1])...)
			out = append(out, do(ops.F64Add))
			return out
		case overloads.MultiplyInt64:
			out = append(out, p.Plan(args[0])...)
			out = append(out, p.Plan(args[1])...)
			out = append(out, do(ops.I64Mul))
			return out
		case overloads.MultiplyDouble:
			out = append(out, p.Plan(args[0])...)
			out = append(out, p.Plan(args[1])...)
			out = append(out, do(ops.F64Mul))
			return out
		case overloads.SubtractInt64:
			out = append(out, p.Plan(args[0])...)
			out = append(out, p.Plan(args[1])...)
			out = append(out, do(ops.I64Sub))
			return out

			// TODO: partial semantics
		case overloads.DivideDouble:
			out = append(out, p.Plan(args[0])...)
			out = append(out, p.Plan(args[1])...)
			out = append(out, do(ops.F64Div))
			return out
		case overloads.DivideInt64:
			out = append(out, p.Plan(args[0])...)
			out = append(out, p.Plan(args[1])...)
			out = append(out, do(ops.I64DivS))
			return out

		case overloads.DoubleToInt:
			out = append(out, p.Plan(args[0])...)
			out = append(out, do(ops.I64TruncSF64))
			return out

		case overloads.EqualsInt64:
			out = append(out, p.Plan(args[0])...)
			out = append(out, p.Plan(args[1])...)
			out = append(out, do(ops.I64Eq))
			return out

			// TODO: all the other functions...

		}
	}

	// Load all arguments to the heap for overload invocation
	fnName := call.Function
	s := p.StringData(fnName)

	out := make(Instructions, 0)
	out = append(out,
		do(ops.I32Const, s.off),
		do(ops.I32Const, int32(len(s.val))))

	for _, arg := range args {
		out = append(out, p.Plan(arg)...)
		// TODO: make sure it is a heap value
		typ, ok := p.typeMap[arg.Id]
		if ok {
			switch t := typ.TypeKind.(type) {
			case *exprpb.Type_Primitive:
				switch t.Primitive {
				case exprpb.Type_INT64:
					out = append(out, do(ops.Call, StoreI64))
				}
			}
		}
	}

	switch len(args) {
	case 1:
		out = append(out, do(ops.Call, Invoke1))
	case 2:
		out = append(out, do(ops.Call, Invoke2))
	default:
		panic(fmt.Sprintf("not implemented: overload %q function %q\n", oName, fnName))
	}

	// TODO: make sure it is a stack value
	typ, ok := p.typeMap[expr.Id]
	if ok {
		switch t := typ.TypeKind.(type) {
		case *exprpb.Type_Primitive:
			switch t.Primitive {
			case exprpb.Type_INT64:
				out = append(out, do(ops.Call, LoadI64))
			}
		}
	}

	return out
}

// planConst generates a constant valued Interpretable.
func (p *planner) planConst(expr *exprpb.Expr) Instructions {
	c := expr.GetConstExpr()
	switch c.ConstantKind.(type) {
	case *exprpb.Constant_BoolValue:
		if c.GetBoolValue() {
			return Instructions{do(ops.I32Const, int32(1))}
		} else {
			return Instructions{do(ops.I32Const, int32(0))}
		}
	case *exprpb.Constant_DoubleValue:
		return Instructions{do(ops.F64Const, c.GetDoubleValue())}
	case *exprpb.Constant_Int64Value:
		return Instructions{do(ops.I64Const, c.GetInt64Value())}
	case *exprpb.Constant_NullValue:
		return Instructions{do(ops.I64Const, int64(0))}
	case *exprpb.Constant_Uint64Value:
		return Instructions{do(ops.I64Const, int64(c.GetUint64Value()))}
	case *exprpb.Constant_StringValue:
		s := p.StringData(c.GetStringValue())
		return Instructions{
			do(ops.I32Const, s.off),
			do(ops.I32Const, int32(len(s.val))),
			do(ops.Call, StoreS),
		}
		/* TODO
		case *exprpb.Constant_BytesValue:
			return types.Bytes(c.GetBytesValue()), nil
		*/
	}
	panic(fmt.Sprintf("unknown constant type: %v", c))
}

// WASM TOOLS

func do(o byte, immediates ...interface{}) disasm.Instr {
	out, _ := ops.New(o)
	return disasm.Instr{
		Op:         out,
		Immediates: immediates,
	}
}
