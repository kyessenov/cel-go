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
	"errors"
	"fmt"

	"github.com/go-interpreter/wagon/disasm"
	"github.com/go-interpreter/wagon/wasm"
	ops "github.com/go-interpreter/wagon/wasm/operators"

	"github.com/google/cel-go/common/overloads"
	"github.com/google/cel-go/common/packages"
	"github.com/google/cel-go/common/types"
	"github.com/google/cel-go/common/types/ref"
	"github.com/google/cel-go/common/types/traits"
	"github.com/google/cel-go/interpreter"
	"github.com/google/cel-go/interpreter/functions"

	exprpb "google.golang.org/genproto/googleapis/api/expr/v1alpha1"
)

type Interpretable = interpreter.Interpretable
type Activation = interpreter.Activation
type Instructions = []disasm.Instr

func NewPlanner(
	provider ref.TypeProvider,
	adapter ref.TypeAdapter,
	pkg packages.Packager,
	checked *exprpb.CheckedExpr) *planner {
	return &planner{
		provider: provider,
		adapter:  adapter,
		pkg:      pkg,
		identMap: make(map[string]Interpretable),
		refMap:   checked.GetReferenceMap(),
		typeMap:  checked.GetTypeMap(),
	}
}

// planner is an implementatio of the interpretablePlanner interface.
type planner struct {
	provider ref.TypeProvider
	adapter  ref.TypeAdapter
	pkg      packages.Packager
	identMap map[string]Interpretable
	refMap   map[int64]*exprpb.Reference
	typeMap  map[int64]*exprpb.Type
}

func Plan(checked *exprpb.CheckedExpr) Instructions {
	planner := NewPlanner(nil, nil, nil, checked)
	return planner.Plan(checked.Expr)
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
		p.planIdent(expr)
	case *exprpb.Expr_SelectExpr:
		p.planSelect(expr)
	case *exprpb.Expr_ListExpr:
		p.planCreateList(expr)
	case *exprpb.Expr_StructExpr:
		p.planCreateStruct(expr)
	case *exprpb.Expr_ConstExpr:
		return p.planConst(expr)
	}
	panic(fmt.Sprintf("unsupported expr: %v", expr))
}

// planIdent creates an Interpretable that resolves an identifier from an Activation.
func (p *planner) planIdent(expr *exprpb.Expr) (Interpretable, error) {
	ident := expr.GetIdentExpr()
	idName := ident.Name
	i, found := p.identMap[idName]
	if found {
		return i, nil
	}
	var resolver func(Activation) (ref.Val, bool)
	if p.pkg.Package() != "" {
		resolver = p.idResolver(idName)
	}
	i = &evalIdent{
		id:        expr.Id,
		name:      idName,
		provider:  p.provider,
		resolveID: resolver,
	}
	p.identMap[idName] = i
	return i, nil
}

// planSelect creates an Interpretable with either:
//  a) selects a field from a map or proto.
//  b) creates a field presence test for a select within a has() macro.
//  c) resolves the select expression to a namespaced identifier.
func (p *planner) planSelect(expr *exprpb.Expr) (Interpretable, error) {
	sel := expr.GetSelectExpr()
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
		op := p.Plan(sel.GetOperand())
		return &evalTestOnly{
			id:    expr.Id,
			field: types.String(sel.Field),
			op:    op,
		}, nil
	}

	// If the Select id appears in the reference map from the CheckedExpr proto then it is either
	// a namespaced identifier or enum value.
	idRef, found := p.refMap[expr.Id]
	if found {
		idName := idRef.Name
		// If the reference has a value, this id represents an enum.
		if idRef.Value != nil {
			// TODO
			/*
				return p.Plan(&exprpb.Expr{Id: expr.Id,
					ExprKind: &exprpb.Expr_ConstExpr{
						ConstExpr: idRef.Value,
					}})
			*/
		}
		// If the identifier has already been encountered before, return the previous Iterable.
		i, found := p.identMap[idName]
		if found {
			return i, nil
		}
		// Otherwise, generate an evalIdent Interpretable.
		i = &evalIdent{
			id:   expr.Id,
			name: idName,
		}
		p.identMap[idName] = i
		return i, nil
	}

	// Lastly, create a field selection Interpretable.
	/*
		op, err := p.Plan(sel.GetOperand())
		if err != nil {
			return nil, err
		}
		var resolver func(Activation) (ref.Val, bool)
		if qualID, isID := p.getQualifiedID(sel); isID {
			resolver = p.idResolver(qualID)
		}
		return &evalSelect{
			id:    expr.Id,
			field: types.String(sel.Field),
			op:        op,
			resolveID: resolver,
		}, nil
	*/
	return nil, errors.New("not implemented")
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
			// short-circuit lhs.
			out = append(out, do(ops.Block, wasm.BlockType(wasm.ValueTypeI32)))
			lhs, err := p.Plan(args[0])
			if err != nil {
				return nil, err
			}
			out = append(out, lhs...)

			// if value is 0, break

			out = append(out, do(ops.End))

			lVal := and.lhs.Eval(ctx)
			lBool, lok := lVal.(types.Bool)
			if lok && lBool == types.False {
				return types.False
			}
			// short-circuit on rhs.
			rVal := and.rhs.Eval(ctx)
			rBool, rok := rVal.(types.Bool)
			if rok && rBool == types.False {
				return types.False
			}
			// return if both sides are bool true.
			if lok && rok {
				return types.True
			}

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

			// TODO: partial semantics
		case overloads.DivideDouble:
			out = append(out, p.Plan(args[0])...)
			out = append(out, p.Plan(args[1])...)
			out = append(out, do(ops.F64Div))
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

	fnName := call.Function
	fmt.Printf("overload %q function %q\n", oName, fnName)

	argCount := len(call.GetArgs())
	var offset int
	if call.Target != nil {
		argCount++
		offset++
	}
	/*
		args := make([]Interpretable, argCount, argCount)
			if call.Target != nil {
				arg, err := p.Plan(call.Target)
				if err != nil {
					return nil, err
				}
				args[0] = arg
			}
			for i, argExpr := range call.GetArgs() {
				arg, err := p.Plan(argExpr)
				if err != nil {
					return nil, err
				}
				args[i+offset] = arg
			}
	*/

	panic("not implemented")
	/*
		// Otherwise, generate Interpretable calls specialized by argument count.
		switch argCount {
		case 0:
			return p.planCallZero(expr, fnName, oName, fnDef)
		case 1:
			return p.planCallUnary(expr, fnName, oName, fnDef, args)
		case 2:
			return p.planCallBinary(expr, fnName, oName, fnDef, args)
		default:
			return p.planCallVarArgs(expr, fnName, oName, fnDef, args)
		}
	*/
}

// planCallZero generates a zero-arity callable Interpretable.
func (p *planner) planCallZero(expr *exprpb.Expr,
	function string,
	overload string,
	impl *functions.Overload) (Interpretable, error) {
	if impl == nil || impl.Function == nil {
		return nil, fmt.Errorf("no such overload: %s()", function)
	}
	return &evalZeroArity{
		id:   expr.Id,
		impl: impl.Function,
	}, nil
}

// planCallUnary generates a unary callable Interpretable.
func (p *planner) planCallUnary(expr *exprpb.Expr,
	function string,
	overload string,
	impl *functions.Overload,
	args []Interpretable) (Interpretable, error) {
	var fn functions.UnaryOp
	var trait int
	if impl != nil {
		if impl.Unary == nil {
			return nil, fmt.Errorf("no such overload: %s(arg)", function)
		}
		fn = impl.Unary
		trait = impl.OperandTrait
	}
	return &evalUnary{
		id:       expr.Id,
		function: function,
		overload: overload,
		arg:      args[0],
		trait:    trait,
		impl:     fn,
	}, nil
}

// planCallBinary generates a binary callable Interpretable.
func (p *planner) planCallBinary(expr *exprpb.Expr,
	function string,
	overload string,
	impl *functions.Overload,
	args []Interpretable) (Interpretable, error) {
	var fn functions.BinaryOp
	var trait int
	if impl != nil {
		if impl.Binary == nil {
			return nil, fmt.Errorf("no such overload: %s(lhs, rhs)", function)
		}
		fn = impl.Binary
		trait = impl.OperandTrait
	}
	return &evalBinary{
		id:       expr.Id,
		function: function,
		overload: overload,
		lhs:      args[0],
		rhs:      args[1],
		trait:    trait,
		impl:     fn,
	}, nil
}

// planCallVarArgs generates a variable argument callable Interpretable.
func (p *planner) planCallVarArgs(expr *exprpb.Expr,
	function string,
	overload string,
	impl *functions.Overload,
	args []Interpretable) (Interpretable, error) {
	var fn functions.FunctionOp
	var trait int
	if impl != nil {
		if impl.Function == nil {
			return nil, fmt.Errorf("no such overload: %s(...)", function)
		}
		fn = impl.Function
		trait = impl.OperandTrait
	}
	return &evalVarArgs{
		id:       expr.Id,
		function: function,
		overload: overload,
		args:     args,
		trait:    trait,
		impl:     fn,
	}, nil
}

// planCreateList generates a list construction Interpretable.
func (p *planner) planCreateList(expr *exprpb.Expr) (Interpretable, error) {
	list := expr.GetListExpr()
	elems := make([]Interpretable, len(list.GetElements()), len(list.GetElements()))
	/*
		for i, elem := range list.GetElements() {
			elemVal, err := p.Plan(elem)
			if err != nil {
				return nil, err
			}
			elems[i] = elemVal
		}
	*/
	return &evalList{
		id:      expr.Id,
		elems:   elems,
		adapter: p.adapter,
	}, nil
}

// planCreateStruct generates a map or object construction Interpretable.
func (p *planner) planCreateStruct(expr *exprpb.Expr) (Interpretable, error) {
	str := expr.GetStructExpr()
	if len(str.MessageName) != 0 {
		return p.planCreateObj(expr)
	}
	entries := str.GetEntries()
	keys := make([]Interpretable, len(entries))
	vals := make([]Interpretable, len(entries))
	/*
		for i, entry := range entries {
			keyVal, err := p.Plan(entry.GetMapKey())
			if err != nil {
				return nil, err
			}
			keys[i] = keyVal

			valVal, err := p.Plan(entry.GetValue())
			if err != nil {
				return nil, err
			}
			vals[i] = valVal
		}
	*/
	return &evalMap{
		id:      expr.Id,
		keys:    keys,
		vals:    vals,
		adapter: p.adapter,
	}, nil
}

// planCreateObj generates an object construction Interpretable.
func (p *planner) planCreateObj(expr *exprpb.Expr) (Interpretable, error) {
	obj := expr.GetStructExpr()
	typeName := obj.MessageName
	var defined bool
	for _, qualifiedTypeName := range p.pkg.ResolveCandidateNames(typeName) {
		if _, found := p.provider.FindType(qualifiedTypeName); found {
			typeName = qualifiedTypeName
			defined = true
			break
		}
	}
	if !defined {
		return nil, fmt.Errorf("unknown type: %s", typeName)
	}
	entries := obj.GetEntries()
	fields := make([]string, len(entries))
	vals := make([]Interpretable, len(entries))
	/*
		for i, entry := range entries {
			fields[i] = entry.GetFieldKey()
			val, err := p.Plan(entry.GetValue())
			if err != nil {
				return nil, err
			}
			vals[i] = val
		}
	*/
	return &evalObj{
		id:       expr.Id,
		typeName: typeName,
		fields:   fields,
		vals:     vals,
		provider: p.provider,
	}, nil
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
		/* TODO
		case *exprpb.Constant_StringValue:
			return types.String(c.GetStringValue()), nil
		case *exprpb.Constant_BytesValue:
			return types.Bytes(c.GetBytesValue()), nil
		*/
	}
	panic(fmt.Sprintf("unknown constant type: %v", c))
}

// getQualifiedId converts a Select expression to a qualified identifier suitable for identifier
// resolution. If the expression is not an identifier, the second return will be false.
func (p *planner) getQualifiedID(sel *exprpb.Expr_Select) (string, bool) {
	validIdent := true
	resolvedIdent := false
	ident := sel.Field
	op := sel.Operand
	for validIdent && !resolvedIdent {
		switch op.ExprKind.(type) {
		case *exprpb.Expr_IdentExpr:
			ident = op.GetIdentExpr().Name + "." + ident
			resolvedIdent = true
		case *exprpb.Expr_SelectExpr:
			nested := op.GetSelectExpr()
			ident = nested.GetField() + "." + ident
			op = nested.Operand
		default:
			validIdent = false
		}
	}
	return ident, validIdent
}

// idResolver returns a function that resolves an identifier to its appropriate namespace.
func (p *planner) idResolver(ident string) func(Activation) (ref.Val, bool) {
	return func(ctx Activation) (ref.Val, bool) {
		for _, id := range p.pkg.ResolveCandidateNames(ident) {
			if object, found := ctx.ResolveName(id); found {
				return object, found
			}
			if typeIdent, found := p.provider.FindIdent(id); found {
				return typeIdent, found
			}
		}
		return nil, false
	}
}

type evalIdent struct {
	id        int64
	name      string
	provider  ref.TypeProvider
	resolveID func(Activation) (ref.Val, bool)
}

// ID implements the Interpretable interface method.
func (id *evalIdent) ID() int64 {
	return id.id
}

// Eval implements the Interpretable interface method.
func (id *evalIdent) Eval(ctx Activation) ref.Val {
	idName := id.name
	if id.resolveID != nil {
		// When the resolveID function is non-nil, the name could be relative
		// to the container.
		if val, found := id.resolveID(ctx); found {
			return val
		}
	} else {
		// Resolve the simple name directly as a type or ident.
		val, found := ctx.ResolveName(idName)
		if found {
			return val
		}
		typeVal, found := id.provider.FindIdent(idName)
		if found {
			return typeVal
		}
	}
	return types.Unknown{id.id}

}

type evalSelect struct {
	id        int64
	op        Interpretable
	field     types.String
	resolveID func(Activation) (ref.Val, bool)
}

// ID implements the Interpretable interface method.
func (sel *evalSelect) ID() int64 {
	return sel.id
}

// Eval implements the Interpretable interface method.
func (sel *evalSelect) Eval(ctx Activation) ref.Val {
	// If the select is actually a qualified identifier return.
	if sel.resolveID != nil {
		if resolve, found := sel.resolveID(ctx); found {
			return resolve
		}
	}
	// Otherwise, evaluate the operand and select the field.
	obj := sel.op.Eval(ctx)
	indexer, ok := obj.(traits.Indexer)
	if !ok {
		return types.ValOrErr(obj, "invalid type for field selection.")
	}
	return indexer.Get(sel.field)
}

type evalTestOnly struct {
	id    int64
	op    Instructions
	field types.String
}

// ID implements the Interpretable interface method.
func (test *evalTestOnly) ID() int64 {
	return test.id
}

// Eval implements the Interpretable interface method.
func (test *evalTestOnly) Eval(ctx Activation) ref.Val {
	/*
		obj := test.op.Eval(ctx)
		tester, ok := obj.(traits.FieldTester)
		if ok {
			return tester.IsSet(test.field)
		}
		container, ok := obj.(traits.Container)
		if ok {
			return container.Contains(test.field)
		}
	*/
	return types.ValOrErr(types.Bool(true), "invalid type for field selection.")

}

type evalOr struct {
	id  int64
	lhs Interpretable
	rhs Interpretable
}

// ID implements the Interpretable interface method.
func (or *evalOr) ID() int64 {
	return or.id
}

// Eval implements the Interpretable interface method.
func (or *evalOr) Eval(ctx Activation) ref.Val {
	// short-circuit lhs.
	lVal := or.lhs.Eval(ctx)
	lBool, lok := lVal.(types.Bool)
	if lok && lBool == types.True {
		return types.True
	}
	// short-circuit on rhs.
	rVal := or.rhs.Eval(ctx)
	rBool, rok := rVal.(types.Bool)
	if rok && rBool == types.True {
		return types.True
	}
	// return if both sides are bool false.
	if lok && rok {
		return types.False
	}
	// TODO: return both values as a set if both are unknown or error.
	// prefer left unknown to right unknown.
	if types.IsUnknown(lVal) {
		return lVal
	}
	if types.IsUnknown(rVal) {
		return rVal
	}
	// if the left-hand side is non-boolean return it as the error.
	return types.ValOrErr(lVal, "no such overload")
}

type evalAnd struct {
	id  int64
	lhs Interpretable
	rhs Interpretable
}

type evalZeroArity struct {
	id   int64
	impl functions.FunctionOp
}

// ID implements the Interpretable interface method.
func (zero *evalZeroArity) ID() int64 {
	return zero.id
}

// Eval implements the Interpretable interface method.
func (zero *evalZeroArity) Eval(ctx Activation) ref.Val {
	return zero.impl()
}

type evalUnary struct {
	id       int64
	function string
	overload string
	arg      Interpretable
	trait    int
	impl     functions.UnaryOp
}

// ID implements the Interpretable interface method.
func (un *evalUnary) ID() int64 {
	return un.id
}

// Eval implements the Interpretable interface method.
func (un *evalUnary) Eval(ctx Activation) ref.Val {
	argVal := un.arg.Eval(ctx)
	// Early return if the argument to the function is unknown or error.
	if types.IsUnknownOrError(argVal) {
		return argVal
	}
	// If the implementation is bound and the argument value has the right traits required to
	// invoke it, then call the implementation.
	if un.impl != nil && (un.trait == 0 || argVal.Type().HasTrait(un.trait)) {
		return un.impl(argVal)
	}
	// Otherwise, if the argument is a ReceiverType attempt to invoke the receiver method on the
	// operand (arg0).
	if argVal.Type().HasTrait(traits.ReceiverType) {
		return argVal.(traits.Receiver).Receive(un.function, un.overload, []ref.Val{})
	}
	return types.NewErr("no such overload: %s", un.function)
}

type evalBinary struct {
	id       int64
	function string
	overload string
	lhs      Interpretable
	rhs      Interpretable
	trait    int
	impl     functions.BinaryOp
}

// ID implements the Interpretable interface method.
func (bin *evalBinary) ID() int64 {
	return bin.id
}

// Eval implements the Interpretable interface method.
func (bin *evalBinary) Eval(ctx Activation) ref.Val {
	lVal := bin.lhs.Eval(ctx)
	rVal := bin.rhs.Eval(ctx)
	// Early return if any argument to the function is unknown or error.
	if types.IsUnknownOrError(lVal) {
		return lVal
	}
	if types.IsUnknownOrError(rVal) {
		return rVal
	}
	// If the implementation is bound and the argument value has the right traits required to
	// invoke it, then call the implementation.
	if bin.impl != nil && (bin.trait == 0 || lVal.Type().HasTrait(bin.trait)) {
		return bin.impl(lVal, rVal)
	}
	// Otherwise, if the argument is a ReceiverType attempt to invoke the receiver method on the
	// operand (arg0).
	if lVal.Type().HasTrait(traits.ReceiverType) {
		return lVal.(traits.Receiver).Receive(bin.function, bin.overload, []ref.Val{rVal})
	}
	return types.NewErr("no such overload: %s", bin.function)
}

type evalVarArgs struct {
	id       int64
	function string
	overload string
	args     []Interpretable
	trait    int
	impl     functions.FunctionOp
}

// ID implements the Interpretable interface method.
func (fn *evalVarArgs) ID() int64 {
	return fn.id
}

// Eval implements the Interpretable interface method.
func (fn *evalVarArgs) Eval(ctx Activation) ref.Val {
	argVals := make([]ref.Val, len(fn.args), len(fn.args))
	// Early return if any argument to the function is unknown or error.
	for i, arg := range fn.args {
		argVals[i] = arg.Eval(ctx)
		if types.IsUnknownOrError(argVals[i]) {
			return argVals[i]
		}
	}
	// If the implementation is bound and the argument value has the right traits required to
	// invoke it, then call the implementation.
	arg0 := argVals[0]
	if fn.impl != nil && (fn.trait == 0 || arg0.Type().HasTrait(fn.trait)) {
		return fn.impl(argVals...)
	}
	// Otherwise, if the argument is a ReceiverType attempt to invoke the receiver method on the
	// operand (arg0).
	if arg0.Type().HasTrait(traits.ReceiverType) {
		return arg0.(traits.Receiver).Receive(fn.function, fn.overload, argVals[1:])
	}
	return types.NewErr("no such overload: %s", fn.function)
}

type evalList struct {
	id      int64
	elems   []Interpretable
	adapter ref.TypeAdapter
}

// ID implements the Interpretable interface method.
func (l *evalList) ID() int64 {
	return l.id
}

// Eval implements the Interpretable interface method.
func (l *evalList) Eval(ctx Activation) ref.Val {
	elemVals := make([]ref.Val, len(l.elems), len(l.elems))
	// If any argument is unknown or error early terminate.
	for i, elem := range l.elems {
		elemVal := elem.Eval(ctx)
		if types.IsUnknownOrError(elemVal) {
			return elemVal
		}
		elemVals[i] = elemVal
	}
	return types.NewDynamicList(l.adapter, elemVals)
}

type evalMap struct {
	id      int64
	keys    []Interpretable
	vals    []Interpretable
	adapter ref.TypeAdapter
}

// ID implements the Interpretable interface method.
func (m *evalMap) ID() int64 {
	return m.id
}

// Eval implements the Interpretable interface method.
func (m *evalMap) Eval(ctx Activation) ref.Val {
	entries := make(map[ref.Val]ref.Val)
	// If any argument is unknown or error early terminate.
	for i, key := range m.keys {
		keyVal := key.Eval(ctx)
		if types.IsUnknownOrError(keyVal) {
			return keyVal
		}
		valVal := m.vals[i].Eval(ctx)
		if types.IsUnknownOrError(valVal) {
			return valVal
		}
		entries[keyVal] = valVal
	}
	return types.NewDynamicMap(m.adapter, entries)
}

type evalObj struct {
	id       int64
	typeName string
	fields   []string
	vals     []Interpretable
	provider ref.TypeProvider
}

// ID implements the Interpretable interface method.
func (o *evalObj) ID() int64 {
	return o.id
}

// Eval implements the Interpretable interface method.
func (o *evalObj) Eval(ctx Activation) ref.Val {
	fieldVals := make(map[string]ref.Val)
	// If any argument is unknown or error early terminate.
	for i, field := range o.fields {
		val := o.vals[i].Eval(ctx)
		if types.IsUnknownOrError(val) {
			return val
		}
		fieldVals[field] = val
	}
	return o.provider.NewValue(o.typeName, fieldVals)
}

// WASM TOOLS

func do(o byte, immediates ...interface{}) disasm.Instr {
	out, _ := ops.New(o)
	return disasm.Instr{
		Op:         out,
		Immediates: immediates,
	}
}
