package wasm

import (
	"fmt"
	"reflect"

	"github.com/go-interpreter/wagon/disasm"
	"github.com/go-interpreter/wagon/exec"
	"github.com/go-interpreter/wagon/wasm"
	ops "github.com/go-interpreter/wagon/wasm/operators"

	"github.com/google/cel-go/common/types"
	"github.com/google/cel-go/common/types/ref"
	"github.com/google/cel-go/common/types/traits"
	"github.com/google/cel-go/interpreter"
	"github.com/google/cel-go/interpreter/functions"
)

// Data type mapping:
// I64: int64
// I64 (as a heap pointer): string, object/message, map, list, null (0)
// I64: host value of any type
// F64: double
// I32: bool
// I32: error (as a triple boolean value)

const (
	Select uint32 = iota + 1
	TestSelect
	LoadIdent
	StoreS
	LoadI64
	StoreI64
	Invoke1
	Invoke2
	Reserved
)

func assemble(instrs []disasm.Instr) []byte {
	out, err := disasm.Assemble(instrs)
	if err != nil {
		panic(err)
	}
	return out
}

// Host manages the data and hands out pointers to the data
type HostFunctions struct {
	Values      map[string]interface{}
	Heap        []ref.Val
	Dispatcher  interpreter.Dispatcher
	TypeAdapter ref.TypeAdapter
}

// I64 values are made concrete for integers
func (host *HostFunctions) LoadIdent(proc *exec.Process, o, l int32) int64 {
	s := make([]byte, l)
	proc.ReadAt(s, int64(o))

	native, ok := host.Values[string(s)]

	// TODO: missing activation value?
	if !ok {
		return 0
	}

	val := host.TypeAdapter.NativeToValue(native)

	// TODO: manage other primitive types
	switch val.Type() {
	case types.IntType:
		return int64(val.(types.Int))
	default:
		host.Heap = append(host.Heap, val)
		return int64(len(host.Heap))
	}
}

func (host *HostFunctions) StoreS(proc *exec.Process, o, l int32) int64 {
	s := make([]byte, l)
	proc.ReadAt(s, int64(o))
	host.Heap = append(host.Heap, types.String(s))
	return int64(len(host.Heap))
}

func (host *HostFunctions) LoadI64(proc *exec.Process, v int64) int64 {
	val := host.Heap[v-1]

	switch val.Type() {
	case types.IntType:
		return int64(val.(types.Int))
	}

	return 0
}

func (host *HostFunctions) StoreI64(proc *exec.Process, v int64) int64 {
	host.Heap = append(host.Heap, types.Int(v))
	return int64(len(host.Heap))
}

func (host *HostFunctions) Invoke1(proc *exec.Process, fo, fl int32, h0 int64) int64 {
	fn := make([]byte, fl)
	proc.ReadAt(fn, int64(fo))
	impl, _ := host.Dispatcher.FindOverload(string(fn))
	if impl == nil {
		panic(fmt.Sprintf("missing overload %s", string(fn)))
	}
	if impl.Unary == nil {
		panic("missing unary impl")
	}

	arg0 := host.Heap[h0-1]
	out := impl.Unary(arg0)
	host.Heap = append(host.Heap, out)
	return int64(len(host.Heap))
}

// TODO: need to realize an error value on the heap
func (host *HostFunctions) Invoke2(proc *exec.Process, fo, fl int32, h0, h1 int64) int64 {
	fn := make([]byte, fl)
	proc.ReadAt(fn, int64(fo))
	impl, _ := host.Dispatcher.FindOverload(string(fn))
	if impl == nil {
		panic(fmt.Sprintf("missing overload %s", string(fn)))
	}
	if impl.Binary == nil {
		panic("missing binary impl")
	}

	arg0 := host.Heap[h0-1]
	arg1 := host.Heap[h1-1]

	out := impl.Binary(arg0, arg1)
	host.Heap = append(host.Heap, out)
	return int64(len(host.Heap))
}

func (host *HostFunctions) Select(proc *exec.Process, h int64, o, l int32) int64 {
	rcv := host.Heap[h-1]
	s := make([]byte, l)
	proc.ReadAt(s, int64(o))
	val := rcv.(traits.Indexer).Get(types.String(s))

	host.Heap = append(host.Heap, val)
	return int64(len(host.Heap))
}

func (host *HostFunctions) TestSelect(proc *exec.Process, h int64, o, l int32) int32 {
	rcv := host.Heap[h-1]
	s := make([]byte, l)
	proc.ReadAt(s, int64(o))
	val := rcv.(traits.Indexer).Get(types.String(s))

	if types.IsError(val) {
		return 0
	} else {
		return 1
	}
}

func MakeModule(instrs []disasm.Instr, strings map[string]*String) (*wasm.Module, *HostFunctions) {
	m := wasm.NewModule()
	host := &HostFunctions{
		Dispatcher:  interpreter.NewDispatcher(),
		TypeAdapter: types.NewRegistry(),
	}
	host.Dispatcher.Add(functions.StandardOverloads()...)

	// stop main invocation that drops the value
	m.Start = nil

	env := wasm.FunctionSig{
		Form:        0,
		ParamTypes:  []wasm.ValueType{},
		ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
	}
	id := wasm.FunctionSig{
		ParamTypes: []wasm.ValueType{wasm.ValueTypeI64}, ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
	}

	// The body of the start function, that should only
	// call the host function
	fb := wasm.FunctionBody{
		Module: m,
		Locals: []wasm.LocalEntry{},
		Code:   assemble(instrs),
	}

	m.Types = &wasm.SectionTypes{
		Entries: []wasm.FunctionSig{env, id},
	}
	m.Function = &wasm.SectionFunctions{
		Types: []uint32{0},
	}

	m.FunctionIndexSpace = []wasm.Function{
		{
			Sig:  &env,
			Body: &fb,
		},
		{
			Sig: &wasm.FunctionSig{
				ParamTypes:  []wasm.ValueType{wasm.ValueTypeI64, wasm.ValueTypeI32, wasm.ValueTypeI32},
				ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
			},
			Host: reflect.ValueOf(host.Select),
		},
		{
			Sig: &wasm.FunctionSig{
				ParamTypes:  []wasm.ValueType{wasm.ValueTypeI64, wasm.ValueTypeI32, wasm.ValueTypeI32},
				ReturnTypes: []wasm.ValueType{wasm.ValueTypeI32},
			},
			Host: reflect.ValueOf(host.TestSelect),
		},
		{
			Sig: &wasm.FunctionSig{
				ParamTypes:  []wasm.ValueType{wasm.ValueTypeI32, wasm.ValueTypeI32},
				ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
			},
			Host: reflect.ValueOf(host.LoadIdent),
		},
		{
			Sig: &wasm.FunctionSig{
				ParamTypes:  []wasm.ValueType{wasm.ValueTypeI32, wasm.ValueTypeI32},
				ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
			},
			Host: reflect.ValueOf(host.StoreS),
		},
		{
			Sig: &wasm.FunctionSig{
				ParamTypes:  []wasm.ValueType{wasm.ValueTypeI64},
				ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
			},
			Host: reflect.ValueOf(host.LoadI64),
		},
		{
			Sig: &wasm.FunctionSig{
				ParamTypes:  []wasm.ValueType{wasm.ValueTypeI64},
				ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
			},
			Host: reflect.ValueOf(host.StoreI64),
		},
		{
			Sig: &wasm.FunctionSig{
				ParamTypes:  []wasm.ValueType{wasm.ValueTypeI32, wasm.ValueTypeI32, wasm.ValueTypeI64},
				ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
			},
			Host: reflect.ValueOf(host.Invoke1),
		},
		{
			Sig: &wasm.FunctionSig{
				ParamTypes:  []wasm.ValueType{wasm.ValueTypeI32, wasm.ValueTypeI32, wasm.ValueTypeI64, wasm.ValueTypeI64},
				ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
			},
			Host: reflect.ValueOf(host.Invoke2),
		},
	}

	m.Code = &wasm.SectionCode{
		Bodies: []wasm.FunctionBody{fb},
	}

	m.Memory = &wasm.SectionMemories{
		Entries: []wasm.Memory{{Limits: wasm.ResizableLimits{Initial: 1}}},
	}
	m.LinearMemoryIndexSpace = make([][]byte, 1)

	m.Data = &wasm.SectionData{}
	for _, str := range strings {
		m.Data.Entries = append(m.Data.Entries, wasm.DataSegment{
			Offset: assemble([]disasm.Instr{do(ops.I32Const, str.off)}),
			Data:   []byte(str.val),
		})
	}

	// manually populate linear memory (function not exposed)
	for _, entry := range m.Data.Entries {
		val, err := m.ExecInitExpr(entry.Offset)
		if err != nil {
			continue
		}
		offset, ok := val.(int32)
		if !ok {
			continue
		}

		memory := m.LinearMemoryIndexSpace[int(entry.Index)]
		if int(offset)+len(entry.Data) > len(memory) {
			data := make([]byte, int(offset)+len(entry.Data))
			copy(data, memory)
			copy(data[offset:], entry.Data)
			m.LinearMemoryIndexSpace[int(entry.Index)] = data
		} else {
			copy(memory[int(offset):], entry.Data)
			m.LinearMemoryIndexSpace[int(entry.Index)] = memory
		}
	}

	return m, host
}
