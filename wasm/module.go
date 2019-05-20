package wasm

import (
	"reflect"

	"github.com/go-interpreter/wagon/disasm"
	"github.com/go-interpreter/wagon/exec"
	"github.com/go-interpreter/wagon/wasm"
	ops "github.com/go-interpreter/wagon/wasm/operators"
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
	LoadI64
	StoreS
	Invoke2
	MapSize
	StringSize
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
	Values map[string]interface{}
	Heap   []interface{}
}

func (host *HostFunctions) LoadI64(proc *exec.Process, o, l int32) int64 {
	s := make([]byte, l)
	proc.ReadAt(s, int64(o))

	val, ok := host.Values[string(s)]
	if !ok {
		return 0
	}

	switch out := val.(type) {
	case int64:
		return out
	default:
		host.Heap = append(host.Heap, val)
		return int64(len(host.Heap))
		// TODO: manage other primitive types
	}
}

func (host *HostFunctions) StoreS(proc *exec.Process, o, l int32) int64 {
	s := make([]byte, l)
	proc.ReadAt(s, int64(o))
	host.Heap = append(host.Heap, string(s))
	return int64(len(host.Heap))
}

// TODO: need to realize an error value on the heap
func (host *HostFunctions) Invoke2(proc *exec.Process, a0, a1 int64) int64 {
	arg0 := host.Heap[a0]
	arg1 := host.Heap[a1]
	_ = arg0
	_ = arg1
	return 0
}

func (host *HostFunctions) Select(proc *exec.Process, h int64, o, l int32) int64 {
	if h <= 0 || h > int64(len(host.Heap)) {
		// cannot find heap object
		return 0
	}
	rcv := host.Heap[h-1]
	m, ok := rcv.(map[string]string)
	if !ok {
		return 0
	}

	s := make([]byte, l)
	proc.ReadAt(s, int64(o))
	val := m[string(s)]
	host.Heap = append(host.Heap, val)
	return int64(len(host.Heap))
}

func (host *HostFunctions) TestSelect(proc *exec.Process, h int64, o, l int32) int32 {
	if h <= 0 || h > int64(len(host.Heap)) {
		// cannot find heap object
		return 0
	}
	rcv := host.Heap[h-1]
	m, ok := rcv.(map[string]string)
	if !ok {
		return 0
	}

	s := make([]byte, l)
	proc.ReadAt(s, int64(o))
	_, ok = m[string(s)]
	if ok {
		return 1
	} else {
		return 0
	}
}

func (host *HostFunctions) MapSize(proc *exec.Process, h int64) int64 {
	if h <= 0 || h > int64(len(host.Heap)) {
		return 0
	}
	val := host.Heap[h-1]
	ref := reflect.ValueOf(val)
	if ref.Kind() == reflect.Map {
		return int64(ref.Len())
	}
	return 0
}

func (host *HostFunctions) StringSize(proc *exec.Process, h int64) int64 {
	if h <= 0 || h > int64(len(host.Heap)) {
		return 0
	}
	val := host.Heap[h-1]
	out, ok := val.(string)
	if ok {
		return int64(len(out))
	}
	return 0
}

func MakeModule(instrs []disasm.Instr, strings map[string]*String) (*wasm.Module, *HostFunctions) {
	m := wasm.NewModule()
	host := &HostFunctions{}

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
			Host: reflect.ValueOf(host.LoadI64),
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
				ParamTypes:  []wasm.ValueType{wasm.ValueTypeI64, wasm.ValueTypeI64},
				ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
			},
			Host: reflect.ValueOf(host.StoreS),
		},
		{
			Sig:  &id,
			Host: reflect.ValueOf(host.MapSize),
		},
		{
			Sig:  &id,
			Host: reflect.ValueOf(host.StringSize),
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
