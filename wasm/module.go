package wasm

import (
	"reflect"

	"github.com/go-interpreter/wagon/disasm"
	"github.com/go-interpreter/wagon/exec"
	"github.com/go-interpreter/wagon/wasm"

	exprpb "google.golang.org/genproto/googleapis/api/expr/v1alpha1"
)

// host call management from wasm

func assemble(instrs []disasm.Instr) []byte {
	out, err := disasm.Assemble(instrs)
	if err != nil {
		panic(err)
	}
	return out
}

type HostFunctions struct {
	Values map[string]interface{}
}

func (host *HostFunctions) Ident(id *Ident) func(proc *exec.Process) int64 {
	return func(proc *exec.Process) int64 {
		switch v := id.typ.TypeKind.(type) {
		case *exprpb.Type_Primitive:
			switch v.Primitive {
			case exprpb.Type_INT64:
				out, _ := host.Values[id.val].(int64)
				return out

				// TODO: manage other types
			}
		}
		return 1
	}
}

func MakeModule(instrs []disasm.Instr, idents []*Ident) (*wasm.Module, *HostFunctions) {
	m := wasm.NewModule()
	host := &HostFunctions{}

	// stop main invocation that drops the value
	m.Start = nil

	env := wasm.FunctionSig{
		Form:        0,
		ParamTypes:  []wasm.ValueType{},
		ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
	}

	// The body of the start function, that should only
	// call the host function
	fb := wasm.FunctionBody{
		Module: m,
		Locals: []wasm.LocalEntry{},
		Code:   assemble(instrs),
	}

	m.FunctionIndexSpace = []wasm.Function{
		{
			Sig:  &env,
			Body: &fb,
		},
	}

	for _, id := range idents {
		m.FunctionIndexSpace = append(m.FunctionIndexSpace, wasm.Function{
			Sig:  &env,
			Host: reflect.ValueOf(host.Ident(id)),
		})
	}

	m.Code = &wasm.SectionCode{
		Bodies: []wasm.FunctionBody{fb},
	}

	return m, host
}
