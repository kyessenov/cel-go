package main

import (
	"fmt"
	"reflect"

	"github.com/go-interpreter/wagon/disasm"
	"github.com/go-interpreter/wagon/exec"
	"github.com/go-interpreter/wagon/wasm"

	"github.com/google/cel-go/cel"
	"github.com/google/cel-go/checker"
	gen "github.com/google/cel-go/wasm"
)

const (
	test = `true`
)

func main() {
	env, _ := cel.NewEnv()
	parsed, iss := env.Parse(test)
	if iss != nil {
		panic(iss.Err())
	}
	checked, iss := env.Check(parsed)
	if iss != nil {
		panic(iss.Err())
	}
	expr, _ := cel.AstToCheckedExpr(checked)
	fmt.Printf("checked %s\n", checker.Print(expr.Expr, expr))
	prg, _ := env.Program(checked)
	out, _, _ := prg.Eval(map[string]interface{}{})
	fmt.Printf("CEL value: %v\n", out)

	instrs, err := gen.Plan(expr)
	if err != nil {
		panic(err)
	}
	module := makeModule(assemble(instrs))
	vm, err := exec.NewVM(module)
	if err != nil {
		panic(err)
	}
	o, err := vm.ExecCode(0)
	if err != nil {
		panic(err)
	}
	fmt.Printf("WASM value: %v\n", o)
}

func assemble(instrs []disasm.Instr) []byte {
	out, err := disasm.Assemble(instrs)
	if err != nil {
		panic(err)
	}
	return out
}

// a host function that can be called by WASM code.
func testHostFunction(proc *exec.Process) {
	fmt.Println("executing host function")
}

func makeModule(code []byte) *wasm.Module {
	m := wasm.NewModule()

	fsig := wasm.FunctionSig{
		Form:        0,
		ParamTypes:  []wasm.ValueType{},
		ReturnTypes: []wasm.ValueType{},
	}
	fsig1 := wasm.FunctionSig{
		Form:        0,
		ParamTypes:  []wasm.ValueType{},
		ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
	}

	// List of all function types available in this module.
	// There is only one: (func [] -> [])
	m.Types = &wasm.SectionTypes{
		Entries: []wasm.FunctionSig{
			fsig1,
			fsig,
		},
	}

	m.Function = &wasm.SectionFunctions{
		Types: []uint32{1, 0},
	}

	// The body of the start function, that should only
	// call the host function
	fb := wasm.FunctionBody{
		Module: m,
		Locals: []wasm.LocalEntry{},
		// code should disassemble to:
		// call 1 (which is host)
		// end
		Code: code,
	}

	// There was no call to `ReadModule` so this part emulates
	// how the module object would look like if the function
	// had been called.
	m.FunctionIndexSpace = []wasm.Function{
		{
			Sig:  &fsig1,
			Body: &fb,
		},
		{
			Sig:  &fsig,
			Host: reflect.ValueOf(testHostFunction),
		},
	}

	m.Code = &wasm.SectionCode{
		Bodies: []wasm.FunctionBody{fb},
	}

	return m
}
