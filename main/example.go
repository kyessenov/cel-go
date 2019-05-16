package main

import (
	"fmt"
	"os"
	"reflect"

	"github.com/go-interpreter/wagon/disasm"
	"github.com/go-interpreter/wagon/exec"
	"github.com/go-interpreter/wagon/wasm"

	"github.com/google/cel-go/cel"
	"github.com/google/cel-go/checker"
	gen "github.com/google/cel-go/wasm"
)

const (
	test = `true ? true && false : false`
)

func main() {
	input := test
	if len(os.Args) > 1 {
		input = os.Args[1]
	}

	env, _ := cel.NewEnv()
	parsed, iss := env.Parse(input)
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

	instrs := gen.Plan(expr)
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

	env := wasm.FunctionSig{
		Form:        0,
		ParamTypes:  []wasm.ValueType{},
		ReturnTypes: []wasm.ValueType{},
	}
	main := wasm.FunctionSig{
		Form:        0,
		ParamTypes:  []wasm.ValueType{},
		ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
	}

	// The body of the start function, that should only
	// call the host function
	fb := wasm.FunctionBody{
		Module: m,
		Locals: []wasm.LocalEntry{},
		Code:   code,
	}

	m.FunctionIndexSpace = []wasm.Function{
		{
			Sig:  &main,
			Body: &fb,
		},
		{
			Sig:  &env,
			Host: reflect.ValueOf(testHostFunction),
		},
	}
	m.Code = &wasm.SectionCode{
		Bodies: []wasm.FunctionBody{fb},
	}

	return m
}
