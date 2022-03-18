// Learn more about F# at http://fsharp.org

open System
open MathNet.Numerics.LinearAlgebra
open MathNet.Symbolics
open Definition
open Operators
open VariableSets.Alphabet

let V = FloatingPoint.RealVector <| vector[1.0;2.0;3.0]

let M = FloatingPoint.RealMatrix <|
        matrix [[3.0; 0.0; 0.0]
                [1.0; 2.0; 0.0]
                [0.0; 1.0; 4.0]]

let symbols2 = dict[ "a", V; "m", M ]


type A = {
    trivial: bool
}


[<EntryPoint>]
let main argv =
    let a0 = SymbolicExpression(Infix.parseOrThrow("a * 2")).Evaluate(symbols2)
    printfn "%A" a0.RealVectorValue
    let a1 = SymbolicExpression(Infix.parseOrThrow("a + 1")).Evaluate(symbols2)
    printfn "%A" a1.RealVectorValue
    let a2 = SymbolicExpression(Infix.parseOrThrow("mat_by_row(a, a)")).Evaluate(symbols2)
    printfn "%A" a2.RealMatrixValue
    let a3 = SymbolicExpression(Infix.parseOrThrow("mat_by_col(a, a)")).Evaluate(symbols2)
    printfn "%A" a3.RealMatrixValue
    let a4 = SymbolicExpression(Infix.parseOrThrow("mat_multiply(m, mat_by_col(a, vec(1.0,2.0,3.0), a), a)")).Evaluate(symbols2)
    printfn "%A" a4

    cFun ("mat_by_row", []) |> ignore

    let symV = Symbol "v"
    let symW = Symbol "w"
    let syml = dict[ "x", FloatingPoint.Real 9.0; ]
    let _ = define "t0" ([symV; symW], (v + w))
    printfn "t0: %A" <| SymbolicExpression(cFun("t0", [x; x])).Evaluate(syml)
    let _ = define "t1" ([symV; symW], Infix.parseOrThrow("t0(v, w)"))
    printfn "2 * t1(x, t1(x, x)) / t1(2 * x, x) * 4: %A" <| SymbolicExpression.Parse("2 * t1(x, t1(x, x)) / t1(2 * x, x) * 4").Evaluate(syml)
    let _ = define "t2" ([symV; symW], Infix.parseOrThrow("2 * t0(v, w) / 3"))
    printfn "2 * t2(x, x) / 3 + t2(x, x * 2): %A" <| SymbolicExpression.Parse("2 * t2(x, x) / 3 + t2(x, x * 2)").Evaluate(syml)
    printfn "t1(x, 2 * t0(x,x)): %A" <| SymbolicExpression(cFun("t1", [x; 2 * cFun("t0", [x; x])])).Evaluate(syml)
    printfn "t1(x, 2 * t1(x,x)): %A" <| SymbolicExpression(cFun("t1", [x; 2 * cFun("t1", [x; x])])).Evaluate(syml)
    printfn "t0(x, t0(x, x) * 2): %A" <| SymbolicExpression(cFun("t0", [x; cFun("t0", [x; x]) * 2])).Evaluate(syml)
    printfn "t0(x, t1(x, x) * 2): %A" <| SymbolicExpression(cFun("t0", [x; cFun("t1", [x; x]) * 2])).Evaluate(syml)

    let a5 = SymbolicExpression(Infix.parseOrThrow("2 * mat_multiply(m, mat_by_col(a, vec(1.0,2.0,3.0), a), a)")).Evaluate(symbols2)
    printfn "%A" a5

    let a6 = SymbolicExpression.Parse("2 * htensor(lo(lo(lo(vec(1,2,3), vec(4,5,6)), lo(vec(7,8,9), vec(10,11,12)))))").Evaluate(symbols2)
    printfn "%A" a6
    0 // return an integer exit code
