// Learn more about F# at http://fsharp.org

open System
open MathNet.Numerics.LinearAlgebra
open MathNet.Symbolics
let v = FloatingPoint.RealVector <| vector[1.0;2.0;3.0]

let M = FloatingPoint.RealMatrix <|
        matrix [[3.0; 0.0; 0.0]
                [1.0; 2.0; 0.0]
                [0.0; 1.0; 4.0]]

let symbols2 = dict[ "a", v; "m", M ]


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
    0 // return an integer exit code
