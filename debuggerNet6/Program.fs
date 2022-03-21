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

let symbols2 = dict[ "v", V; "m", M ]


type A = {
    trivial: bool
}


[<EntryPoint>]
let main argv =
    let a0 = SymbolicExpression(Infix.parseOrThrow("v * 2")).Evaluate(symbols2)
    printfn "%A" a0.RealVectorValue
    let a1 = SymbolicExpression(Infix.parseOrThrow("v + 1")).Evaluate(symbols2)
    printfn "%A" a1.RealVectorValue
    let a2 = SymbolicExpression(Infix.parseOrThrow("mat_by_row(v, v)")).Evaluate(symbols2)
    printfn "%A" a2.RealMatrixValue
    let a3 = SymbolicExpression(Infix.parseOrThrow("mat_by_col(v, v)")).Evaluate(symbols2)
    printfn "a3: %A" a3.RealMatrixValue
    let a4 = SymbolicExpression(Infix.parseOrThrow("mat_multiply(m, mat_by_col(v, vec(1.0,2.0,3.0), v), v)")).Evaluate(symbols2)
    printfn "a4: %A" a4

    cFun ("mat_by_row", []) |> ignore

    let symV = Symbol "v"
    let symW = Symbol "w"
    
    let symV1 = Symbol "v1"
    let symW1 = Symbol "w1"
    let symV2 = Symbol "v2"
    let symW2 = Symbol "w2"
    let symX = Symbol "x"
    let syml = dict [ "x", FloatingPoint.Real 9.0; ]
    let _ = define "t0" ([symV; symW], (v + w))
    let _ = define "t1" ([symV; symW], Infix.parseOrThrow("t0(v, w)"))
    let _ = define "t2" ([symV; symW], Infix.parseOrThrow("2 * t0(v, w) / 3"))

    let lambdaExp =
        try
            MathNet.Symbolics.Linq.formatLambda (cFun("t0", [x; x])) [symV; symW] //intensive error
        with
        | _ -> None

    printfn "t0: %A" <| SymbolicExpression(cFun("t0", [x; x])).Evaluate(syml)
    printfn "t0-2: %A" <| SymbolicExpression.Parse("1 + t0(x, x)").Evaluate(syml)
    printfn "2 * t1(x, t1(x, x)) / t1(2 * x, x) * 4: %A" <| SymbolicExpression.Parse("2 * t1(x, t1(x, x)) / t1(2 * x, x) * 4").Evaluate(syml)

    let infix2 = Infix.parseOrThrow("2 * t0(v1, w1) / 3")
    let lambdaExp2 =
        try
            MathNet.Symbolics.Linq.formatLambda infix2 [symV2; symW2]  //intensive error
        with
        | _ -> None

    let infix3_0 = Infix.parseOrThrow("t0(x, x)")
    let infix3_1 = Infix.parseOrThrow("t1(x, x)")
    let infix3_2 = Infix.parseOrThrow("t2(x, x * 2)")
    let infix3 = Infix.parseOrThrow("2 * t2(x, x) / 3 + t2(x, x * 2)")


    let (Some lambdaExp3_0) = MathNet.Symbolics.Linq.formatLambda infix3_0 [symX]
    let (Some lambdaExp3_2) = MathNet.Symbolics.Linq.formatLambda infix3_2 [symX]
    let (Some lambdaExp3) = MathNet.Symbolics.Linq.formatLambda infix3 [symX]

    let toEvaluate = SymbolicExpression.Parse("2 * t2(x, x) / 3 + t2(x, x * 2)")
    let (Some toLambda) = MathNet.Symbolics.Linq.formatLambda toEvaluate.Expression [symX]

    printfn "2 * t2(x, x) / 3 + t2(x, x * 2): %A" <| toEvaluate.Evaluate(syml)
    printfn "t1(x, 2 * t0(x,x)): %A" <| SymbolicExpression(cFun("t1", [x; 2 * cFun("t0", [x; x])])).Evaluate(syml)
    printfn "t1(x, 2 * t1(x,x)): %A" <| SymbolicExpression(cFun("t1", [x; 2 * cFun("t1", [x; x])])).Evaluate(syml)
    printfn "t0(x, t0(x, x) * 2): %A" <| SymbolicExpression(cFun("t0", [x; cFun("t0", [x; x]) * 2])).Evaluate(syml)
    printfn "t0(x, t1(x, x) * 2): %A" <| SymbolicExpression(cFun("t0", [x; cFun("t1", [x; x]) * 2])).Evaluate(syml)

    let a5 = SymbolicExpression(Infix.parseOrThrow("2 * mat_multiply(m, mat_by_col(v, vec(1.0,2.0,3.0), v), v)")).Evaluate(symbols2)
    printfn "a5: %A" a5

    let a6 = SymbolicExpression.Parse("2 * htensor(lo(lo(lo(vec(1,2,3), vec(4,5,6)), lo(vec(7,8,9), vec(10,11,12)))))").Evaluate(symbols2)
    printfn "a6:%A" a6

    let a7expr = SymbolicExpression.Parse("t0(1, 2 * htensor(lo(lo(lo(vec(1,2,3), vec(4,5,6)), lo(vec(7,8,9), vec(10,11,12))))))")
    let a7 = a7expr.Evaluate(symbols2)
    printfn "a7:%A" a7

    0 // return an integer exit code
