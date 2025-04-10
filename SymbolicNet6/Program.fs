namespace MathNet.Symbolics
module Program =
    open Definition

    printfn "%A" <| SymbolicExpression(Infix.parseOrThrow("x")).Evaluate(dict ["x", FloatingPoint.Real 2.0])

    let _ =
        define "mx3" ([Symbol "cmid"; Symbol "pos"],
            SymbolicExpression.XParse "(cmid+5+ scale* (pos + 5)) + vec(1,2)") 
            //SymbolicExpression.XParse "vec(cmid+5, scale, pos + 5)") 
    let _ =
        define "mx2" ([Symbol "cmid"; Symbol "pos"],
            SymbolicExpression.XParse "vec(cmid+5, scale, pos + 5)") 

    printfn "%A" <| SymbolicExpression.Parse("mx2(1, 3)").Evaluate(dict ["scale", MathNet.Symbolics.FloatingPoint.Real 99.0])
    printfn "%A" <| SymbolicExpression.Parse("mx3(1, 3)").Evaluate(dict ["scale", MathNet.Symbolics.FloatingPoint.Real 99.0])
