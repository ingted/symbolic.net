namespace MathNet.Symbolics
module Program =
    open Definition
    let _ =
        define "mx2" ([Symbol "cmid"; Symbol "pos"],
            SymbolicExpression.XParse "vec(cmid+5, scale, pos + 5)") 


    printfn "%A" <| SymbolicExpression.Parse("mx2(1, 3)").Evaluate(dict ["scale", MathNet.Symbolics.FloatingPoint.Real 99.0])
