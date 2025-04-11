namespace MathNet.Symbolics
module Program =
    open Definition
    open MathNet.Numerics.LinearAlgebra
    printfn "%A" <| SymbolicExpression(Infix.parseOrThrow("x")).Evaluate(dict ["x", FloatingPoint.Real 2.0])

    let _ =
        cur3fto1v "ma_base" ((
            fun cur cmid scale pos -> //vector [1.0;2;3]
                printfn "cur => %A" cur //cur = 0 是用來表示"當根"
                if scale = 30.0 || cmid <> 0 then //ES連續月目前以 0 表示
                    vector [1.5; 2.5; 3.5 + float cur + pos * 2.0]
                else
                    failwithf "scale not supported"
                        
            ), Symbol "cur")

    let _ =
        define "ma" ([Symbol "cmid"; Symbol "scale"; Symbol "pos"],
            SymbolicExpression.XParse "5 * ma_base(cmid, scale, pos + 1)")

    let _ =
        define "mx3" ([Symbol "cmid"; Symbol "pos"],
            SymbolicExpression.XParse "(cmid+5+ scale* (pos + 5)) + vec(1,2)") 
            //SymbolicExpression.XParse "vec(cmid+5, scale, pos + 5)") 
    let _ =
        define "mx2" ([Symbol "cmid"; Symbol "pos"],
            SymbolicExpression.XParse "vec(cmid+5, scale, pos + 5)") 

    printfn "%A" <| SymbolicExpression.Parse("ma(0.0, 30.0, 1.0) + 1").Evaluate(dict ["cur", MathNet.Symbolics.FloatingPoint.Real 9.0])
    printfn "%A" <| SymbolicExpression.Parse("mx2(1, 3)").Evaluate(dict ["scale", MathNet.Symbolics.FloatingPoint.Real 99.0])
    printfn "%A" <| SymbolicExpression.Parse("mx3(1, 3)").Evaluate(dict ["scale", MathNet.Symbolics.FloatingPoint.Real 99.0])
