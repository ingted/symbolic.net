#if INTERACTIVE
#r "nuget: Unquote, 7.0.1"
#load "TestCore.fsx"
#I @"G:\coldfar_py\coldfar-symbolics\SymbolicNet6\bin\Debug\net9.0\"
#r @"SymbolicNet6.dll"
#r @"G:\coldfar_py\coldfar-symbolics\scripts\FsProfiler\FsProfiler.dll"
#r @"MathNet.Numerics.dll"
#r @"nuget:FsUnit"
#r @"nuget:FParsec"
#r @"nuget:MathNet.Numerics.FSharp"
#r "nuget: DiffSharp.Core, 1.0.7"
#r "nuget: DiffSharp.Backends.Reference, 1.0.7"
#r "nuget: DiffSharp.Backends.Torch, 1.0.7"
#r @"..\..\..\實驗\SharFTrade.Exp\bin2\net9.0\protobuf-net.Core.dll"

#endif
open TestCore
open MathNet.Symbolics
open Definition
open MathNet.Numerics.LinearAlgebra
open FAkka.Microsoft.FSharp.Core.LeveledPrintf

let vec (s: 'T seq) = Vector<'T>.Build.DenseOfEnumerable s


let forcePrint = 2

let _ =
    define "mx2" ([Symbol "cmid"; Symbol "pos"],
        SymbolicExpression.XParse "vec(cmid+5, scale, pos + 5)") 
let _ =
    define "mx3" ([Symbol "cmid"; Symbol "pos"],
        SymbolicExpression.XParse "(cmid+5+ scale* (pos + 5)) + vec(1,2+pos)")

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
    define "dup0" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "x + y")

let _ =
    define "dup0_" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "x + y")

let _ =
    define "dup00" ([Symbol "x"; Symbol "z"],
        SymbolicExpression.XParse "x + 11 * z")

let _ =
    define "dup1" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "dup0(x+1,y*2)")
let _ =
    define "dup2" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "dup0(x+1,y*dup0_(x+1,y*2))")

let _ = defAct "hi" (fun () -> printfn "hi")

let _ =
    define "dup3" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "x + y * dup00(x, y) + z")
let _ =
    define "dup4" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "dup3(x+1,y*2)")

let _ =
    define "mx4" ([Symbol "cmid"; Symbol "pos"; Symbol "scale"],
        SymbolicExpression.XParse "vec(cmid, scale, pos)") 
let _ =
    define "mx5" ([Symbol "cmid"; Symbol "pos"],
        SymbolicExpression.XParse "(cmid + scale * pos) + mx4(2,3,5)")

let _ =
    define "mx6" ([Symbol "cmid"; Symbol "pos"],
        SymbolicExpression.XParse "vec(cmid, scale, pos)") 
let _ =
    define "mx7" ([Symbol "cmid"; Symbol "pos"; Symbol "scale"],
        SymbolicExpression.XParse "(cmid + scale * pos) + mx6(2,3)")


let _ =
    define "mx9" ([Symbol "x"],
        SymbolicExpression.XParse "x * 2") 
let _ =
    define "mx91" ([Symbol "x"],
        SymbolicExpression.XParse "x1 * 2") 
let _ =
    define "mx10" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "mx9(x) + y")
let _ =
    define "mx101" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "mx91(x) + y")

let _ =
    define "mx11" ([Symbol "x"; Symbol "y"; Symbol "z"],
        SymbolicExpression.XParse "mx10(x,y) + mx9(z)")

let _ =
    define "mx111" ([Symbol "x"; Symbol "y"; Symbol "z"],
        SymbolicExpression.XParse "mx101(x,y) + mx91(z)")

//let whileImpl (globalContext: GlobalContext) (scopedContext: ScopedContext option) (prevOutput: FloatingPoint) (currentContext: ScopedContext) : FloatingPoint =
//    match prevOutput with
//    | NestedList [condition; body] ->
//        // 從NestedList中提取條件和循環體
//        let rec loop lastResult =
//            // 評估條件
//            let condResult = 
//                match condition with
//                | NestedExpr condExpr ->
//                    // 評估條件表達式
//                    let result = condExpr |> List.map (fun expr -> 
//                        MathNet.Symbolics.Evaluate.evaluate2 (globalContext, Some (currentContext :> IDictionary<string, FloatingPoint>)) expr)
//                    // 取最後一個結果
//                    List.last result
//                | _ -> failwith "While: Condition must be an expression"
        
//            // 檢查條件是否為真
//            match condResult with
//            | FloatingPoint.Real value when value <> 0.0 ->
//                // 條件為真，評估循環體
//                let bodyResult = 
//                    match body with
//                    | NestedExpr bodyExpr ->
//                        // 評估循環體表達式
//                        let result = bodyExpr |> List.map (fun expr -> 
//                            MathNet.Symbolics.Evaluate.evaluate2 (globalContext, Some (currentContext :> IDictionary<string, FloatingPoint>)) expr)
//                        // 取最後一個結果
//                        List.last result
//                    | _ -> failwith "While: Body must be an expression"
            
//                // 繼續循環
//                loop bodyResult
//            | _ ->
//                // 條件為假，返回最後的結果
//                lastResult
    
//        // 開始循環，初始結果為Undef
//        loop Undef
//    | _ -> failwith "While: Expected NestedList with condition and body"


open FAkka.Microsoft.FSharp.Core.LeveledPrintf
//改 PTRACE 可以 SHOW 計算細節
//printLevelSet PRINTLEVEL.PTRACE
//printLevelSet PRINTLEVEL.PWARN
printLevelSet PRINTLEVEL.PERROR

//SymbolicExpression.Parse("mx7(7,vec(9,11,13),vec(0,0,0))").Evaluate(dict ["scale", FloatingPoint.Real -17.0])

//TestCore.testIdFilter <- Some [|10|]
//TestCore.testIdFilter <- Some [|5;51;6;61|]
//TestCore.testIdFilter <- Some [|5;6;602;603|]
//TestCore.testIdFilter <- Some [|603|]

TestCore.testIdFilterOut <- Some [|32; 42; 52; 62|]

[
    test 1 forcePrint (<@ fun () -> 
                        let expr = SymbolicExpression.Parse("u.*v")
                        let env = 
                            dict [
                                "u", FloatingPoint.RealVector (vector [10.0; 20.0; 30.0])
                                "v", FloatingPoint.RealVector (vector [10.0; 20.0; 30.0])
                            ]

                        let expr, cmpl = Compile.compileExpressionOrThrow2 expr.Expression [Symbol "u"; Symbol "v"]

                        //printfn "compiled method = %A" cmpl.Method
                        //printfn "param count = %d" (cmpl.Method.GetParameters().Length)
                        let paramCount = cmpl.Method.GetParameters().Length

                        //cmpl.DynamicInvoke([|env["u"];env["v"]|]) //會造成參數個數判斷錯誤
                        paramCount, unbox<Value> <| cmpl.DynamicInvoke([| box env["u"]; box env["v"] |])                                                  @>) (3, Value.RealVec (vec [100.0; 400.0; 900.0]))
    test 2 forcePrint (<@ fun () -> SymbolicExpression.Parse("(u.*(v + 1)+2) * 2").Evaluate(dict [
        "u", FloatingPoint.RealVector (vector [10.0; 20.0; 30.0])
        "v", FloatingPoint.RealVector (vector [10.0; 20.0; 30.0])
    ])                                                                                                                                                    @>) (RealVector (vec [224.0; 844.0; 1864.0]))
    test 3 forcePrint (<@ fun () -> SymbolicExpression.Parse("dup4(7,8)").Evaluate(dict ["z", FloatingPoint.Real -8.0])                                   @>) (FloatingPoint.Real 2944.0)
    test 4 forcePrint (<@ fun () -> SymbolicExpression.Parse("dup4(7,8)").Evaluate(dict ["z", FloatingPoint.Real 8.0])                                    @>) (FloatingPoint.Real 2960.0)
    //test 32 forcePrint (<@ fun () -> SymbolicExpression.Parse("dup4(7,8)").EvaluateMode0(dict ["z", FloatingPoint.Real -8.0])                             @>) (FloatingPoint.Real -1280.0)
    //test 42 forcePrint (<@ fun () -> SymbolicExpression.Parse("dup4(7,8)").EvaluateMode0(dict ["z", FloatingPoint.Real 8.0])                              @>) (FloatingPoint.Real 1552.0)
    test 5 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx7(7,vec(9,11,13),19)").Evaluate(dict ["scale", FloatingPoint.Real 5.0])                   @>) (RealVector (vec [180.0; 221.0; 257.0]))
    test 6 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx7(7,vec(9,11,13),19)").Evaluate(dict ["scale", FloatingPoint.Real -17.0])                 @>) (RealVector (vec [180.0; 199.0; 257.0]))
    test 602 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx11(2,3,5)").Evaluate(dict ["x", FloatingPoint.Real -100.0; 
                                                                                             "y", FloatingPoint.Real -10000.0; 
                                                                                             "z", FloatingPoint.Real -1000000.0])                         @>) (FloatingPoint.Real 17.0)
                                                                                             
                                                                                             //函數參數無x1，會自動從 symbol value 取
    test 603 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx111(2,3,5)").Evaluate(dict ["x1", FloatingPoint.Real -100.0; 
                                                                                             //函數參數有 x 則在不缺的情況下不使用
                                                                                             "y", FloatingPoint.Real -10000.0; 
                                                                                             "z", FloatingPoint.Real -1000000.0])                         @>) (FloatingPoint.Real -397.0)
    
    test 51 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx7(7,vec(9,11,13),19)").EvaluateCorrect(dict ["scale", FloatingPoint.Real 5.0])           @>) (RealVector (vec [180.0; 221.0; 257.0]))
    test 61 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx7(7,vec(9,11,13),19)").EvaluateCorrect(dict ["scale", FloatingPoint.Real -17.0])         @>) (RealVector (vec [180.0; 199.0; 257.0]))
    test 612 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx11(2,3,5)").EvaluateCorrect(dict ["x", FloatingPoint.Real -100.0; 
                                                                                                    "y", FloatingPoint.Real -10000.0; 
                                                                                                    "z", FloatingPoint.Real -1000000.0])                  @>) (FloatingPoint.Real 17.0)
    test 613 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx111(2,3,5)").EvaluateCorrect(dict ["x1", FloatingPoint.Real -100.0; 
                                                                                                     "y", FloatingPoint.Real -10000.0; 
                                                                                                     "z", FloatingPoint.Real -1000000.0])                 @>) (FloatingPoint.Real -397.0)

    //test 52 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx7(7,vec(9,11,13),19)").EvaluateMode0(dict ["scale", FloatingPoint.Real 5.0])             @>) (RealVector (vec [180.0; 235.0; 257.0]))
    //test 62 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx7(7,vec(9,11,13),19)").EvaluateMode0(dict ["scale", FloatingPoint.Real -17.0])           @>) (RealVector (vec [180.0; 235.0; 257.0]))
    test 7 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx5(7,vec(9,11,13))").Evaluate(dict ["scale", FloatingPoint.Real -8.0])                     @>) (RealVector (vec [-63.0; -76.0; -94.0]))
    test 8 forcePrint (<@ fun () -> SymbolicExpression.Parse("hi()").Evaluate(dict [])                                                                    @>) Undef
    test 9 forcePrint (<@ fun () -> SymbolicExpression.Parse("dup1(7,8)").Evaluate(dict [])                                                               @>) (FloatingPoint.Real 24.0)
    test 10 forcePrint (<@ fun () -> SymbolicExpression.Parse("dup2(7,8)").Evaluate(dict [])                                                              @>) (FloatingPoint.Real 200.0)
    test 11 forcePrint (<@ fun () -> " "                                                                                                                  @>) " "
    test 12 forcePrint (<@ fun () -> 2                                                                                                                    @>) 2
    test 13 forcePrint (<@ fun () -> SymbolicExpression(Infix.parseOrThrow("x")).Evaluate(dict ["x", FloatingPoint.Real 2.0])                             @>) (FloatingPoint.Real 2.0)
    test 14 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx2(1, 3)").Evaluate(dict ["scale", MathNet.Symbolics.FloatingPoint.Real 99.0])            @>) (RealVector (vec [6.0; 99.0; 8.0]))
    test 15 forcePrint (<@ fun () -> SymbolicExpression.Parse("mx3(1, 3)").Evaluate(dict ["scale", MathNet.Symbolics.FloatingPoint.Real 99.0])            @>) (RealVector (vec [799.0; 803.0]))
    test 16 forcePrint (<@ fun () -> SymbolicExpression.Parse("ma_base(0.0, 30.0, 1.0)").Evaluate(dict ["cur", MathNet.Symbolics.FloatingPoint.Real 9.0]) @>) (RealVector (vec [1.5; 2.5; 14.5]))

    
    
]
|> fun l ->
    let ll = l |> List.indexed |> List.choose (fun (i, vo) -> vo |> Option.map (fun (b, e) ->  i, b, e))
    let failed = ll |> List.tryFind (fun (i, r, f) -> not r)
    if failed.IsSome then
        ll 
        |> List.find (fun (i,r,f) ->
            let (j ,_, _) = failed.Value 
            j = i
        )
        |> fun (i,r,f) ->
            printfn "================================="
            testBody f |> printfn "%s"