#if INTERACTIVE
#r @"..\bin\net9.0\SymbolicNet6.dll"
#r @"nuget:MathNet.Numerics, 6.0.0-beta1"
#r @"nuget:FsUnit"
#r @"nuget:FParsec"
#r @"nuget:MathNet.Numerics.FSharp, 6.0.0-beta1"
#r @"nuget:PersistedConcurrentSortedList"
#r @"nuget:FAkka.Deedle"
#load @"..\..\SymbolicNet6.Test\Global.fs"

#r "nuget: DiffSharp.Core, 1.0.7"
#r "nuget: DiffSharp-cpu, 1.0.7"
#r "nuget: DiffSharp.Backends.Reference, 1.0.7"
#r "nuget: DiffSharp.Backends.Torch, 1.0.7"
#endif

open MathNet.Numerics
open MathNet.Symbolics
open Global
open Operators
open VariableSets.Alphabet
type Expr = SymbolicExpression
open Definition
open Evaluate

type SCD = | S of CD<int, int>

let cdInS = CD<int, int>(dict [123, 456])
let scd = S cdInS

cdInS.TryAdd (456, 789)


(SymbolicExpression.Parse "(ttc)").Evaluate(dict ["ttc", FloatingPoint.Real 123.0])
(SymbolicExpression.Parse "str(ttc)").Evaluate(dict ["ttc", FloatingPoint.Real 123.0])

Evaluate.IF_PRECISE <- true

let (BR ff) = (SymbolicExpression.Parse "(a + 1)^(x^(y * 2))").Evaluate(dict ["a", FloatingPoint.Real 2.0; "x", FloatingPoint.Real 3.0; "y", FloatingPoint.Real 4.0;])

let (Number n) = pow 3N (pow 3N 8N)

ff=n

let symV = Symbol "v"
let symW = Symbol "w"
let symX = Symbol "x"
let symY = Symbol "y"
let symZ = Symbol "z"

let name = Symbol "name"
let defList = Symbol "defList"
let paramList = Symbol "param"
let defCount = Symbol "defCnt"
let paramCount = Symbol "paramCnt"

let def = Symbol "def"
let defLineCount = Symbol "defLineCount"

let chk (cond) s (f) = if f <> cond then failwith s

Definition.funDict.TryRemove "len"
Definition.funDict.TryAdd ("len", (DTProc ([
    [symX], (DBFun ((fun parentScopeIdOpt procEnv symbolValues exprs ->
        let stx = procEnv.stx
        let l =
            match stx.Value.TryGetValue("x") with
            | false, _ -> 0.0
            | true, v ->
                match v with
                | NestedExpr l -> l.Length
                | NestedList l -> l.Length
                | NestedMap m -> m.Count
                | _ ->
                    failwithf "len not supported, %A" v

        let out = {
            procEnv
                with
                    prevOutput = Some (FloatingPoint.Real l)
        }
        out
    ), OutFP))
], 0, None)))


Definition.funDict.TryRemove "let"
Definition.funDict.TryAdd ("let", (DTProc ([
    [symX; symV], (DBFun ((fun parentScopeIdOpt procEnv symbolValues exprs ->
        let g = procEnv.gCtx
        let s = procEnv.sCtx
        let prevO = procEnv.prevOutput
        let stx = procEnv.stx
        let ifTop = procEnv.depth = 0
        //stx.Value.TryGetValue "x" |> printfn "%A"
        exprs.Value[0] |> printfn "exprs[0]: %A"
        exprs.Value[0].Ident.SymbolName |> printfn "exprs.Value[0].Ident.SymbolName: %A"
        printfn $"ifTop: {ifTop}"
        let stxVal_v = stx.Value.TryGetValue(symV.SymbolName) |> snd
        //effectIn[exprs.Value[0].Ident.SymbolName] <- stxVal_v
        printfn "stxId: %A" stxVal_v
        let out = {
            procEnv
                with
                    prevOutput = Some Undef
        }
        let vName = exprs.Value[0].Ident.SymbolName
        let effected =
            if ifTop then
                {out with
                    gCtx = gCtxAdd vName stxVal_v out.gCtx
                    sCtx = sCtxAdd parentScopeIdOpt vName stxVal_v out.sCtx
                    }
            else
                {out with
                    sCtx = sCtxAdd parentScopeIdOpt vName stxVal_v out.sCtx
                    }
        effected
        
    ), OutFP))
    //[symX;], (DBFun ((fun g s prevO stx exprs ifTop ->
    //    stx.Value.TryGetValue "x" |> printfn "%A"
    //    exprs.IsNone |> printfn "exprs.IsNone %A"
    //    printfn $"ifTop: {ifTop}"
    //    printfn "stxId: %A" (stx.Value.TryGetValue "stepId" |> snd)
    //    let effectIn =
    //        if ifTop then
    //            g.ctx
    //        else
    //            s.Value.ctx
    //    //effectIn["ttc"]  |> printfn "ttc: %A"
    //    Undef
    //), OutFP))
], 1, None)))


Definition.funDict.TryRemove "eval"
Definition.funDict.TryAdd ("eval", (DTProc ([
    [symX], (DBFun ((fun parentScopeIdOpt procEnv symbolValues exprs ->
        let stx = procEnv.stx
        let ifTop = procEnv.depth = 0
        printfn $"ifTop: {ifTop}"
        //printfn "symbolValues: %A" symbolValues
        //printfn "=============================="
        let stxVal_v = stx.Value.TryGetValue(symX.SymbolName) |> snd
        match stxVal_v with
        | NestedExpr l ->
            let dp = DTProc ([[], DBExp (l, OutFP)], 0, None)
            let gid = System.Guid.NewGuid().ToString().Replace("-", "")
            let rm = Definition.funDict.TryRemove gid
            let add = Definition.funDict.TryAdd (gid, dp)
            let evaluated = evaluate2 (Evaluate.IF_PRECISE, parentScopeIdOpt, symbolValues, {procEnv with stx = Some (procEnv.stx.Value |> Map.remove symX.SymbolName)}) (FunInvocation (Symbol gid, []))
            {
                evaluated.eEnv
                    with
                        prevOutput = Some evaluated.eRst
            }
        | _ ->
            failwith "Not NestedExpr to evaluate"
    ), OutFP))
], 0, None)))

(SymbolicExpression.Parse "eval(expr(x,123))").Evaluate(dict ["x", BR 1478N]) |> chk (BR 123N) "eval001 failed"
(SymbolicExpression.Parse "len(123,456)").EvaluateNoThrow(dict []) |> chk (Choice2Of2 "len not supported, BR 123N") "eval001.1 failed"
(SymbolicExpression.Parse "len(param(123,456))").Evaluate(dict []) |> chk (FloatingPoint.Real 2.0) "eval001.2 failed"
(SymbolicExpression.Parse "len(expr(123,456))").Evaluate(dict []) |> chk (FloatingPoint.Real 2.0) "eval001.3 failed"
(SymbolicExpression.Parse "len(expr(x,param(123,456)))").Evaluate(dict []) |> chk (FloatingPoint.Real 2.0) "eval001.4 failed"

(SymbolicExpression.Parse "eval(expr(x))").Evaluate(dict ["x", BR 1478N]) |> chk (BR 1478N) "eval002 failed"
(SymbolicExpression.Parse "eval(expr(x))").EvaluateNoThrow(dict []) |> chk (Choice2Of2 "Failed to find symbol x") "eval002.1 failed"

(SymbolicExpression.Parse "eval(x)").EvaluateNoThrow(dict ["x", BR 1478N]) |> chk (Choice2Of2 "Not NestedExpr to evaluate")  "eval003 failed"
(SymbolicExpression.Parse "eval(x)").EvaluateNoThrow(dict ["x", NestedExpr [Identifier (Symbol "x")]]) |> chk (Choice1Of2 (NestedExpr [Identifier (Symbol "x")]))  "eval004 failed"
(SymbolicExpression.Parse "eval(x)").EvaluateNoThrow(dict ["x", NestedExpr [Identifier (Symbol "y")]; "y", BR 7788N]) |> chk (Choice1Of2 (BR 7788N))  "eval005 failed"


Definition.funDict.TryRemove "print"
Definition.funDict.TryAdd ("print", (DTProc ([
    [symX;], (DBFun ((fun parentScopeIdOpt procEnv symbolValues exprs ->
        let g = procEnv.gCtx
        let s = procEnv.sCtx
        let prevO = procEnv.prevOutput
        let stx = procEnv.stx
        let ifTop = procEnv.depth = 0
        printfn "=> %A" (stx.Value.TryGetValue "x" |> snd)
        procEnv
    ), OutFP))
], 0, None)))

Definition.funDict.TryRemove "printCheck"
Definition.funDict.TryAdd ("printCheck", (DTProc ([
    [symX;symY;], (DBFun ((fun parentScopeIdOpt procEnv symbolValues exprs ->
        let g = procEnv.gCtx
        let s = procEnv.sCtx
        let prevO = procEnv.prevOutput
        let stx = procEnv.stx
        let ifTop = procEnv.depth = 0
        printfn "=> %A" (stx.Value.TryGetValue "x" |> snd)
        let _, check = stx.Value.TryGetValue "y"
        if stx.Value.TryGetValue "x" <> stx.Value.TryGetValue "y" then
            { procEnv with prevOutput = Some (Str $"x <> {check}") }
        else
            procEnv
    ), OutFP))
], 0, None)))

let defBase (parentScopeIdOpt:System.Guid option) (procEnv:ProcEnv) (symbolValues:SymbolValues) (exprs:Expression list option) =
        let g = procEnv.gCtx
        let s = 
            if procEnv.sCtx.IsSome then
                procEnv.sCtx.Value
            else
                NamedContext.New(parentScopeIdOpt, None)
        let prevO = procEnv.prevOutput
        let stx = procEnv.stx
        let ifTop = procEnv.depth = 0
        let _, (NestedExpr pList) = stx.Value.TryGetValue paramList.SymbolName
        let _, (NestedExpr dList) = stx.Value.TryGetValue defList.SymbolName
        pList |> printfn "%A"
        exprs.Value[0] |> printfn "exprs[0]: %A"
        exprs.Value[0].Ident.SymbolName |> printfn "exprs.Value[0].Ident.SymbolName: %A"
        printfn $"ifTop: {ifTop}"

        let _, Str funName = stx.Value.TryGetValue name.SymbolName
        printfn "funName: %s" funName
        let funParam =  pList |>List.map (fun e -> e.Ident)
        printfn "pList: %A" pList
        //let funDef =  dList

        //let ctx =X
        //    if ifTop then
        //        s.ctx
        //    else
        //        g.ctx

        let fd =
            if ifTop then
                Definition.funDict
            else
                if s.ctx.ContainsKey "funDict" then
                    s.ctx["funDict"].funDict
                else
                    new FunDict()

        let removed, _ = fd.TryRemove funName
        let proc = DTProc ([funParam, DBExp (dList, OutFP)], 0, None)
        printfn "%A" proc
        let added = fd.TryAdd (funName, proc)

        printfn $"removed: {removed}, added: {added}"

        let out = procEnv

        let effected =
            if ifTop then
                out
            else
                {out with sCtx = sCtxAdd parentScopeIdOpt "funDict" (FD fd) (Some s)}
        effected
        //procEnv




Definition.funDict.TryRemove "def"
Definition.funDict.TryAdd ("def", (DTProc ([
    [name; paramCount; defCount; paramList; defList], (DBFun (defBase, OutFP))
], 0, None )))

(SymbolicExpression.Parse "let(ttc, 789)").Evaluate(dict ["ttc1", FloatingPoint.Real 123.0])
(SymbolicExpression.Parse "print(123)").Evaluate(dict [])


Definition.funDict.TryRemove "main"
Definition.funDict.TryAdd ("main", DTProc ([
    [], (DBExp ([
        Infix.parseOrThrow "let(ttc, 789)"
        Infix.parseOrThrow "print(ttc)"
    ], OutVar [Symbol "ttc"]))
], 0, None))
(SymbolicExpression.Parse "main()").Evaluate(dict ["ttc", FloatingPoint.Real 9487.0])

Definition.funDict.TryRemove "main"
Definition.funDict.TryAdd ("main", DTProc ([
    [], (DBExp ([
        Infix.parseOrThrow "let(ttc1, 789)"
        Infix.parseOrThrow "print(ttc)"
    ], OutVar [Symbol "ttc"; Symbol "ttc1"]))
], 0, None))
(SymbolicExpression.Parse "main()").Evaluate(dict ["ttc", FloatingPoint.Real 9487.0])

//55a82fb8d6e0a188c7dfff2ae3c18d4459b8cc4d
//這個 commit def 內的 def 一樣會定義在 depth = 0，所以出來繼續用，接下來要改成 def 內的只在 def 內生效
(SymbolicExpression.Parse "def(yyds, 1, 1, x, x+1)").Evaluate(dict [])
if (SymbolicExpression.Parse "yyds(123)").Evaluate(dict []) <> BR 124N then failwith "failed 0001"

(SymbolicExpression.Parse "def(ttc, 1, 1, x, printCheck(x*2, 246))").Evaluate(dict [])
if (SymbolicExpression.Parse "ttc(123)").Evaluate(dict []) <> Undef then failwith "failed 0002"




(SymbolicExpression.Parse "def(ttc, 1, 2, x, def(t1,1,1,x,x+100000))").Evaluate(dict [])
(SymbolicExpression.Parse "ttc(123)").Evaluate(dict []) |> chk Undef "failed 0003"
(SymbolicExpression.Parse "t1(123)").Evaluate(dict []) |> chk (BR 100123N) "failed 0004"

(SymbolicExpression.Parse "def(ttc, 1, 2, x, def(t1,1,1,x,x+100000), printCheck(x*2, 246))").Evaluate(dict [])
(SymbolicExpression.Parse "ttc(123)").Evaluate(dict []) |> chk Undef "failed 0005"
(SymbolicExpression.Parse "t1(123)").Evaluate(dict []) |> chk (BR 100123N) "failed 0006"


(SymbolicExpression.Parse "def(ttc, 1, 3, x, def(t1,1,1,x,x+100000), print(x*2), t1(x/3))").Evaluate(dict [])
(SymbolicExpression.Parse "ttc(123)").Evaluate(dict []) |> chk (BR 100041N) "failed 0007"
(SymbolicExpression.Parse "t1(123)").Evaluate(dict []) |> chk (BR 100123N) "failed 0008"

(SymbolicExpression.Parse "def(yyds, 1, 3, x, printCheck(x+1, 124), printCheck(x*2, 246), x/3)").Evaluate(dict [])
(SymbolicExpression.Parse "yyds(123)").Evaluate(dict []) |> chk (BR 41N) "failed 0009"

(SymbolicExpression.Parse "tttt(123)")







Definition.funDict.TryRemove "main"
Definition.funDict.TryAdd ("main", DTProc ([
    [], (DBExp ([
        Infix.parseOrThrow "let(ttc1, 789)"
        Infix.parseOrThrow "let(y, 10000000)"
        Infix.parseOrThrow "print(ttc)"
        Infix.parseOrThrow "print(ttc1)"
        Infix.parseOrThrow "print(ttc1)"
        Infix.parseOrThrow "def(ttc, 2, 3, x, y, def(t1,1,1,x,x+100000), print(x*2), t1(x + y/3))"
        Infix.parseOrThrow "print(ttc(ttc1, 9))"
        Infix.parseOrThrow "let(gg,ttc(ttc1, 9))"
        Infix.parseOrThrow "printCheck(gg, 100792)"
    ], OutFP))
], 0, None))
(SymbolicExpression.Parse "main()").Evaluate(dict ["ttc", FloatingPoint.Real 9487.0]) |> chk Undef "failed 0010"



Definition.funDict.TryRemove "main"
Definition.funDict.TryAdd ("main", DTProc ([
    [], (DBExp ([
        Infix.parseOrThrow "let(ttc1, 789)"
        //Infix.parseOrThrow "let(y, 10000000)"
        Infix.parseOrThrow "print(ttc)"
        Infix.parseOrThrow "print(ttc1)"
        Infix.parseOrThrow "print(ttc1)"
        Infix.parseOrThrow "def(ttc, 2, 3, x, y, def(t1,1,1,x,x+100000+y), print(x*2), t1(x + y/3))"
        (*
        正確計算：
        > 789+4;;
        val it: int = 793

        > 793+100000+12;;
        val it: int = 100805
        *)
        Infix.parseOrThrow "print(ttc(ttc1, 12))"
        Infix.parseOrThrow "let(gg,ttc(ttc1, 12))"
        Infix.parseOrThrow "print(gg)"
    ], OutVar [Symbol "gg"]))
], 0, None))
(SymbolicExpression.Parse "main()").Evaluate(dict ["ttc", FloatingPoint.Real 9487.0]) |> chk (NestedList [BR 100805N]) "failed 0010"



Definition.funDict.TryRemove "main"
Definition.funDict.TryAdd ("main", DTProc ([
    [], (DBExp ([
        Infix.parseOrThrow "let(x, 1023)"
        Infix.parseOrThrow "let(ttc1, x)"
        Infix.parseOrThrow "ttc1"
    ], OutFP))
], 0, None))
(SymbolicExpression.Parse "main()").Evaluate(dict ["x", FloatingPoint.Real 9487.0; "ttc1", FloatingPoint.Real 1487.0])
|> chk (BR 1023N) "failed 0010.1"

Definition.funDict.TryRemove "main"
Definition.funDict.TryAdd ("main", DTProc ([
    [], (DBExp ([
        Infix.parseOrThrow "let(x, 1023)"
        Infix.parseOrThrow "let(ttc1, x)"
        Infix.parseOrThrow "x"
    ], OutFP))
], 0, None))
(SymbolicExpression.Parse "main()").Evaluate(dict ["x", FloatingPoint.Real 9487.0; "ttc1", FloatingPoint.Real 1487.0])
|> chk (BR 1023N) "failed 0010.2"



Definition.funDict.TryRemove "main"
Definition.funDict.TryAdd ("main", DTProc ([
    [], (DBExp ([
        Infix.parseOrThrow "let(x, 123)"
        Infix.parseOrThrow "def(ttc, 2, 3, y1, y2, let(x,456), print(x), print(y2))"
        Infix.parseOrThrow "ttc(100,200)"
    ], OutVar [Symbol "x"]))
], 0, None))
(SymbolicExpression.Parse "main()").Evaluate(dict ["x", FloatingPoint.Real 9487.0; "ttc", FloatingPoint.Real 1487.0])
|> chk (BR 1023N) "failed 0011"





Definition.funDict.Keys
Definition.funDict["t1"]
Definition.funDict["yyds"]



(*
實驗
//let x = 1
let f () =
    let x = 123
    printfn "%d" x
f()
printfn "%d" x
*)

let _ =
    define "testDefine" ([Symbol "x"],
        SymbolicExpression.XParse "x * 2") 



Definition.funDict.TryRemove "main"
Definition.funDict.TryAdd ("main", DTProc ([
    [], (DBExp ([
        Infix.parseOrThrow "let(ttc, str(789))"
        Infix.parseOrThrow "print(ttc)"
    ], OutVar [Symbol "ttc"]))
], 0, None))
(SymbolicExpression.Parse "main()").Evaluate(dict ["ttc", FloatingPoint.Real 9487.0])

BigRational.ToDouble(BigRational.FromDecimal 789M).ToString();;

(SymbolicExpression.Parse "len(expr(xxx + yyy, abc))").Evaluate(dict [])
(SymbolicExpression.Parse "len(param(xxx, abc))").Evaluate(dict [])



let _ =
    define "fun" ([Symbol "name1"; Symbol "paramList1"; Symbol "exprList1"],
        SymbolicExpression.XParse "def(name1, 1, 1, paramList1, exprList1)")

(SymbolicExpression.Parse "fun(yyds1, param(x), expr(x+1))").Evaluate(dict [])
(SymbolicExpression.Parse "yyds1(123)").Evaluate(dict []) |> chk (BR 124N) "failed 0011"

(SymbolicExpression.Parse "fun(yyds1, param(x, y), expr(x+1+y))").Evaluate(dict [])
(SymbolicExpression.Parse "yyds1(123, 6)").Evaluate(dict []) |> chk (BR 130N) "failed 0012"

(SymbolicExpression.Parse "fun(yyds1, param(x), expr(x+1+y))").Evaluate(dict [])
(SymbolicExpression.Parse "yyds1(123)").Evaluate(dict ["y", BR 16N]) |> chk (BR 140N) "failed 0013"

(SymbolicExpression.Parse "fun(yyds1, x, expr(x+1+y))").Evaluate(dict [])
(SymbolicExpression.Parse "yyds1(123)").EvaluateNoThrow(dict ["y", BR 16N]) |> chk (Choice2Of2 ("Failed to find symbol x")) "failed 0014"


(SymbolicExpression.Parse "let(x,expr(x,123))").EvaluateBase(dict ["x", BR 1478N]).eEnv.sCtx.Value.ctx["x"] |> chk (NestedExpr [Identifier (Symbol "x"); Number 123N]) "failed 0015"

(SymbolicExpression.Parse "let(x,x)").EvaluateBase(dict ["x", BR 1478N]).eEnv.sCtx.Value.ctx["x"] |> chk (BR 1478N) "failed 0016"




(*
+		["exprList"]	NestedExpr [FunInvocation (Symbol "expr", [Sum [Number 1N; Identifier (Symbol ...); ...]; ...]); ...]	
+		["name"]	Str "yyds1"	
+		["paramList"]	NestedExpr [FunInvocation (Symbol "param", [Identifier (Symbol "x")])]	


*)


Definition.funDict.Keys |> Seq.toArray
Definition.funDict["fun"]
Definition.funDict["name"]



open System
let outputCode =
    EvalRst
    ({ gCtx = { id = Guid.Parse "019720a2-fc49-7a2c-a6b0-36a10a2932ad"
                ctx = Map [] }
       sCtx =
        Some
          { id = Guid.Parse "019720a2-fc4c-7aaa-8232-62c5af030f17"
            ctx =
             Map
               [("it",
                 EvalRst
                   ({ gCtx =
                       { id =
                          Guid.Parse "019720a2-fc49-7a2c-a6b0-36a10a2932ad"
                         ctx = Map [] }
                      sCtx =
                       Some
                         { id =
                            Guid.Parse "019720a2-fc4c-709d-be14-f7be514dfab3"
                           ctx = Map [("it", Undef); ("ttc", BR 789N)] }
                      prevOutput = Some Undef
                      stx =
                       Some
                         (Map
                            [("stepId",
                              Str "f766bb3b-60b0-4367-9333-bfede9f321a8");
                             ("v", BR 789N)])
                      procParamArgExpr = None
                      depth = 0 }, Undef))] }
       prevOutput =
        Some
          (EvalRst
             ({ gCtx =
                 { id = Guid.Parse "019720a2-fc49-7a2c-a6b0-36a10a2932ad"
                   ctx = Map [] }
                sCtx =
                 Some
                   { id = Guid.Parse "019720a2-fc4c-7aaa-8232-62c5af030f17"
                     ctx =
                      Map
                        [("it",
                          EvalRst
                            ({ gCtx =
                                { id =
                                   Guid.Parse "019720a2-fc49-7a2c-a6b0-36a10a2932ad"
                                  ctx = Map [] }
                               sCtx =
                                Some
                                  { id =
                                     Guid.Parse "019720a2-fc4c-709d-be14-f7be514dfab3"
                                    ctx =
                                     Map [("it", Undef); ("ttc", BR 789N)] }
                               prevOutput = Some Undef
                               stx =
                                Some
                                  (Map
                                     [("stepId",
                                       Str
                                         "f766bb3b-60b0-4367-9333-bfede9f321a8");
                                      ("v", BR 789N)])
                               procParamArgExpr = None
                               depth = 0 }, Undef))] }
                prevOutput =
                 Some
                   (EvalRst
                      ({ gCtx =
                          { id =
                             Guid.Parse "019720a2-fc49-7a2c-a6b0-36a10a2932ad"
                            ctx = Map [] }
                         sCtx =
                          Some
                            { id =
                               Guid.Parse "019720a2-fc4c-709d-be14-f7be514dfab3"
                              ctx = Map [("it", Undef); ("ttc", BR 789N)] }
                         prevOutput = Some Undef
                         stx =
                          Some
                            (Map
                               [("stepId",
                                 Str "f766bb3b-60b0-4367-9333-bfede9f321a8");
                                ("v", BR 789N)])
                         procParamArgExpr = None
                         depth = 0 }, Undef))
                stx =
                 Some
                   (Map
                      [("stepId", Str "43efacbd-6cfb-4a38-803a-27005ad803f6");
                       ("x", FloatingPoint.Real 9487.0)])
                procParamArgExpr = None
                depth = 0 },
              EvalRst
                ({ gCtx =
                    { id = Guid.Parse "019720a2-fc49-7a2c-a6b0-36a10a2932ad"
                      ctx = Map [] }
                   sCtx =
                    Some
                      { id =
                         Guid.Parse "019720a2-fc4c-709d-be14-f7be514dfab3"
                        ctx = Map [("it", Undef); ("ttc", BR 789N)] }
                   prevOutput = Some Undef
                   stx =
                    Some
                      (Map
                         [("stepId",
                           Str "f766bb3b-60b0-4367-9333-bfede9f321a8");
                          ("v", BR 789N)])
                   procParamArgExpr = None
                   depth = 0 }, Undef)))
       stx =
        Some (Map [("stepId", Str "b621bd1d-3df1-4b50-9d23-f4e0737975d4")])
       procParamArgExpr = None
       depth = 0 }, NestedList [FloatingPoint.Real 9487.0])







(SymbolicExpression.Parse "fun(param(xxx, yyy), expr(xxx + yyy))").Evaluate(dict [])

type A = | AA
    with
        member val orz:int with get, set




type A = {i:int}
    with
        static let a = 123
        static member aaa = a









Infix.parseOrUndefined "x" ==> "x"

let var_x_0 = Infix.parse "x" //val var_x_0 : Result<Expression,string> = Ok (Identifier (Symbol "x"))
let var_x = Infix.parseOrUndefined "x" //val var_x : Expression = Identifier (Symbol "x")
let var_x_expr = SymbolicExpression(var_x)



open MathNet.Numerics.LinearAlgebra
let v = vector[1.0;2.0;3.0]

let M = 
        matrix [[3.0; 0.0; 0.0]
                [1.0; 2.0; 0.0]
                [0.0; 1.0; 4.0]]


v * M

M * v

v * v


let eval_var_x_value = (Compile.compileExpression1OrThrow var_x_expr.Expression symX).Invoke(1.0) //error

let var_x_2 = Expr.Variable("x").Expression
let sin_of_x = Infix.parseOrUndefined "sin(x)"

var_x = var_x_2 //true


(Compile.compileExpression1OrThrow sin_of_x symX).Invoke(3.0)
(Compile.compileExpression1OrThrow var_x symX).Invoke(3.0)


let symExp5 = Expr.Parse("v + w + x + y + z")
let cmpl = Compile.compileExpressionOrThrow (symExp5.Expression) [symV; symW; symX; symY; symZ] 
cmpl.DynamicInvoke(1.0, 2.0, 3.0, 4.0, 5.0)

cmpl.GetInvocationList().[0]
cmpl.DynamicInvoke([|box 1.0; box 2.0; box 3.0; box 4.0; box 5.0|]:obj[])

cmpl.GetType().FullName
cmpl.Method.Invoke(null, [|1.0; 2.0; 3.0; 4.0; 5.0|])

let ivk = cmpl.GetType().GetMethod("DynamicInvoke")
ivk.Invoke(cmpl, [|box 1.0; box 2.0; box 3.0; box 4.0; box 5.0|])

(var_x_2 + var_x_2).ToString()

let parse_expr = Expr.Parse("1/(a*b)")
parse_expr.Expression = Infix.parseOrUndefined "1/(a*b)"

parse_expr.ToString()

let symbols = dict[ "a", FloatingPoint.Real 2.0; "b", FloatingPoint.Real 3.0; "x", FloatingPoint.Real 6.0]

// Returns 0.166666666666667
let code_expr = SymbolicExpression(abs(1 / (-a * b)))
let code = abs(1 / (-a * b))
let code1_0 = abs( fromDouble 1.0)
let code1_1 = abs( Value.fromDouble 1.0 |> Values.unpack)
code1_0 = code1_1
let eval_value = code_expr.Evaluate(symbols)
var_x_expr.Evaluate(symbols)
eval_value.RealValue

Expr.Variable("a").Evaluate(symbols)

let aa = Expr.Variable("a").Expression

SymbolicExpression(aa + 1).Evaluate(symbols)

SymbolicExpression(Pi).Evaluate(dict[]) //error
SymbolicExpression(Pi).RealNumberValue //val it : float = 3.141592654

Expr.Parse("sin(pi)").ToString()
Expr.Parse("sin(pi)").Evaluate(dict[])
Expr.Parse("pi").Evaluate(dict[])
Expr.Parse("3 * j").Evaluate(dict[])
Expr.Parse("pow(5,pow(5,2))^2").Evaluate(dict[])
Expr.Parse("sum([1;2;3])").Evaluate(dict[]) //error
Expr.Parse("sum(1,2,3)").Evaluate(dict[])
Expr.Parse("pow(5,pow(5,a))^2").ToString()
Expr.Parse("ttc(123)").ToString()
SymbolicExpression(sum([fromDouble 1.0; fromDouble 2.0])).Evaluate(dict[])
SymbolicExpression(sum([fromDouble 1.0; fromDouble 2.0])).ToString()
Infix.format(sum([x; fromDouble 2.0; y]))
//https://github.com/mathnet/mathnet-symbolics/issues/44
let e3 = Infix.parseOrThrow("L+H+L+H - (L+H)")

let expanded = Algebraic.expand(e3)
Infix.format(expanded)


let e4 = Infix.parseOrThrow("a + b - (a + b)")

let expanded4 = Algebraic.expand(e4)
Infix.format(expanded4)


let log_test = SymbolicExpression(log (fromInt32 10) (fromDouble 100.0))
let eval_log_test = log_test.Evaluate(symbols)

symV

open Definition
define "test" ([symV; symW], (v + w)*2)
SymbolicExpression(Infix.parseOrThrow("2^test(x, 2 * x)")).Evaluate(dict[ "x", FloatingPoint.Real 2.0; ])

SymbolicExpression(cFun("test", [x + (fromInt32 10); (fromDouble 100.0)])*2).Evaluate(dict[ "x", FloatingPoint.Real 9.0; ])


Infix.parseOrThrow("test(2 * x, 3 * x)").ToString()
Infix.format(cFun("test", [x + (fromInt32 10); (fromDouble 100.0)])*2)

let y = pow 2Q (sin(x))
Infix.format(y)


def1ito1i "orz" (fun x -> 3*x)
SymbolicExpression(Infix.parseOrThrow("orz(2 * x)")).Evaluate(dict[ "x", FloatingPoint.Real 2.0; ])

let e5 = Infix.parseOrThrow("orz(2 * x - 2 * x) + a + b - (a + b)")

let expanded5 = SymbolicExpression(Algebraic.expand(e5)).Evaluate(dict[])


open MathNet.Numerics.LinearAlgebra

FloatingPoint.Real 1.0 = FloatingPoint.Real 12.0
let vvv = FloatingPoint.RealVector <| vector[1.0;2.0;3.0]


let symbols2 = dict[ "a", vvv ]

SymbolicExpression(Infix.parseOrThrow("a + 1")).Evaluate(symbols2)
SymbolicExpression(Infix.parseOrThrow("a + a")).Evaluate(symbols2)
SymbolicExpression(Infix.parseOrThrow("2 * a")).Evaluate(symbols2)

Infix.parseOrThrow("2 * a")

SymbolicExpression(Infix.parseOrThrow("a")).Evaluate(symbols2).RealVectorValue
int System.Double.NaN


open Definition
define "test" ([symV; symW], (v + w)*2)
let e6 = Infix.parseOrThrow("test(a + a + b,test (9,2,0))")

let expanded6 = Algebraic.expand(e6)
printfn "%s" <| Infix.format(expanded6)

let symbols3 = dict[ "a", FloatingPoint.Real 2.0; "b", FloatingPoint.Real 3.0; "test", FloatingPoint.Real 6.0]

SymbolicExpression(expanded6).Evaluate(symbols3)
define "test" ([symV], v * 2)
