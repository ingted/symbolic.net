#I @"..\..\SymbolicNet6\bin\net9.0\"
#r @"SymbolicNet6.dll"
#r @"..\..\scripts\FsProfiler\FsProfiler.dll"
//#r @"nuget: MathNet.Numerics"
#r @"MathNet.Numerics.dll"
#r @"nuget:FsUnit"
#r @"nuget:FParsec"
#r @"nuget:MathNet.Numerics.FSharp"
#r "nuget: DiffSharp.Core, 1.0.7"
#r "nuget: DiffSharp.Backends.Reference, 1.0.7"
#r "nuget: DiffSharp.Backends.Torch, 1.0.7"
#r @"G:\coldfar_py\sharftrade9\實驗\SharFTrade.Exp\bin2\net9.0\protobuf-net.Core.dll"
//#I @"..\SymbolicNet6"
//#load @".\Symbols.fs"
//#load @".\Approximation.fs"
//#load @".\Value.fs"
//#load @".\Expression.fs"
////#load @".\Evaluate.fsi"
//#load @".\Definition.fs"
//#load @".\Numbers.fs"
//#load @".\Structure.fs"
//#load @".\Algebraic.fs"
//#load @".\Calculus.fs"
//#load @".\Polynomial.fs"
//#load @".\Rational.fs"
//#load @".\Exponential.fs"
//#load @".\Trigonometric.fs"
//#load @".\Approximate.fs"
//#load @".\Enriched\EnrichedExpression.fs"
//#load @".\Visual\VisualExpression.fs"
//#load @".\Visual\Infix.fs"
//#load @".\Visual\LaTeX.fs"
//#load @".\Visual\MathML.fs"
//#load @".\Typed\TypedExpression.fs"
//#load @".\Typed\Quotations.fs"
//#load @".\Linq.fs"
//#load @".\Compile.fs"
//#load @".\Evaluate.fs"
#load @"..\..\SymbolicNet6.Test\Global.fs"

open MathNet.Numerics
open MathNet.Symbolics
open Global
open Operators
open VariableSets.Alphabet
type Expr = SymbolicExpression

Infix.parseOrUndefined "x" ==> "x"

let symV = Symbol "v"
let symW = Symbol "w"
let symX = Symbol "x"
let symY = Symbol "y"
let symZ = Symbol "z"



open Definition

open System.Linq.Expressions

let addB = Expression.Parameter(typeof<System.Double>, "b")
let addC = Expression.Parameter(typeof<MathNet.Symbolics.Value>, "c")

Expression.Add(
            addB,
            addC
        )

typeof<float> = typeof<System.Double>

let mutable o = [|1;2;3|]

let changeIt (o:int[]) =
    o.[2] <- 0

changeIt o

let changeIt2 (oo:int[]) =
    o <- [||]

changeIt2 o


open MathNet.Numerics.LinearAlgebra


let _ =
    define "dup00" ([Symbol "x"; Symbol "z"],
        SymbolicExpression.XParse "x + 11 * z")

let _ =
    define "dup3" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "x + y * dup00(x, y) + z")

let _ =
    define "dup4" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "dup3(x+1,y*2)")

let _ =
    define "dup5" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "dup4(x,y)+1")

let _ =
    define "dup31" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "x + y * y + z")
let _ =
    define "dup41" ([Symbol "x"; Symbol "y"],
        SymbolicExpression.XParse "dup31(x+1,y*2)")

SymbolicExpression.Parse("dup4(7,8)").EvaluateMode0(dict ["z", FloatingPoint.Real -8.0]) //5889 = 9 + 32 * (8 + 11 * 16) - 8 (不正確，應該等於 2944)
SymbolicExpression.Parse("dup3(8,16)").EvaluateMode0(dict ["z", FloatingPoint.Real -8.0]) //2944 = 8 + 16 * (8 + 11 * 16) - 8 (正確)
SymbolicExpression.Parse("dup41(7,8)").EvaluateMode0(dict ["z", FloatingPoint.Real -8.0]) //1025 = 9 + 32 * 32 - 8 (不正確，應該等於 256)
SymbolicExpression.Parse("dup31(8,16)").EvaluateMode0(dict ["z", FloatingPoint.Real -8.0]) //256 = 8 + 16 * 16 - 8 (正確)

SymbolicExpression.Parse("dup5(7,8)").Evaluate(dict ["z", FloatingPoint.Real -8.0]) 
SymbolicExpression.Parse("dup4(7,8)").Evaluate(dict ["z", FloatingPoint.Real -8.0]) 
SymbolicExpression.Parse("dup3(8,16)").Evaluate(dict ["z", FloatingPoint.Real -8.0]) 
SymbolicExpression.Parse("dup41(7,8)").Evaluate(dict ["z", FloatingPoint.Real -8.0]) 
SymbolicExpression.Parse("dup31(8,16)").Evaluate(dict ["z", FloatingPoint.Real -8.0])
















let s_ = seq [1.0; 2.0; 3.0]
let v_ : Vector<float> = Vector<float>.Build.DenseOfEnumerable(s_)
try
    Infix.parseOrThrow "sum(i, 1, n, i^2)"//不支援
    ()
with
| exn ->
    printfn "%s" exn.Message
(SymbolicExpression.Parse "str(ttc+1)").Evaluate(dict ["ttc", FloatingPoint.Real 123.0])

SymbolicExpression(Sum([Number<|BigRational.FromInt 1;Number <| BigRational.FromInt 1 ])).Evaluate(dict [])
LaTeX.format (Sum([Number<|BigRational.FromInt 1;Number <| BigRational.FromInt 1;Number <| BigRational.FromInt 2 ]))


define "test" ([symV; symW], (v + w) * 2)
define "test1" ([symV; symW], Infix.parseOrThrow("test(v, w)"))
define "sum" ([symV; symW; symX], Infix.parseOrThrow(""))
define "sum" ([symV; symW; symX], v + w + x)


LaTeX.format (Infix.parseOrThrow("1 + v"))
SymbolicExpression(Infix.parseOrThrow("2^test(test(x, -2), 2 * x)")).Evaluate(dict [ "x", FloatingPoint.Real 2.0; ])
SymbolicExpression(Infix.parseOrThrow("acos(1)")).Evaluate(dict [])
SymbolicExpression(Infix.parseOrThrow("sum(1,2,3)")).Evaluate(dict [])

SymbolicExpression(Infix.parseOrThrow("x")).Evaluate(dict ["x", FloatingPoint.Real 2.0])
//SymbolicExpression(Infix.parseOrThrow("2^test(x, 2 * x)")).Evaluate(dict [ "x", MathNet.Symbolics.Value.fromSingle 2.0; ])
SymbolicExpression(Infix.parseOrThrow("2^test1(x, 2 * x)")).Evaluate(dict [ "x", FloatingPoint.Real 2.0; ])

SymbolicExpression(Infix.parseOrThrow("2^test1(x, 2 * x)")).Expression.ToString()
Infix.parseOrThrow("2^test1(x, 2 * x)").ToString()

SymbolicExpression(Product
    [Number 2N;
        FunInvocation (Symbol "test",
            [Sum [Number 10N; Identifier (Symbol "x")]; Approximation (Real 100.0)]
        )
    ]
).Evaluate(dict[ "x", FloatingPoint.Real 2.0; ])



SymbolicExpression(Power
    (Number 2N,
     FunInvocation
       (Symbol "test",
        [Identifier (Symbol "x"); Product [Number 2N; Identifier (Symbol "x")]])
       )
).Evaluate(dict[ "x", FloatingPoint.Real 2.0; ])

#r @"G:\coldfar_py\sharftrade9\實驗\ExperimentsContainer\../SharFTrade.Exp/bin2/net9.0\protobuf-net.dll"
#r @"G:\coldfar_py\sharftrade9\實驗\ExperimentsContainer\../SharFTrade.Exp/bin2/net9.0\protobuf-net.Core.dll"

let power = Power (
    Number 2N,
    FunInvocation
       (Symbol "test",
        [Identifier (Symbol "x"); Product [Number 2N; Identifier (Symbol "x")]])
       )
SymbolicExpression(Infix.parseOrThrow((SymbolicExpression power).ToString()))

SymbolicExpression(cFun("test", [x + (fromInt32 10); (fromDouble 100.0)])*2).Evaluate(dict[ "x", FloatingPoint.Real 9.0; ])

let symbolsd = dict [ "x", FloatingPoint.Real 9.0; ]
SymbolicExpression(cFun("test1", [x + (fromInt32 10); (fromDouble 100.0)])*2).Evaluate(symbolsd)


Linq.formatComplexLambda (Infix.parseOrThrow "x") [(Symbol "x")]


let syml = dict [ "x", FloatingPoint.Real 9.0; ]
define "t0" ([symV; symW], (v + w))
SymbolicExpression(cFun("t0", [x; x])).Evaluate(syml)
define "t1" ([symV; symW], Infix.parseOrThrow("t0(v, w)"))
SymbolicExpression(cFun("t1", [x; x])).Evaluate(syml)



Infix.parseOrThrow("test(2 * x, 3 * x)").ToString()
Infix.format(cFun("test", [x + (fromInt32 10); (fromDouble 100.0)])*2)

let y = pow 2Q (sin(x))
Infix.format(y)


def1ito1i "orz" (fun x -> 3*x)
SymbolicExpression(Infix.parseOrThrow("orz(2 * x)")).Evaluate(dict [ "x", FloatingPoint.Real 2.0; ])

let e5 = Infix.parseOrThrow("orz(2 * x - 2 * x) + a + b - (a + b)")

let expanded5 = SymbolicExpression(Algebraic.expand(e5)).Evaluate(dict [])

open System.Linq.Expressions


let rec translateExpr (linq:Expression) = 
    match linq with
    | :? MethodCallExpression as mc ->
        let le = mc.Arguments.[0] :?> LambdaExpression
        let args, body = translateExpr le.Body
        le.Parameters.[0] :: args, body
    | _ ->
        printfn "not MethodCallExpression"
        [], linq


open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Linq
//#r @"nuget: FSharp.Quotations.Evaluator"
//open FSharp.Quotations.Evaluator
//let liq = QuotationEvaluator.ToLinqExpression (<@@ fun a b c -> (a + b) * c @@>)


open Microsoft.FSharp.Linq.RuntimeHelpers
open System
let toLinq (expr : Expr<'a -> 'b>) =
    let linq = LeafExpressionConverter.QuotationToExpression expr
    let call = linq :?> MethodCallExpression
    let lambda = call.Arguments.[0] :?> LambdaExpression
    Expression.Lambda<Func<'a, 'b>>(lambda.Body, lambda.Parameters) 

LeafExpressionConverter.QuotationToExpression (<@ fun a b c -> (a + b) * c @>) :?> MethodCallExpression
LeafExpressionConverter.QuotationToExpression <@ System.String.Concat("Hello", "World") @> :?> MethodCallExpression

let liq = toLinq (<@ fun a b c -> (a + b) * c @>)

liq.Compile()


let rec collectParamsAndBody (e: Expression) =
    match e with
    | :? LambdaExpression as le ->
        let args, body = collectParamsAndBody le.Body
        let ps = le.Parameters |> Seq.toList
        (ps @ args), body
    | :? MethodCallExpression as mc when mc.Method.Name = "ToFSharpFunc" ->
        collectParamsAndBody mc.Arguments.[0]
    | other ->
        [], other


//let args, body = translateExpr liq //後面會錯誤，正確版本是 collectParamsAndBody
let args, body = collectParamsAndBody liq
let f = Expression.Lambda<Func<int, int, int, int>>(body, args |> Array.ofSeq)
f.Compile().Invoke(10, 11, 2)


let aa = LeafExpressionConverter.QuotationToExpression (<@ fun () -> printfn "%d" 123 @>) :?> MethodCallExpression
aa.ToString()



let _ =
    define "成交明細" ([],
        SymbolicExpression.XParse "1") 
SymbolicExpression(SymbolicExpression.XParse "2 + 成交明細()").Evaluate(dict [])



let expr = PointwiseMul (
    
    Identifier (Symbol "u")
    , Identifier (Symbol "v")
)

open System.Collections.Concurrent
open System.Collections.Generic

type ConcurrentDictionary<'k,'v>  with 
    static member op_Implicit (x:IDictionary<'k,'v>) =
        ConcurrentDictionary<'k,'v> x

type IDictionary<'k,'v>  with 
    static member op_Implicit (x:IDictionary<'k,'v>) =
        ConcurrentDictionary<'k,'v> x


let env =
    dict [
        "u", FloatingPoint.RealVector (vector [10.0; 20.0; 30.0])
        "v", FloatingPoint.RealVector (vector [10.0; 20.0; 30.0])
    ]
    |> ConcurrentDictionary<_, _>

let result = Evaluate.evaluate2_ env None expr
// ➜ RealVector [20.0; 40.0; 60.0]

SymbolicExpression(expr).ToString()
SymbolicExpression(expr).Evaluate(env)
SymbolicExpression.Parse("u.*v").Evaluate(env)
SymbolicExpression.Parse("u.*v").ToString()
SymbolicExpression.Parse("(u.*(v + 1)+2) * 2").ToString()
SymbolicExpression.Parse("(u.*(v + 1)+2) * 2").Evaluate(dict [
        "u", FloatingPoint.RealVector (vector [10.0; 20.0; 30.0])
        "v", FloatingPoint.RealVector (vector [10.0; 20.0; 30.0])
    ])

let expr, cmpl = Compile.compileExpressionOrThrow2 expr [Symbol "u"; Symbol "v"]

printfn "compiled method = %A" cmpl.Method
printfn "param count = %d" (cmpl.Method.GetParameters().Length)

cmpl.DynamicInvoke([|(env["u"],env["v"])|])
cmpl.DynamicInvoke([|env["u"];env["v"]|])
cmpl.DynamicInvoke([| box env["u"]; box env["v"] |])

type FooParam =
| BoolParam of bool
| StrParam of string
with 
    static member op_Implicit(x: bool) = BoolParam x
    static member op_Implicit(x: string) = StrParam x


let foo (x: FooParam) = 
    match x with
    | BoolParam y -> printfn "Bool: %A" y
    | StrParam z -> printfn "String: %A" z

foo true



let mi = typeof<MathNet.Symbolics.Linq.MyOps>.GetMethod("PointwiseMultiply", [|typeof<float[]>;typeof<float[]>|])

let aExpr = Expression.Constant([| 1.0; 2.0 |])
let bExpr = Expression.Constant([| 3.0; 4.0 |])

let callExpr = Expression.Call(mi, aExpr, bExpr)

let lambda = Expression.Lambda<System.Func<float[]>>(callExpr)
let compiled = lambda.Compile()
let result = compiled.Invoke() // 這裡會觸發 orz



SymbolicExpression.Parse("dup4(7,8)^3").Evaluate(dict ["z", FloatingPoint.Real -8.0])
