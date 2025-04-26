//#r @"..\src\Symbolics\bin\Debug\netstandard2.0\MathNet.Symbolics.dll"
#r @"..\SymbolicNet6\bin\Debug\net9.0\SymbolicNet6.dll"
#r @".\FsProfiler\FsProfiler.dll"
#r @"nuget: MathNet.Numerics, 5.0.0"
#r @"nuget:FsUnit"
#r @"nuget:FParsec"
#r @"nuget:MathNet.Numerics.FSharp"
#r "nuget: DiffSharp.Core, 1.0.7"
#r "nuget: DiffSharp.Backends.Reference, 1.0.7"
#r "nuget: DiffSharp.Backends.Torch, 1.0.7"
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
#load @"..\SymbolicNet6.Test\Global.fs"

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

[<RequireQualifiedAccess>]
type Value =
    | Number of BigRational
    | Approximation of Approximation
    | ComplexInfinity
    | PositiveInfinity
    | NegativeInfinity
    | Undefined
    with 
        static member (+) (vl : Value, vr : Value) =
            match vl with
            | Number vlv ->
                match vr with
                | Number vrv ->
                    vlv * vrv
        static member (*) (vl : Value, vr : float) =
            match vl with
            | Approximation (Real vlv) ->
                vlv * vr
        static member (+) (vl : Value, vr : float) =
            match vl with
            | Approximation (Real vlv) ->
                vlv + vr
        static member (+) (vl : float, vr : Value) =
            match vr with
            | Approximation vrv ->
                match vrv with
                | Approximation.Real vrvv ->
                    vl + vrvv

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

define "test" ([symV; symW], (v + w) * 2)
define "test1" ([symV; symW], Infix.parseOrThrow("test(v, w)"))
SymbolicExpression(Infix.parseOrThrow("2^test(x, 2 * x)")).Evaluate(dict[ "x", FloatingPoint.Real 2.0; ])
SymbolicExpression(Infix.parseOrThrow("2^test1(x, 2 * x)")).Evaluate(dict[ "x", FloatingPoint.Real 2.0; ])

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

parse liq

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
