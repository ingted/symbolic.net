//#r @"..\src\Symbolics\bin\Debug\netstandard2.0\MathNet.Symbolics.dll"
#r @"G:\git\mathnet-symbolics\SymbolicNet6\bin\Debug\net6.0\SymbolicNet6.dll"
#r @".\FsProfiler\FsProfiler.dll"
#r @"nuget:MathNet.Numerics"
#r @"nuget:FsUnit"
#r @"nuget:FParsec"
#r @"nuget:MathNet.Numerics.FSharp"
#r "nuget: DiffSharp.Core, 1.0.7-preview1873603133"
#r "nuget: DiffSharp.Backends.Reference, 1.0.7-preview1873603133"
#r "nuget: DiffSharp.Backends.Torch, 1.0.7-preview1873603133"
#I @"..\SymbolicNet6"
#load @".\Symbols.fs"
#load @".\Approximation.fs"
#load @".\Value.fs"
#load @".\Expression.fs"
//#load @".\Evaluate.fsi"
#load @".\Definition.fs"
#load @".\Numbers.fs"
#load @".\Structure.fs"
#load @".\Algebraic.fs"
#load @".\Calculus.fs"
#load @".\Polynomial.fs"
#load @".\Rational.fs"
#load @".\Exponential.fs"
#load @".\Trigonometric.fs"
#load @".\Approximate.fs"
#load @".\Enriched\EnrichedExpression.fs"
#load @".\Visual\VisualExpression.fs"
#load @".\Visual\Infix.fs"
#load @".\Visual\LaTeX.fs"
#load @".\Visual\MathML.fs"
#load @".\Typed\TypedExpression.fs"
#load @".\Typed\Quotations.fs"
#load @".\Linq.fs"
#load @".\Compile.fs"


















#load @".\Evaluate.fs"
#load @"..\src\Symbolics.Tests\Global.fs"

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





define "test" ([symV; symW], (v + w)*2)
define "test1" ([symV; symW], Infix.parseOrThrow("test(v, w)"))
SymbolicExpression(Infix.parseOrThrow("2^test(x, 2 * x)")).Evaluate(dict[ "x", FloatingPoint.Real 2.0; ])

SymbolicExpression(cFun("test", [x + (fromInt32 10); (fromDouble 100.0)])*2).Evaluate(dict[ "x", FloatingPoint.Real 9.0; ])

let symbolsd = dict[ "x", FloatingPoint.Real 9.0; ]
SymbolicExpression(cFun("test1", [x + (fromInt32 10); (fromDouble 100.0)])*2).Evaluate(symbolsd)


Infix.parseOrThrow("test(2 * x, 3 * x)").ToString()
Infix.format(cFun("test", [x + (fromInt32 10); (fromDouble 100.0)])*2)

let y = pow 2Q (sin(x))
Infix.format(y)


def1ito1i "orz" (fun x -> 3*x)
SymbolicExpression(Infix.parseOrThrow("orz(2 * x)")).Evaluate(dict[ "x", FloatingPoint.Real 2.0; ])

let e5 = Infix.parseOrThrow("orz(2 * x - 2 * x) + a + b - (a + b)")

let expanded5 = SymbolicExpression(Algebraic.expand(e5)).Evaluate(dict[])

open System.Linq.Expressions


let rec translateExpr (linq:Expression) = 
    match linq with
    | :? MethodCallExpression as mc ->
        let le = mc.Arguments.[0] :?> LambdaExpression
        let args, body = translateExpr le.Body
        le.Parameters.[0] :: args, body
    | _ -> [], linq


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

let liq = toLinq (<@ fun a b c -> (a + b) * c @>)

liq.Compile()


let args, body = translateExpr liq
let f = Expression.Lambda<Func<int, int, int, int>>
          (body, args |> Array.ofSeq)
f.Compile().Invoke(10, 11, 2)


let aa = LeafExpressionConverter.QuotationToExpression (<@ fun () -> printfn "%d" 123 @>) :?> MethodCallExpression
aa.ToString()
