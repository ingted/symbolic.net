#r @"..\bin\net9.0\SymbolicNet6.dll"
#r @"nuget:MathNet.Numerics"
#r @"nuget:FsUnit"
#r @"nuget:FParsec"
#r @"nuget:MathNet.Numerics.FSharp"
#r @"nuget:PersistedConcurrentSortedList"
#r @"nuget:FAkka.Deedle"
#load @"..\..\SymbolicNet6.Test\Global.fs"

open MathNet.Numerics
open MathNet.Symbolics
open Global
open Operators
open VariableSets.Alphabet
type Expr = SymbolicExpression
open Definition
open Evaluate

(SymbolicExpression.Parse "(ttc)").Evaluate(dict ["ttc", FloatingPoint.Real 123.0])
(SymbolicExpression.Parse "str(ttc)").Evaluate(dict ["ttc", FloatingPoint.Real 123.0])


let symV = Symbol "v"
let symW = Symbol "w"
let symX = Symbol "x"
let symY = Symbol "y"
let symZ = Symbol "z"


Definition.funDict.TryRemove "let"
Definition.funDict.TryAdd ("let", (DTProc [
    [symX; symV], (DBFun (fun g s prevO stx exprs ifTop ->
        stx.GetValue "x" |> printfn "%A"
        exprs.Value[0] |> printfn "exprs[0]: %A"
        exprs.Value[0].Ident.SymbolName |> printfn "exprs.Value[0].Ident.SymbolName: %A"
        printfn $"ifTop: {ifTop}"
        let effectIn =
            if ifTop then
                g
            else
                s
        effectIn[exprs.Value[0].Ident.SymbolName] <- stx.GetValue("v").Value
        printfn "stxId: %A" (stx.GetValue "stepId")
        Undef
    ))
    [symX;], (DBFun (fun g s prevO stx exprs ifTop ->
        stx.GetValue "x" |> printfn "%A"
        exprs.IsNone |> printfn "exprs.IsNone %A"
        printfn $"ifTop: {ifTop}"
        printfn "stxId: %A" (stx.GetValue "stepId")
        let effectIn =
            if ifTop then
                g
            else
                s
        effectIn["ttc"]  |> printfn "ttc: %A"
        Undef
    ))
]))
Definition.funDict.TryRemove "print"
Definition.funDict.TryAdd ("print", (DTProc [
    [symX;], (DBFun (fun g s prevO stx exprs ifTop ->
        printfn "%A" (stx.GetValue "x").Value
        Undef
    ))
]))

Definition.funDict.TryRemove "def"
Definition.funDict.TryAdd ("def", (DTProc [
    [symX; symV], (DBFun (fun g s prevO stx exprs ifTop ->
        stx.GetValue "x" |> printfn "%A"
        exprs.Value[0] |> printfn "exprs[0]: %A"
        exprs.Value[0].Ident.SymbolName |> printfn "exprs.Value[0].Ident.SymbolName: %A"
        printfn $"ifTop: {ifTop}"
        let effectIn =
            if ifTop then
                g
            else
                s
        effectIn[exprs.Value[0].Ident.SymbolName] <- stx.GetValue("v").Value
        printfn "stxId: %A" (stx.GetValue "stepId")
        Undef
    ))

]))


(*
¹êÅç
//let x = 1
let f () =
    let x = 123
    printfn "%d" x
f()
printfn "%d" x
*)
(SymbolicExpression.Parse "let(ttc, 789)").Evaluate(dict ["ttc", FloatingPoint.Real 123.0])
(SymbolicExpression.Parse "print(123)").Evaluate(dict [])




(SymbolicExpression.Parse "expr(xxx + yyy, abc)").Evaluate(dict [])
(SymbolicExpression.Parse "param(xxx, abc)").Evaluate(dict [])
(SymbolicExpression.Parse "def(param(xxx, yyy), expr(xxx + yyy))").Evaluate(dict [])






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
