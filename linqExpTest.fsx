open System
open System.Collections.Generic
open System.Linq.Expressions


let paramA = Expression.Parameter(typeof<string>, "a")

type ExprHelper<'T> () =
    static member Quote(e:Expression<'T>) = e

let expr : Expression<Func<string, bool>> =
    ExprHelper<Func<string, bool>>.Quote (fun b -> b = "Something")


Expression.Lambda(
    Expression.Invoke(expr, paramA),
    paramA
)



open Microsoft.FSharp.Linq.RuntimeHelpers
open System
open System.Linq.Expressions

//F#-helper method for Linq.Expressions: fssnip.net/ts/title/F-lambda-to-C-LINQ-Expression
module Lambda =
    let toExpression (``f# lambda`` : Quotations.Expr<'a>) =
        ``f# lambda``
        |> LeafExpressionConverter.QuotationToExpression 
        |> unbox<Expression<'a>>

let toTraverse = <@ Func<int, int, int>(fun i k -> i + k + 1) @> |> Lambda.toExpression 
// val toTraverse : Expression<Func<int,int>> = i => (i + 1)

let toInject = <@ Func<int, int>(fun j -> j * 2) @> |> Lambda.toExpression
// val toInject : Expression<Func<int,int>> = j => (j * 2)

type 'T rc = Collections.ObjectModel.ReadOnlyCollection<'T>

let inline visitor (b:^T when ^T:(member Body:Expression) and ^T:(member Parameters:ParameterExpression rc) ) =
    { new ExpressionVisitor() with
        member __.VisitParameter _ = (^T:(member Body:Expression) b)
        member __.VisitLambda x =
            let visitedBody = base.Visit x.Body
            Expression.Lambda(visitedBody, (^T:(member Parameters:ParameterExpression rc) b)) :> Expression
        }
let visited = (visitor toInject).Visit toTraverse
// val visited : Expression = j => ((j * 2) + 1)
(((visited :?> LambdaExpression).Body :?> BinaryExpression).Left :?> BinaryExpression).Left
let f = Expression.Lambda(visited).Compile().DynamicInvoke() |> unbox<Func<int,int>>
let fv = f.Invoke(5) // val it : int = 11

let toTraverse2 = <@ Func<float, float>(fun i -> i + 1.0) @> |> Lambda.toExpression 
// val toTraverse : Expression<Func<int,int>> = i => (i + 1)

let toInject2 = <@ Func<float, float>(fun j -> j * 2.0) @> |> Lambda.toExpression
// val toInject : Expression<Func<int,int>> = j => (j * 2)

let visited2 = (visitor toInject2).Visit toTraverse2

let vLambda2 = Expression.Lambda(visited2)

vLambda2.Body

let f2 = vLambda2.Compile().DynamicInvoke() |> unbox<Func<float,float>>
let fv2 = f2.Invoke(5.0)

let i = 0.0
let VALUES = <@ i + 1.0 @> |> LeafExpressionConverter.QuotationToExpression 



let toInjectP2 = <@ Func<float, float>(fun j -> j * 2.0) @> |> Lambda.toExpression


let visitorP (paramNm:string) (b:LambdaExpression) (P:ParameterExpression rc) =
    { new ExpressionVisitor() with
        member __.VisitParameter param =
            if param.Name = paramNm then
                b.Body
            else
                param
        member __.VisitLambda x =
            let visitedBody = base.Visit x.Body
            let pp =
                P
                |> Seq.map (fun po ->
                    if po.Name = paramNm then
                        b.Parameters
                        |> Seq.item 0
                    else
                        po
                )
            Expression.Lambda(visitedBody, pp) :> Expression
        }

let visitedP = (visitorP "k" toInject toTraverse.Parameters).Visit toTraverse
let visitedP2 = (visitorP "i" toInject toTraverse.Parameters).Visit visitedP


let visitorAllP (inject:Expression) (newParams:ParameterExpression[]) f =
    { new ExpressionVisitor() with
        member __.VisitParameter param =
            let processed = f param inject newParams
            processed
        member __.VisitLambda x =
            let visitedBody = base.Visit x.Body                    
            Expression.Lambda(visitedBody, newParams) :> Expression
        }




let replaceName pNmOriginal pNm2Replace (expr:LambdaExpression) =
    let typOfP2Replace = expr.Parameters |> Seq.find (fun p -> p.Name = pNmOriginal)
    let param_replace = Expression.Parameter(typOfP2Replace.Type, pNm2Replace) 
    let param_handler =
        fun (param:ParameterExpression) inj _ ->
            if param.Name = pNmOriginal then
                inj 
            else
                param :> Expression
    (visitorAllP param_replace (expr.Parameters
                                |> Seq.map (fun param ->
                                    if param.Name = pNmOriginal then
                                        param_replace
                                    else
                                        param
                                )
                                |> Seq.toArray) param_handler).Visit expr


let toTraverseAllP = <@ Func<int, int, int>(fun i k -> i + k) @> |> Lambda.toExpression :> Expression
 
replaceName "i" "m" (toTraverseAllP :?> LambdaExpression)

type TRIVIAL = {
    orz: int
}
    with
        static member (+) (vl : TRIVIAL, vr : TRIVIAL) =
            {
                orz = vl.orz + vr.orz
            }
        static member (+) (vl : TRIVIAL, vr : int) =
            {
                orz = vl.orz + vr
            }
        static member (+) (vl : int, vr : TRIVIAL) =
            {
                orz = vl + vr.orz * 100
            }

//type Int32 with
//    static member (+) (vl : int, vr : TRIVIAL) =
//            {
//                orz = vl + vr.orz
//            }

//let inline (+) (vl : int) (vr : TRIVIAL) =
//    {
//        orz = vl + vr.orz
//    }
123 + {orz=7}

#r "nuget: DiffSharp.Core, 1.0.7-preview1873603133"
#r "nuget: DiffSharp.Backends.Reference, 1.0.7-preview1873603133"
#r "nuget: DiffSharp.Backends.Torch, 1.0.7-preview1873603133"
open DiffSharp
open DiffSharp.Util
let t3 = dsharp.tensor [[1.1; 2.2]; [1.1; 2.2]; [1.1; 2.2]]
1 + t3

let toInjectAllP = <@ Func<float, TRIVIAL>(fun j -> {orz=123}) @> |> Lambda.toExpression :> Expression :?> LambdaExpression

let originalParams = (toTraverseAllP :?> LambdaExpression).Parameters|>Seq.toArray

let param_handler =
    fun (param:ParameterExpression) (inject:Expression) newParams ->
        let newInj = replaceName "j" param.Name (inject :?> LambdaExpression)
        (newInj :?> LambdaExpression).Body


let new_body = (visitorAllP toInjectAllP originalParams param_handler).Visit toTraverseAllP


let p1ToChange = (toTraverseAllP :?> LambdaExpression).Parameters.[0]
param_handler p1ToChange toInjectAllP 0


let addA = Expression.Parameter(typeof<TRIVIAL>, "a")
let addB = Expression.Parameter(typeof<int>, "b")
let addC = Expression.Parameter(typeof<Tensor>, "c")

Expression.Add(
            addB,
            addA
        )

Expression.Add(
            addC,
            addB
        )

//#r @"nuget: System.Linq.Dynamic"
#r @"nuget: System.Linq.Dynamic.Core"
//#r @"nuget: EntityFramework"
//#r @"C:\Program Files (x86)\Reference Assemblies\Microsoft\Framework\.NETFramework\v4.0\System.Data.Entity.dll"
//#r @"C:\Program Files (x86)\Reference Assemblies\Microsoft\Framework\.NETFramework\v4.0\System.Data.Entity.Design.dll"
open System.Linq.Expressions
open System.Linq.Dynamic
open System.Linq.Dynamic.Core

open System
//let strExp = @"(Person.Age > 3 AND Person.Weight > 50) OR Person.Age < 3"
let strExp = @"psn.Age + 1"

type Person =
    {
      Name: string
      Weight: int
      FavouriteDay:DateTime
      Age: int
    }


let expParam = Expression.Parameter(typeof<Person>, "psn")
let e2parse = System.Linq.Dynamic.Core.DynamicExpressionParser.ParseLambda([| expParam |], null, strExp)


e2parse.Body.GetType().FullName


Expression.Lambda(
    e2parse.Body,
    expParam
).Compile().DynamicInvoke([|box {Name="";Weight=123;FavouriteDay=Unchecked.defaultof<DateTime>;Age=3}|])


let strExp2 = @"psn + 1"

let expParam2 = Expression.Parameter(typeof<int>, "psn")
let e2parse2 = System.Linq.Dynamic.Core.DynamicExpressionParser.ParseLambda([| expParam2 |], null, strExp2)
