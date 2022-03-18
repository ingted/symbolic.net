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

let toTraverse = <@ Func<int, int>(fun i -> i + 1) @> |> Lambda.toExpression 
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
