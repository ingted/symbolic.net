open System.Collections.Generic
open FSharp.Quotations.ExprShape
open FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Linq.RuntimeHelpers

type Record = {
    A: int
}
type Dict () = //this is the type the c# lib wants (a dictionary representation of a type)
    inherit Dictionary<string, obj>()

let substitute<'a> (ex: Expr<'a->bool>) =
    let arg = 
          match ex with 
          | ShapeLambda (v, _) -> v
          | _ -> failwith "This is not a lambda. Shouldn't happen."

    let newArg = Var("arg", typeof<Dict>)
    let replaceVar (v: Var) = if v = arg then newArg else v

    let tEntityItem = typeof<Dict>.GetProperty("Item")
    let isATypeShapeVar = function | ShapeVar var -> var.Type = typeof<'a> | _ -> false
    let rec substituteExpr =
        function
        | PropertyGet (Some (ShapeVar a), propOrValInfo, c) when a = arg ->
            let getter = Expr.PropertyGet(Expr.Var newArg, tEntityItem, [Expr.Value(propOrValInfo.Name)] )
            Expr.Coerce(getter, propOrValInfo.PropertyType)
        | ShapeVar var -> Expr.Var (var |> replaceVar)
        | ShapeLambda (var, expr) -> Expr.Lambda(var |> replaceVar, substituteExpr expr)
        | ShapeCombination(shapeComboObject, exprList) ->
            RebuildShapeCombination(shapeComboObject, List.map substituteExpr exprList)
        | ex -> ex

    substituteExpr ex |> LeafExpressionConverter.QuotationToExpression



substitute <@ fun t -> let z = { A = 15 } in z.A = 15 && t.A = 10 @>


open System.Linq.Expressions
open System

let toLinq (expr : Expr<'a -> 'b>) =
    let linq = LeafExpressionConverter.QuotationToExpression expr
    let call = linq :?> MethodCallExpression
    let lambda = call.Arguments.[0] :?> LambdaExpression
    Expression.Lambda<Func<'a, 'b>>(lambda.Body, lambda.Parameters) 

let toLinq2<'T> (expr : Expr) =
    let linq = LeafExpressionConverter.QuotationToExpression expr
    let call = linq :?> MethodCallExpression
    let lambda = call.Arguments.[0] :?> LambdaExpression
    Expression.Lambda<'T>(lambda.Body, lambda.Parameters) 

(toLinq (<@ fun a -> a + 1 @>)).Compile().Invoke(123)


(toLinq2<Func<int, int>> (<@@ fun a -> a + 1 @@>)).Compile().Invoke(123) //not work

type ExprHelper = 
  static member Quote(e:Expression<System.Func<int, int>>) = e

let two = 2
let expr = ExprHelper.Quote(fun x -> x * two) 
expr.Compile().Invoke(4)


let expr1 = 
  <@ System.Func<_, _>(fun x -> x * two) @>
  |> LeafExpressionConverter.QuotationToExpression 
  |> unbox<Expression<Func<int, int>>>
expr1.Compile().Invoke(4) // desired to return 8


let expr2 = 
  <@@ System.Func<_, _>(fun x -> x * two) @@>
  |> LeafExpressionConverter.QuotationToExpression 
  |> unbox<Expression<Func<int, int>>>
expr2.Compile().Invoke(4) // desired to return 8



let expr3 = 
  <@@ System.Func<_, _, _>(fun x y -> x + y) @@>
  |> LeafExpressionConverter.QuotationToExpression 
  |> unbox<Expression<Func<int, int, int>>>
expr3.Compile().Invoke(1,2) // desired to return 8


let expr4 = 
  <@@ System.Func<_>(fun () -> 123) @@>
  |> LeafExpressionConverter.QuotationToExpression 
  |> unbox<Expression<Func<int>>>
expr4.Compile().Invoke() // desired to return 8

type ExprHelper2 = 
  static member Quote(e:Expression<System.Func<_>>) = e

let expr5 = ExprHelper2.Quote(fun () -> 123)
expr5.Compile().Invoke()


expr5.Reduce() :?> LambdaExpression


