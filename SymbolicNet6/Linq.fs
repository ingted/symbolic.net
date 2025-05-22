namespace MathNet.Symbolics

open System
open System.Collections.Generic
open MathNet.Symbolics
open MathNet.Numerics
open System.Linq.Expressions


open ExpressionPatterns
open Operators
//open Evaluate
open MathNet.Numerics.LinearAlgebra
open Definition
#if TENSOR_SUPPORT
open DiffSharp
#endif
open System.Collections.Concurrent
//open PersistedConcurrentSortedList
//open Deedle
open System.Runtime.InteropServices
open System.Runtime.CompilerServices

module TupleHelpers =    
    let inline tp1 (a,_,_) = a
    let inline tp2 (_,b,_) = b
    let inline tp3 (_,_,c) = c
    let inline tp13 (a,_,c) = a,c

    let inline qp1 (a,_,_,_) = a
    let inline qp2 (_,b,_,_) = b
    let inline qp3 (_,_,c,_) = c
    let inline qp4 (_,_,_,d) = d

[<RequireQualifiedAccess>]
module Linq =
    open Microsoft.FSharp.Linq.RuntimeHelpers
    open MathNet.Numerics.LinearAlgebra
    let ivk (e:Expression) =
        if e.Type.Name = "Func`2" then
            let aparam = Expression.Parameter(typeof<IDictionary<string, FloatingPoint>>)
            Expression.Invoke(e, aparam) :> Expression
        else
            e
    module Option =
        let map2 f a b = a |> Option.bind (fun a' -> b |> Option.map (fun b' -> f a' b'))

    type ExprHelper () =
        static member val evaluate : IDictionary<string,FloatingPoint> -> MathNet.Symbolics.Expression -> FloatingPoint = Unchecked.defaultof<(IDictionary<string,FloatingPoint> -> MathNet.Symbolics.Expression -> FloatingPoint)> with get, set
        static member Quote<'T>(e:Expression<'T>) = e
        static member toExpression (``f# lambda`` : Quotations.Expr<'a>) =
            ``f# lambda``
            |> LeafExpressionConverter.QuotationToExpression 
            |> unbox<Expression<'a>>


    type MyOps =
        static member PointwiseMultiply(a: float[], b: float[]) =
            Array.map2 (*) a b
        static member PointwiseMultiply(a: Vector<float>, b: Vector<float>) =
            a.PointwiseMultiply b
        static member PointwiseMultiply(a: Value, b: Value) =
            a.ValueRealVec.PointwiseMultiply b.ValueRealVec |> Value.RealVec
        static member PointwiseMultiply(a: int[], b: int[]) =
            Array.map2 (*) a b
        static member PointwiseMultiply(a: decimal[], b: decimal[]) =
            Array.map2 (*) a b

    [<CompiledName("Parse")>]
    let rec parse (q: System.Linq.Expressions.Expression) : MathNet.Symbolics.Expression =
        match q.NodeType, q with
        | ExpressionType.UnaryPlus, (:? UnaryExpression as e) -> +(parse e.Operand)
        | ExpressionType.Negate, (:? UnaryExpression as e) -> -(parse e.Operand)
        | ExpressionType.Add, (:? BinaryExpression as e) -> (parse e.Left) + (parse e.Right)
        | ExpressionType.Subtract, (:? BinaryExpression as e) -> (parse e.Left) - (parse e.Right)
        | ExpressionType.Multiply, (:? BinaryExpression as e) -> (parse e.Left) * (parse e.Right)
        | ExpressionType.Divide, (:? BinaryExpression as e) -> (parse e.Left) / (parse e.Right)
        | ExpressionType.Constant, (:? ConstantExpression as e) -> fromInt64 (Convert.ToInt64(e.Value))
        | ExpressionType.Parameter, (:? ParameterExpression as e) -> Identifier (Symbol e.Name)
        | ExpressionType.MemberAccess, (:? MemberExpression as e) -> Identifier (Symbol e.Member.Name)
        | ExpressionType.Lambda, (:? LambdaExpression as e) -> parse e.Body
        | ExpressionType.Try, (:? TryExpression as e) -> parse e.Body
        | ExpressionType.Convert, (:? UnaryExpression as e) -> parse e.Operand
        | ExpressionType.Call, (:? MethodCallExpression as e) when
            e.Method.Name = "PointwiseMultiply" &&
            e.Method.DeclaringType = typeof<MyOps> ->
                printfn "PointwiseMultiply"
                pointwiseMultiply (parse e.Arguments[0]) (parse e.Arguments[1])
        | _ ->
            failwith $"NodeType {q.NodeType} not supported"

    let rec private numerator = function
        | NegPower _ -> one
        | Product ax -> product <| List.map numerator ax
        | z -> z

    let rec private denominator = function
        | NegPower (r, p) -> r ** -p
        | Product ax -> product <| List.map denominator ax
        | _ -> one

    //let rec translateExpr (linq:Expression) = 
    //    match linq with
    //    | :? MethodCallExpression as mc ->
    //        let le = mc.Arguments.[0] :?> LambdaExpression
    //        let args, body = translateExpr le.Body
    //        le.Parameters.[0] :: args, body
    //    | _ -> [], linq

    //20250406 取代 translateExpr
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

    type 'T rc = Collections.ObjectModel.ReadOnlyCollection<'T>

    type Expression with
        member this.LambdaExprFindSingleParam() =
            (this :?> LambdaExpression).Parameters.[0]
        member this.LambdaExprFindSingleParamType() =
            this.LambdaExprFindSingleParam().Type
        member this.LambdaBody() =
            (this :?> LambdaExpression).Body

    let exprObj2ValueToInject = //: Expression<Func<obj, MathNet.Symbolics.Value>> =
        ExprHelper.Quote<Func<obj, MathNet.Symbolics.Value>> (fun j ->
            match j with
            | :? Value as v -> v
            //| _ when j.GetType() = typeof<float> -> //20250406 應該不用這樣寫
            | :? float as v ->
                //failwith "orz"
                //MathNet.Symbolics.Value.fromDouble  0.0
                Value.Approximation (Approximation.Real v)
            | :? Vector<float> as v ->
                Value.RealVec v
            | :? Matrix<float> as v ->
                Value.RealMat v
            | _ ->
                failwithf "exprObj2ValueToInject: %s, %A" (j.GetType().FullName) j
            )
            :> Expression :?> LambdaExpression

           
    let exprFloatingPoint2ValueToInject = 
        let rec h (j:FloatingPoint) =
            match j with
            | Real r -> Value.Approximation (Approximation.Real r)
            | Complex c -> Value.fromComplex c
            | RealVector rv ->
                Value.RealVec rv
            | RealMatrix rm ->
                Value.RealMat rm
#if TENSOR_SUPPORT
            | WTensor (DSTensor dt) -> Value.DSTen dt
#endif
            | NestedList l ->
                //let ll = l |> List.map h
                if l.Length = 0 then
                    Value.Empty
                else
                    match l[0] with
                    | Real _ -> Value.RealVec (Vector<float>.Build.DenseOfEnumerable (l |> Seq.map (fun lv -> lv.RealValue)))
               
            | _ ->
                failwithf "exprFloatingPoint2ValueToInject not supported!!! %A" j
        ExprHelper.Quote<Func<FloatingPoint, MathNet.Symbolics.Value>> (h)
            :> Expression :?> LambdaExpression



    let visitorP (paramIdx:int) (b:Expression) (p:ParameterExpression[]) =
        { new ExpressionVisitor() with
            member __.VisitParameter param =
                if p.Length > paramIdx then
                    if param.Name = p.[paramIdx].Name then
                        let casted = Expression.Convert(b, typeof<obj>) :> Expression
                        let ivk = Expression.Invoke(exprObj2ValueToInject, [|casted|])
                        ivk
                    else
                        param
                else
                    param
            member __.VisitLambda x =
                let visitedBody = base.Visit x.Body
                Expression.Lambda(visitedBody, p)
            }

            

    let visitorAllP (inject:Expression) (newParams:ParameterExpression[]) f =
        let mutable np = newParams
        { new ExpressionVisitor() with
            member __.VisitParameter param =
                let processed = f param inject np
                processed
            member __.VisitLambda x =
                let visitedBody = base.Visit x.Body                    
                Expression.Lambda(visitedBody, np) :> Expression
            member __.VisitBinary b =
                //if b.Left.Type = typeof<float> && b.Right.Type = typeof<Value> && b.NodeType = ExpressionType.Add then
                //    failwithf "orz"
                //else
                    
                    let bOut =
                        b.Update(
                            base.Visit(b.Left),
                            base.VisitAndConvert(b.Conversion, "VisitBinary"),
                            base.Visit(b.Right)
                        )
                    bOut
            member __.VisitUnary node =
                node.Update(base.Visit(node.Operand))
            member __.VisitInvocation node =
                try
                    base.VisitInvocation(node)
                with
                | exn ->
                    failwithf "VisitInvocation exn: %A" exn
            }

    let visitorAllP2 (newParams:ParameterExpression[]) funNewParam2ParamExp =
        let npDict = newParams |> Seq.map (fun p -> p.Name, p) |> dict
        { new ExpressionVisitor() with
            member __.VisitParameter param =
                let newExp = funNewParam2ParamExp param npDict
                newExp
            member __.VisitLambda x =
                let visitedBody = base.Visit x.Body                    
                Expression.Lambda(visitedBody, newParams) :> Expression
            member __.VisitBinary b =
                let bOut =
                    b.Update(
                        base.Visit(b.Left),
                        base.VisitAndConvert(b.Conversion, "VisitBinary"),
                        base.Visit(b.Right)
                    )
                bOut
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
        printfn "replaceName: %s" pNmOriginal
        (visitorAllP param_replace (expr.Parameters
                                    |> Seq.map (fun param ->
                                        if param.Name = pNmOriginal then
                                            param_replace
                                        else
                                            param
                                    )
                                    |> Seq.toArray) param_handler).Visit expr


    let replaceType pNm (expr:LambdaExpression) =
        let param_exp_replace =
            //Expression.Parameter(pType2Replace, pNm)
            (replaceName "j" pNm exprObj2ValueToInject)
        let param_replace = param_exp_replace.LambdaExprFindSingleParam()
        let param_handler =
            fun (param:ParameterExpression) inj _ ->
                if param.Name = pNm then
                    inj 
                else
                    param :> Expression
        printfn "replaceType: %A" expr
        (visitorAllP (param_exp_replace.LambdaBody()) (expr.Parameters
                                    |> Seq.map (fun param ->
                                        if param.Name = pNm then
                                            param_replace
                                        else
                                            param
                                    )
                                    |> Seq.toArray) param_handler).Visit expr

    let visitorLambda (paramNm:string) (b:LambdaExpression) (p:ParameterExpression rc) =
        { new ExpressionVisitor() with
            member __.VisitParameter param =
                if param.Name = paramNm then
                    b.Body
                else
                    param
            member __.VisitLambda x =
                let visitedBody = base.Visit x.Body
                let pp =
                    p
                    |> Seq.map (fun po ->
                        if po.Name = paramNm then
                            b.Parameters
                            |> Seq.item 0
                        else
                            po
                    )
                Expression.Lambda(visitedBody, pp) :> Expression
            }

    //let pointwiseMulExpr (a: Expression) (b: Expression) : Expression =
    //    // 呼叫你預先註冊的靜態方法（如 MyOps.PointwiseMultiply）
    //    Expression.Call(typeof<MyOps>.GetMethod("PointwiseMultiply", [| typeof<Vector<float>>; typeof<Vector<float>> |]), a, b)

    let callPointwise x y =
        Expression.Call(typeof<MyOps>.GetMethod("PointwiseMultiply", [| typeof<Value>; typeof<Value> |]), x, y) :> Expression
    let sharedPointwiseMul (a: Expression) (b: Expression) : Expression =

        match a.NodeType, b.NodeType with
        | ExpressionType.Lambda, ExpressionType.Lambda ->
            let al = a :?> LambdaExpression
            let bl = b :?> LambdaExpression
            let allParams =
                Seq.append al.Parameters bl.Parameters
                |> Seq.distinct
            let body =
                callPointwise al.Body bl.Body
            Expression.Lambda(body, allParams) :> Expression

        | ExpressionType.Lambda, _ ->
            let al = a :?> LambdaExpression
            let body = callPointwise al.Body b
            Expression.Lambda(body, al.Parameters) :> Expression

        | _, ExpressionType.Lambda ->
            let bl = b :?> LambdaExpression
            let body = callPointwise a bl.Body
            Expression.Lambda(body, bl.Parameters) :> Expression

        | _, _ ->
            callPointwise a b

    let rec toLambda (expr : MathNet.Symbolics.Expression) (args : Symbol list) (valueType : Type) (mathType : Type) (funcInvokTyp : Type option) constant value add mul div pow atan2 log abs besselj bessely besseli besselk besseliratio besselkratio hankelh1 hankelh2 : LambdaExpression option =
        let valueTypeArr1 = [| valueType |]
        let valueTypeArr2 = [| valueType; valueType |]
        
        let argName = function |Symbol(n) -> n
        let mutable paramList =
            match funcInvokTyp with
            | Some t ->
                List.map (fun x -> Expression.Parameter(t, argName x)) args
            | None ->
                List.map (fun x -> Expression.Parameter(valueType, argName x)) args
        let getParam p = List.fold (fun x (y : ParameterExpression) ->
            match x with
                | None when y.Name = (argName p) -> Some y
                | Some(v) -> Some v
                | _ -> None) None paramList
        let mathCall1 (name : string) (a : Expression) = Expression.Call(mathType.GetMethod(name, valueTypeArr1), a) :> Expression
        //let mathCall2 (name : string) (a : Expression) (b : Expression) = Expression.Call(mathType.GetMethod(name, valueTypeArr2), a, b) :> Expression
        let rec convertExpr : MathNet.Symbolics.Expression -> Expression option = function
            | FunInvocation (Symbol fnm, xs) ->
                let xsv = xs |> List.choose convertExpr
                let fBody = Definition.funDict.[fnm]
                match fBody with
                | DTExp (param, bodyDef) ->

                    let (Some exprBy2Lambda) = formatValueLambda bodyDef param

                    //let expParam =
                    //    param
                    //    |> Seq.map (fun (Symbol s) ->
                    //        Expression.Parameter(typeof<Value>, s)
                    //    )

                    //let (Some bodyExp) =
                    //    let oldParamList = paramList
                    //    paramList <- expParam |> Seq.toList
                    //    let be = convertExpr bodyDef
                    //    paramList <- oldParamList
                    //    be

                    //let lambda =
                    //    Expression.Lambda(
                    //        bodyExp,
                    //        expParam
                    //    )

                    //let vLambda_base =                        
                    //    (visitorAllP2 (expParam |> Seq.toArray) (fun p paDict ->
                    //        if paDict.ContainsKey p.Name then
                    //            paDict.[p.Name]
                    //        else
                    //            p
                    //        :> Expression
                    //    )).Visit (lambda:>Expression) :?> LambdaExpression

                    //let vLambda, _ =
                    //    List.fold (fun ((s:LambdaExpression), idx) a ->
                    //        let sParam = s.Parameters |> Seq.toArray
                    //        //let s_nxt = Expression.Lambda((visitorP idx a sParam).Visit (s:>Expression))                            
                    //        let s_nxt = (visitorP idx a sParam).Visit (s:>Expression)
                    //        s_nxt :?> LambdaExpression, idx + 1
                    //    ) (exprBy2Lambda, 0) xsv

                    let xsvv =
                        xsv
                        |> List.map (fun xsExp ->
                            let casted = Expression.Convert(xsExp, typeof<obj>) :> Expression
                            let ivk = Expression.Invoke(exprObj2ValueToInject, [|casted|])
                            ivk :> Expression
                        )


                    let vLambda = Expression.Invoke(exprBy2Lambda, xsvv)

                    Some (vLambda :> Expression)
                //| DTCurF3toV1 (f, (Symbol sym)) ->
                | compSupp ->
                    failwithf "havent yet supported compilation"
            | Identifier(sym) ->
                Option.map (fun x -> x :> Expression) (getParam sym)
            | Argument(sym) ->
                Option.map (fun x -> x :> Expression) (getParam sym)
            | Values.Value v -> value v
            | Constant c -> constant c
            | Function(func, par) ->
                let convertFunc : Function -> (Expression -> Expression) option = function
                    | Sin  -> Some (mathCall1 "Sin")
                    | Cos  -> Some (mathCall1 "Cos")
                    | Tan  -> Some (mathCall1 "Tan")
                    | Csc  -> Some (mathCall1 "Csc")
                    | Sec  -> Some (mathCall1 "Sec")
                    | Cot  -> Some (mathCall1 "Cot")
                    | Sinh -> Some (mathCall1 "Sinh")
                    | Cosh -> Some (mathCall1 "Cosh")
                    | Tanh -> Some (mathCall1 "Tanh")
                    | Csch  -> Some (mathCall1 "Csch")
                    | Sech  -> Some (mathCall1 "Sech")
                    | Coth  -> Some (mathCall1 "Coth")
                    | Asin -> Some (mathCall1 "Asin")
                    | Acos -> Some (mathCall1 "Acos")
                    | Atan -> Some (mathCall1 "Atan")
                    | Acsc -> Some (mathCall1 "Acsc")
                    | Asec -> Some (mathCall1 "Asec")
                    | Acot -> Some (mathCall1 "Acot")
                    | Asinh -> Some (mathCall1 "Asinh")
                    | Acosh -> Some (mathCall1 "Acosh")
                    | Atanh -> Some (mathCall1 "Atanh")
                    | Acsch -> Some (mathCall1 "Acsch")
                    | Asech -> Some (mathCall1 "Asech")
                    | Acoth -> Some (mathCall1 "Acoth")
                    | AiryAi -> Some (mathCall1 "AiryAi")
                    | AiryAiPrime -> Some (mathCall1 "AiryAiPrime")
                    | AiryBi -> Some (mathCall1 "AiryBi")
                    | AiryBiPrime -> Some (mathCall1 "AiryBiPrime")
                    | Ln   -> Some (mathCall1 "Log")
                    | Lg  -> Some (mathCall1 "Log10")
                    | Exp  -> Some (mathCall1 "Exp")
                    | Abs  -> Some abs
                let f = convertFunc func
                let e = convertExpr par
                Option.map2 id f e
            | FunctionN(Atan2, [x;y]) ->
                let exprX = convertExpr x
                let exprY = convertExpr y
                Option.map2 atan2 exprX exprY
            | FunctionN(Log, [x;y]) ->
                let exprX = convertExpr x
                let exprY = convertExpr y
                Option.map2 log exprX exprY
            | FunctionN(BesselJ, [nu;x]) ->
                let exprX = convertExpr nu
                let exprY = convertExpr x
                Option.map2 besselj exprX exprY
            | FunctionN(BesselY, [nu;x]) ->
                let exprX = convertExpr nu
                let exprY = convertExpr x
                Option.map2 bessely exprX exprY
            | FunctionN(BesselI, [nu;x]) ->
                let exprX = convertExpr nu
                let exprY = convertExpr x
                Option.map2 besseli exprX exprY
            | FunctionN(BesselK, [nu;x]) ->
                let exprX = convertExpr nu
                let exprY = convertExpr x
                Option.map2 besselk exprX exprY
            | FunctionN(BesselIRatio, [nu;x]) ->
                let exprX = convertExpr nu
                let exprY = convertExpr x
                Option.map2 besseliratio exprX exprY
            | FunctionN(BesselKRatio, [nu;x]) ->
                let exprX = convertExpr nu
                let exprY = convertExpr x
                Option.map2 besselkratio exprX exprY
            | FunctionN(HankelH1, [nu;x]) ->
                let exprX = convertExpr nu
                let exprY = convertExpr x
                Option.map2 hankelh1 exprX exprY
            | FunctionN(HankelH2, [nu;x]) ->
                let exprX = convertExpr nu
                let exprY = convertExpr x
                Option.map2 hankelh2 exprX exprY
            | FunctionN(_) -> None
            | PosIntPower(x, Number(y)) ->
                let basis = convertExpr x
                let rec exponentiate (power : BigRational) exp  =
                    if  power.Numerator.IsEven then
                        let newBasis = mul exp exp
                        exponentiate (power / 2N) newBasis
                    elif power = 1N then
                        exp
                    else
                        let newBasis = exponentiate (power - 1N) exp
                        mul exp newBasis
                Option.map (exponentiate y) basis
            | Power(x, m) when m = minusOne ->
                let a = convertExpr x
                Option.map2 div (value Value.one) a
            | Power (x, Power(n, m)) when m = minusOne ->
                let a = convertExpr x
                //let b = convertExpr (Power(n, m))
                if n = two then
                    Option.map (mathCall1 "Sqrt") a
                else
                    let a = convertExpr x
                    let b = convertExpr (Power(n, m))
                    Option.map2 pow a b
            | Power(Constant E, y) ->
                let exponent = convertExpr y
                Option.map (mathCall1 "Exp") exponent
            | Power(x, y) ->
                let baseE = convertExpr x
                let exponE = convertExpr y
                Option.map2 pow baseE exponE
            | Sum(xs) ->
                let summands = List.map convertExpr xs
                let exprv = List.fold (Option.map2 add) (value Value.zero) summands
                //let vv =
                //    match exprv with
                //    | Some exprvv -> exprvv
                //    | None ->
                //        Unchecked.defaultof<Expression>
                exprv
            | Product(_) as p ->
                let n = numerator p
                let d = denominator p
                if isOne d then
                    compileFraction n
                else
                    let nExp = compileFraction n
                    let dExp = compileFraction d
                    Option.map2 div nExp dExp
            | PointwiseMul (x, y) ->
                let a = convertExpr x
                let b = convertExpr y
                Option.map2 sharedPointwiseMul a b
            | Undefined -> None
        and compileFraction = function
            | Product(xs) ->
                let prods = List.map convertExpr xs
                let fRtn = List.fold (Option.map2 mul) (value Value.one) prods
                fRtn
            | x -> convertExpr x
        let simplifiedBody = Trigonometric.simplify expr
        Option.map (fun (body:Expression) ->
            //if body.NodeType = ExpressionType.Lambda then

            //    let toInject = <@ Func<float, Value>(fun j -> Value.Approximation (Approximate.real j)) @> |> ExprHelper.toExpression

            //    //let param_handler =
            //    //    fun param b p ->
            //    //        let ivxExp = Expression.Invoke(b, [|param :> Expression |])
            //    //        ivxExp :> Expression
            //    let param_handler =
            //        fun (param:ParameterExpression) (inject:Expression) (newParams:ParameterExpression[]) ->
            //            let newInj = replaceName "j" param.Name (inject :?> LambdaExpression)
            //            let paramIdx =
            //                newParams
            //                |> Array.findIndex (fun p -> p.Name = param.Name)
            //            newParams.[paramIdx] <- newInj.LambdaExprFindSingleParam()
            //                //Expression.Parameter(newInj.LambdaExprFindSingleParamType(), param.Name)
            //            (newInj :?> LambdaExpression).Body

            //    let originalParams = (body :?> LambdaExpression).Parameters|>Seq.toArray

            //    let new_body = (visitorAllP toInject originalParams param_handler).Visit body


            //    let ivx =
            //        Expression.Lambda(
            //            Expression.Invoke(new_body, paramList |> Seq.map (fun p -> p :> Expression)),
            //            //new_body.LambdaBody(),
            //            paramList
            //        )
            //    ivx
            //else
                Expression.Lambda(body, paramList)

            ) (convertExpr simplifiedBody)
    and sharedMul (a:Expression) (b:Expression) = //Expression.Multiply(a, b) :> Expression
            match a.NodeType, b.NodeType with
            | (ExpressionType.Lambda, ExpressionType.Lambda) ->
                let al = a:?>LambdaExpression
                let bl = b:?>LambdaExpression

                let distParam =
                    seq [al.Parameters; bl.Parameters]
                    |> Seq.concat
                    |> Seq.distinct
                let bexprm =
                    Expression.Lambda(
                                Expression.Multiply(al.Body, bl.Body),
                                distParam
                            )
                bexprm :> Expression
                

            | (ExpressionType.Lambda, bt) when bt <> ExpressionType.Lambda ->
                let al = a:?>LambdaExpression
                let aexprm =
                    Expression.Lambda(
                            Expression.Multiply(al.Body, b),
                            al.Parameters
                        )                     
                aexprm :> Expression
            | (at, ExpressionType.Lambda) when at <> ExpressionType.Lambda ->
                let bl = b:?>LambdaExpression
                Expression.Lambda(
                            Expression.Multiply(a, bl.Body),
                            bl.Parameters
                        )
                     :> Expression
            | (at, bt) when bt <> ExpressionType.Lambda && at <> ExpressionType.Lambda ->
                Expression.Multiply(a, b) :> Expression

    and value_VT = function
            | Value.Approximation a -> Some (Expression.Constant a.RealValue :> Expression)
            | Value.NegativeInfinity -> Some (Expression.Constant System.Double.NegativeInfinity :> Expression)
            | Value.PositiveInfinity -> Some (Expression.Constant System.Double.PositiveInfinity :> Expression)
            | Value.Number n -> Some (Expression.Constant (float n) :> Expression)
            | Value.RealVec v ->
                Some (Expression.Constant v :> Expression)
            | Value.ComplexVec v ->
                Some (Expression.Constant v :> Expression)
            | Value.RealMat v ->
                Some (Expression.Constant v :> Expression)
            | Value.ComplexMat v ->
                Some (Expression.Constant v :> Expression)
            | _ ->
                None
    and constant_VT = function
            | E -> Some (Expression.Constant Constants.E :> Expression)
            | Pi -> Some (Expression.Constant Constants.Pi :> Expression)
            | _ -> None
    and valueTypeFloat = typeof<float>
    and mathType = typeof<System.Math>
    and add_VT a b = Expression.Add(a, b) :> Expression
    and div_VT a b = Expression.Divide(a, b) :> Expression
    and mathCall1 (name : string) (a : Expression) = Expression.Call(mathType.GetMethod(name, [| valueTypeFloat |]), a) :> Expression
    and mathCall2 (name : string) (a : Expression) (b : Expression) = Expression.Call(mathType.GetMethod(name, [| valueTypeFloat; valueTypeFloat |]), a, b) :> Expression
    and pow_VT = mathCall2 "Pow"
    and atan2_VT = mathCall2 "Atan2"
    and log_VT a b = mathCall2 "Log" b a
    and abs_VT = mathCall1 "Abs"
    and [<CompiledName("FormatValueLambda")>] formatValueLambda (expr : MathNet.Symbolics.Expression) (args : Symbol list) : LambdaExpression option =
        let mul = sharedMul
        formatLambdaBase expr args valueTypeFloat mathType (Some typeof<Value>) mathCall2 constant_VT value_VT add_VT mul div_VT pow_VT atan2_VT log_VT abs_VT
    
    //and value_T = function
    //        | Value.Approximation a -> Some (Expression.Constant a.RealValue :> Expression)
    //        | Value.NegativeInfinity -> Some (Expression.Constant System.Double.NegativeInfinity :> Expression)
    //        | Value.PositiveInfinity -> Some (Expression.Constant System.Double.PositiveInfinity :> Expression)
    //        | Value.Number n -> Some (Expression.Constant (float n) :> Expression)
    //        //20250413 加入了這幾個，如果有問題要拿掉
    //        | Value.RealVec v ->
    //            Some (Expression.Constant v :> Expression)
    //        | Value.ComplexVec v ->
    //            Some (Expression.Constant v :> Expression)
    //        | Value.RealMat v ->
    //            Some (Expression.Constant v :> Expression)
    //        | Value.ComplexMat v ->
    //            Some (Expression.Constant v :> Expression)
    //        | _ -> None
    //and constant_T = function
    //        | E -> Some (Expression.Constant Constants.E :> Expression)
    //        | Pi -> Some (Expression.Constant Constants.Pi :> Expression)
    //        | _ -> None
    
    //and add_T a b = Expression.Add(a, b) :> Expression

    //and div_T a b = Expression.Divide(a, b) :> Expression
    //and pow_T = mathCall2 "Pow"
    //and atan2_T = mathCall2 "Atan2"
    //and log_T a b = mathCall2 "Log" b a
    //and abs_T = mathCall1 "Abs"
    and [<CompiledName("FormatLambda")>] formatLambda (expr : MathNet.Symbolics.Expression) (args : Symbol list) : LambdaExpression option =
        //let mul (a:Expression) (b:Expression) = //Expression.Multiply(a, b) :> Expression
        //    match a.NodeType, b.NodeType with
        //    | (ExpressionType.Lambda, ExpressionType.Lambda) ->
        //        let al = a:?>LambdaExpression
        //        let bl = b:?>LambdaExpression

        //        let distParam =
        //            seq [al.Parameters; bl.Parameters]
        //            |> Seq.concat
        //            |> Seq.distinct
        //        let bexprm =
        //            Expression.Lambda(
        //                        Expression.Multiply(al.Body, bl.Body),
        //                        distParam
        //                    )
        //        bexprm :> Expression
                

        //    | (ExpressionType.Lambda, bt) when bt <> ExpressionType.Lambda ->
        //        let al = a:?>LambdaExpression
        //        let aexprm =
        //            Expression.Lambda(
        //                    Expression.Multiply(al.Body, b),
        //                    al.Parameters
        //                )                     
        //        aexprm :> Expression
        //    | (at, ExpressionType.Lambda) when at <> ExpressionType.Lambda ->
        //        let bl = b:?>LambdaExpression
        //        Expression.Lambda(
        //                    Expression.Multiply(a, bl.Body),
        //                    bl.Parameters
        //                )
        //             :> Expression
        //    | (at, bt) when bt <> ExpressionType.Lambda && at <> ExpressionType.Lambda ->
        //        Expression.Multiply(a, b) :> Expression
        let mul_T = sharedMul
        formatLambdaBase expr args valueTypeFloat mathType None mathCall2 constant_VT value_VT add_VT mul_T div_VT pow_VT atan2_VT log_VT abs_VT

    and besselj = mathCall2 "BesselJ"
    and bessely = mathCall2 "BesselY"
    and besseli = mathCall2 "BesselI"
    and besselk = mathCall2 "BesselK"
    and besseliratio = mathCall2 "BesselIRatio"
    and besselkratio = mathCall2 "BesselKRatio"
    and hankelh1 = mathCall2 "HankelH1"
    and hankelh2 = mathCall2 "HankelH2"
    and [<CompiledName("FormatLambdaBase")>] formatLambdaBase (expr : MathNet.Symbolics.Expression) (args : Symbol list)
            valueType mathType (funcInvokTyp : Type option) mathCall2 constant value add mul div pow atan2 log abs
            : LambdaExpression option =        
        toLambda expr args valueType mathType funcInvokTyp constant value add mul div pow atan2 log abs besselj bessely besseli besselk besseliratio besselkratio hankelh1 hankelh2

    [<CompiledName("FormatComplexLambda")>]
    let formatComplexLambda (expr : MathNet.Symbolics.Expression) (args : Symbol list) : LambdaExpression option =
        let value = function
            | Value.Approximation a -> Some (Expression.Constant a.ComplexValue :> Expression)
            | Value.NegativeInfinity -> Some (Expression.Constant (complex System.Double.NegativeInfinity 0.0) :> Expression)
            | Value.PositiveInfinity -> Some (Expression.Constant (complex System.Double.PositiveInfinity 0.0) :> Expression)
            | Value.Number n -> Some (Expression.Constant (complex (float n) 0.0) :> Expression)
            | _ -> None
        let constant = function
            | E -> Some (Expression.Constant (complex Constants.E 0.0) :> Expression)
            | Pi -> Some (Expression.Constant (complex Constants.Pi 0.0) :> Expression)
            | I -> Some (Expression.Constant (complex 0.0 1.0) :> Expression)
            //| _ -> None
        let valueTypeComplex = typeof<complex>
        let mathTypeComplex = typeof<complex>
        let mathCall1Complex (name : string) (a : Expression) = Expression.Call(mathTypeComplex.GetMethod(name, [| valueTypeComplex |]), a) :> Expression
        let mathCall2Complex (name : string) (a : Expression) (b : Expression) = Expression.Call(mathTypeComplex.GetMethod(name, [| valueTypeComplex; valueTypeComplex |]), a, b) :> Expression
        let add = mathCall2Complex "Add"
        let mul = mathCall2Complex "Multiply"
        let div = mathCall2Complex "Divide"
        let pow = mathCall2Complex "Pow"
        let atan2 a b = mathCall1Complex "Atan" (div a b)
        let log a b =
            let ln = mathCall1Complex "Log"
            div (ln b) (ln a)
        let abs a = Expression.Convert(mathCall1Complex "Abs" a, valueTypeComplex) :> Expression
        formatLambdaBase expr args valueTypeComplex mathTypeComplex None mathCall2Complex constant value add mul div pow atan2 log abs
        //let besselj = mathCall2 "BesselJ"
        //let bessely = mathCall2 "BesselY"
        //let besseli = mathCall2 "BesselI"
        //let besselk = mathCall2 "BesselK"
        //let besseliratio = mathCall2 "BesselIRatio"
        //let besselkratio = mathCall2 "BesselKRatio"
        //let hankelh1 = mathCall2 "HankelH1"
        //let hankelh2 = mathCall2 "HankelH2"
        //toLambda expr args valueType mathType constant value add mul div pow atan2 log abs besselj bessely besseli besselk besseliratio besselkratio hankelh1 hankelh2

module Compile =
    let compiledCache0 = new System.Collections.Concurrent.ConcurrentDictionary<MathNet.Symbolics.Expression * Symbol list, LambdaExpression option>()
    let delegateCache0 = new System.Collections.Concurrent.ConcurrentDictionary<MathNet.Symbolics.Expression * Symbol list, Delegate option>()

    let compiledCache = new System.Collections.Concurrent.ConcurrentDictionary<MathNet.Symbolics.Expression * Symbol list, LambdaExpression>()
    let delegateCache = new System.Collections.Concurrent.ConcurrentDictionary<MathNet.Symbolics.Expression * Symbol list, Delegate>()


    let compiledCache2 = new System.Collections.Concurrent.ConcurrentDictionary<MathNet.Symbolics.Expression * Symbol list, LambdaExpression>()
    let delegateCache2 = new System.Collections.Concurrent.ConcurrentDictionary<MathNet.Symbolics.Expression * Symbol list, Delegate>()

    let complexCache = new System.Collections.Concurrent.ConcurrentDictionary<MathNet.Symbolics.Expression * Symbol list, LambdaExpression option>()
    let delegateComplexCache = new System.Collections.Concurrent.ConcurrentDictionary<MathNet.Symbolics.Expression * Symbol list, Delegate option>()

    let complexCache2 = new System.Collections.Concurrent.ConcurrentDictionary<MathNet.Symbolics.Expression * Symbol list, LambdaExpression option>()
    let delegateComplexCache2 = new System.Collections.Concurrent.ConcurrentDictionary<MathNet.Symbolics.Expression * Symbol list, Delegate>()

    let compileExpression (expr_:MathNet.Symbolics.Expression) (args_:Symbol list) =
        let cmpl =
            delegateCache0.GetOrAdd(
                (expr_, args_)
                , (fun (expr, args) ->
                    let exprv =
                        compiledCache0.GetOrAdd(
                            (expr, args)
                            , fun (expr, args) ->
                                (Linq.formatLambda expr args)
                        )
                    Option.map (fun (x : LambdaExpression) -> x.Compile()) exprv
                )
            )
        cmpl


    let compileComplexExpression (expr_:MathNet.Symbolics.Expression) (args_:Symbol list) =
        delegateComplexCache.GetOrAdd(
            (expr_, args_)
            , fun (expr, args) ->                
                let lambdaExp =
                    complexCache.GetOrAdd(
                        (expr, args)
                        , fun (expr, args) ->
                            Linq.formatComplexLambda expr args
                    )
                Option.map (fun (x : LambdaExpression) -> x.Compile()) lambdaExp
        )

    let compileExpressionOrThrow (expr_:MathNet.Symbolics.Expression) (args_:Symbol list) =
        let cmpl =
            delegateCache.GetOrAdd(
                (expr_, args_)
                , (fun (expr, args) ->
                    let exprv =
                        compiledCache.GetOrAdd(
                            (expr, args)
                            , fun (expr, args) ->
                                (Linq.formatLambda expr args).Value
                        )
                    exprv.Compile()
                )
            )
        cmpl

    let compileExpressionOrThrow2 (expr_:MathNet.Symbolics.Expression) (args_:Symbol list) =
        let exprv =
            compiledCache2.GetOrAdd(
                (expr_, args_)
                , fun (expr, args) ->
                    let exprv_base = (Linq.formatValueLambda expr args).Value

                    let f2vParam =
                        args
                        |> List.map (fun (Symbol s) ->
                            let paramI = Expression.Parameter(typeof<FloatingPoint>, s)
                            paramI
                        ) |> List.toArray

                    let f2v =
                        f2vParam
                        |> Array.map (fun paramI ->
                            let ivk = Expression.Invoke(Linq.exprFloatingPoint2ValueToInject :> Expression, [|paramI:> Expression|])
                            ivk :> Expression
                        )
        
        
                    let exprv =
                        Expression.Lambda(
                            Expression.Invoke(exprv_base:> Expression, f2v) :> Expression
                            , f2vParam
                        )
                    exprv
            )

        let cmpl =
            delegateCache2.GetOrAdd(
                (expr_, args_)
                , (fun _ ->
                    exprv.Compile()
                )
            )
        exprv, cmpl

    let compileExpressionOrThrow2_ (expr_:MathNet.Symbolics.Expression, args_:Symbol list) =
        compileExpressionOrThrow2 expr_ args_

    let compileComplexExpressionOrThrow (expr_:MathNet.Symbolics.Expression) (args_:Symbol list) =

        let cmpl =
            delegateComplexCache2.GetOrAdd(
                (expr_, args_)
                , (fun (expr, args) ->
                    let exprv =
                        complexCache2.GetOrAdd(
                            (expr, args)
                            , fun (expr, args) ->
                                (Linq.formatComplexLambda expr args)
                        )
                    exprv.Value.Compile()
                )
            )
        cmpl

    let compileExpression1 expr arg = Option.map (fun (x : Delegate) -> x :?> Func<float, float>) (compileExpression expr [ arg ])
    let compileExpression2 expr arg1 arg2 = Option.map (fun (x : Delegate) -> x :?> Func<float, float, float>) (compileExpression expr [ arg1; arg2 ])
    let compileExpression3 expr arg1 arg2 arg3 = Option.map (fun (x : Delegate) -> x :?> Func<float, float, float, float>) (compileExpression expr [ arg1; arg2; arg3 ])
    let compileExpression4 expr arg1 arg2 arg3 arg4 = Option.map (fun (x : Delegate) -> x :?> Func<float, float, float, float, float>) (compileExpression expr [ arg1; arg2; arg3; arg4 ])

    let compileExpression1OrThrow expr arg = compileExpressionOrThrow expr [ arg ] :?> Func<float, float>
    let compileExpression2OrThrow expr arg1 arg2 = compileExpressionOrThrow expr [ arg1; arg2 ] :?> Func<float, float, float>
    let compileExpression3OrThrow expr arg1 arg2 arg3 = compileExpressionOrThrow expr [ arg1; arg2; arg3 ] :?> Func<float, float, float, float>
    let compileExpression4OrThrow expr arg1 arg2 arg3 arg4 = compileExpressionOrThrow expr [ arg1; arg2; arg3; arg4 ] :?> Func<float, float, float, float, float>

    let compileComplexExpression1 expr arg = Option.map (fun (x : Delegate) -> x :?> Func<complex, complex>) (compileComplexExpression expr [ arg ])
    let compileComplexExpression2 expr arg1 arg2 = Option.map (fun (x : Delegate) -> x :?> Func<complex, complex, complex>) (compileComplexExpression expr [ arg1; arg2 ])
    let compileComplexExpression3 expr arg1 arg2 arg3 = Option.map (fun (x : Delegate) -> x :?> Func<complex, complex, complex, complex>) (compileComplexExpression expr [ arg1; arg2; arg3 ])
    let compileComplexExpression4 expr arg1 arg2 arg3 arg4 = Option.map (fun (x : Delegate) -> x :?> Func<complex, complex, complex, complex, complex>) (compileComplexExpression expr [ arg1; arg2; arg3; arg4 ])

    let compileComplexExpression1OrThrow expr arg = compileComplexExpressionOrThrow expr [ arg ] :?> Func<complex, complex>
    let compileComplexExpression2OrThrow expr arg1 arg2 = compileComplexExpressionOrThrow expr [ arg1; arg2 ] :?> Func<complex, complex, complex>
    let compileComplexExpression3OrThrow expr arg1 arg2 arg3 = compileComplexExpressionOrThrow expr [ arg1; arg2; arg3 ] :?> Func<complex, complex, complex, complex>
    let compileComplexExpression4OrThrow expr arg1 arg2 arg3 arg4 = compileComplexExpressionOrThrow expr [ arg1; arg2; arg3; arg4 ] :?> Func<complex, complex, complex, complex, complex>

module Evaluate =
    open TupleHelpers


    let rec listOf2Obj ((wt0:TensorWrapper), (shape:int list)) : float [] * (int list) =
        match wt0 with
        | VecInTensor v ->
            let s = v.Count::shape
            printfn "v.Count: %d" v.Count
            v.AsArray(), s
        | ListOf lo ->
            let s = lo.Length::shape
            printfn "twl.Length: %d" lo.Length
            let inner =
                    lo
                    |> List.map (fun twli ->
                        listOf2Obj (twli, s)
                    )
            let ss = snd inner.[0]
            let vl =
                inner
                |> List.collect (fun vi ->
                   let veci = fst vi
                   veci
                   |> List.ofArray
                )
            vl |> Array.ofList, ss
        | _ ->
            failwithf "listOf2Obj orz"

    let listOf2DSTensor (wt0:TensorWrapper) =
#if TENSOR_SUPPORT
        let fArray, shapeReversed = listOf2Obj (wt0, [])
        dsharp.view ((dsharp.tensor fArray), shapeReversed |> Seq.rev)
#else
        failwithf "Tensor not supported"
#endif

    //module orz = 
    //    type A =
    //    | AV of int list
    //    | AL of A list


    //    let rec listOf2Obj1 (wt0:A) =
    //        match wt0 with
    //        | AL twl ->
    //            let inner = twl |> List.map listOf2Obj1
    //            let itm0 = inner.[0] |> box
    //            match itm0 with
    //            | :? (A list) as al ->
    //                al |> List.collect (fun ali ->
    //                    listOf2Obj1 ali
    //                    )
    //            | :? (int list) as il -> il
                
    //        | AV v -> v

    //    let rec listOf2Obj ((wt0:A), (shape:int list)) : (int list) * (int list) =
    //        match wt0 with
    //        | AV v ->
    //            let s = v.Length::shape
    //            printfn "v.Length: %d" v.Length
    //            v, s
    //        | AL twl ->
    //            let s = twl.Length::shape
    //            printfn "twl.Length: %d" twl.Length
    //            let inner =
    //                twl
    //                |> List.map (fun twli ->
    //                    listOf2Obj (twli, s)
    //                )
    //            let ss = snd inner.[0]
    //            (inner |> List.collect fst), ss

    //    listOf2Obj (AL [
    //                    AL [
    //                        AL [
    //                            AV [123; 345; 999]
    //                            ];
    //                        AL [
    //                            AV [1230; 3450; 888]
    //                            ];
    //                        AL [
    //                            AV [123; 345; 777]
    //                            ];
    //                        AL [
    //                            AV [1230; 3450; 666]
    //                            ]
    //                        ]
    //                    ], [])


    let (|Infinity|_|) = function
        | PosInf | NegInf | ComplexInf -> Some Infinity
        | _ -> None

    [<CompiledName("Real")>]
    let freal x = FloatingPoint.Real(x)

    [<CompiledName("Complex")>]
    let fcomplex r i = FloatingPoint.Complex (complex r i)

    let rec fnormalize = function
        | Real x when Double.IsPositiveInfinity(x) -> PosInf
        | Real x when Double.IsNegativeInfinity(x) -> NegInf
        | Real x when Double.IsInfinity(x) -> ComplexInf // not supported by double?
        | Real x when Double.IsNaN(x) -> Undef
        | Complex x when x.IsInfinity() && x.IsReal() -> if x.Real > 0.0 then PosInf else NegInf
        | Complex x when x.IsInfinity() -> ComplexInf
        | Complex x when x.IsReal() -> fnormalize (Real x.Real)
        | Complex x when x.IsNaN() -> Undef
        | x -> x

    let fadd u v =
        match u, v with
        | Real x, Real y -> Real (x+y)
        | Real x, Complex y | Complex y, Real x -> Complex ((complex x 0.0) + y)
        | Complex x, Complex y -> Complex (x+y)
        | Real x, RealVector y -> RealVector (x+y)
        | RealVector x, RealVector y -> RealVector (x+y)
        | ComplexVector x, ComplexVector y -> ComplexVector (x+y)
        | RealMatrix x, RealMatrix y -> RealMatrix (x+y)
        | ComplexMatrix x, ComplexMatrix y -> ComplexMatrix (x+y)
        | Undef, _ | _, Undef -> Undef
        | ComplexInf, Infinity | Infinity, ComplexInf -> ComplexInf
        | PosInf, NegInf -> Undef
        | PosInf, _ | _, PosInf -> PosInf
        | NegInf, _ | _, NegInf -> NegInf
        //| WTensor (DSTensor dt), Real y -> WTensor (DSTensor (dt + y))
#if TENSOR_SUPPORT
        | Real x, WTensor (DSTensor dt) -> WTensor (DSTensor (x + dt))
#endif
        | _ -> failwith "not supported"

    let fmultiply u v =
        match u, v with
        | Real x, Real y -> Real (x*y)
        | Real x, Complex y | Complex y, Real x -> Complex ((complex x 0.0) * y)
        | Complex x, Complex y -> Complex (x*y)
        | Real x, RealVector y -> RealVector (x*y)
        | RealVector x, RealVector y -> Real (x*y)
        | ComplexVector x, ComplexVector y -> Complex (x*y)
        | RealMatrix x, RealMatrix y -> RealMatrix (x*y)
        | ComplexMatrix x, ComplexMatrix y -> ComplexMatrix (x*y)
        | Undef, _ | _, Undef -> Undef
        | ComplexInf, Infinity | Infinity, ComplexInf -> ComplexInf
        | PosInf, NegInf -> NegInf
        | PosInf, Real x | Real x, PosInf ->
            if x < 0.0 then NegInf else if x > 0.0 then PosInf else Undef
        | NegInf, Real x | Real x, NegInf ->
            if x < 0.0 then PosInf else if x > 0.0 then NegInf else Undef
        | PosInf, _ | _, PosInf -> PosInf
        | NegInf, _ | _, NegInf -> NegInf
#if TENSOR_SUPPORT
        | Real x, WTensor (DSTensor t) -> WTensor (DSTensor (x * t))
#endif
        | _ -> failwith "not supported"

    let fpower u v =
        match u, v with
        | Real x, Real y when x < 0.0 && (y%1.0 <> 0.0) -> Complex (Complex.pow (complex y 0.0) (complex x 0.0))
        | Real x, Real y -> Real (Math.Pow(x, y))
        | Complex x, Real y -> Complex (Complex.pow (complex y 0.0) x)
        | Real x, Complex y -> Complex (Complex.pow y (complex x 0.0))
        | Complex x, Complex y -> Complex (Complex.pow y x)
        | Undef, _ | _, Undef -> Undef
        | ComplexInf, Infinity | Infinity, ComplexInf -> ComplexInf
        | Infinity, PosInf -> ComplexInf
        | Infinity, NegInf -> Real (0.0)
        | _ -> failwith "not supported"

    let fapply f u =
        match f, u with
        | Abs, Real x -> Real (Math.Abs x)
        | Abs, Complex x -> Real (Complex.magnitude x)
        | Abs, RealVector x -> Real (x.L2Norm())
        | Abs, ComplexVector x -> Real (x.L2Norm())
        | Abs, RealMatrix x -> Real (x.L2Norm())
        | Abs, ComplexMatrix x -> Real (x.L2Norm())
        | Ln, Real x -> Real (Math.Log(x))
        | Ln, Complex x -> Complex (Complex.ln x)
        | Lg, Real x -> Real (Math.Log10 x)
        | Lg, Complex x -> Complex (Complex.log10 x)
        | Exp, Real x -> Real (Math.Exp x)
        | Exp, Complex x -> Complex (Complex.exp x)
        | Sin, Real x -> Real (Math.Sin x)
        | Sin, Complex x -> Complex (Complex.sin x)
        | Cos, Real x -> Real (Math.Cos x)
        | Cos, Complex x -> Complex (Complex.cos x)
        | Tan, Real x -> Real (Math.Tan x)
        | Tan, Complex x -> Complex (Complex.tan x)
        | Csc, Real x -> Real (Trig.Csc x)
        | Csc, Complex x -> Complex (Trig.Csc x)
        | Sec, Real x -> Real (Trig.Sec x)
        | Sec, Complex x -> Complex (Trig.Sec x)
        | Cot, Real x -> Real (Trig.Cot x)
        | Cot, Complex x -> Complex (Trig.Cot x)
        | Sinh, Real x -> Real (Trig.Sinh(x))
        | Sinh, Complex x -> Complex (Trig.Sinh(x))
        | Cosh, Real x -> Real(Trig.Cosh(x))
        | Cosh, Complex x -> Complex (Trig.Cosh(x))
        | Tanh, Real x -> Real (Trig.Tanh(x))
        | Tanh, Complex x -> Complex (Trig.Tanh(x))
        | Csch, Real x -> Real (Trig.Csch(x))
        | Csch, Complex x -> Complex (Trig.Csch(x))
        | Sech, Real x -> Real(Trig.Sech(x))
        | Sech, Complex x -> Complex (Trig.Sech(x))
        | Coth, Real x -> Real (Trig.Coth(x))
        | Coth, Complex x -> Complex (Trig.Coth(x))
        | Asin, Real x -> Real (Trig.Asin(x))
        | Asin, Complex x -> Complex (Trig.Asin(x))
        | Acos, Real x -> Real (Trig.Acos(x))
        | Acos, Complex x -> Complex (Trig.Acos(x))
        | Atan, Real x -> Real (Trig.Atan(x))
        | Atan, Complex x -> Complex (Trig.Atan(x))
        | Acsc, Real x -> Real (Trig.Acsc(x))
        | Acsc, Complex x -> Complex (Trig.Acsc(x))
        | Asec, Real x -> Real (Trig.Asec(x))
        | Asec, Complex x -> Complex (Trig.Asec(x))
        | Acot, Real x -> Real (Trig.Acot(x))
        | Acot, Complex x -> Complex (Trig.Acot(x))
        | Asinh, Real x -> Real (Trig.Asinh(x))
        | Asinh, Complex x -> Complex (Trig.Asinh(x))
        | Acosh, Real x -> Real (Trig.Acosh(x))
        | Acosh, Complex x -> Complex (Trig.Acosh(x))
        | Atanh, Real x -> Real (Trig.Atanh(x))
        | Atanh, Complex x -> Complex (Trig.Atanh(x))
        | Acsch, Real x -> Real (Trig.Acsch(x))
        | Acsch, Complex x -> Complex (Trig.Acsch(x))
        | Asech, Real x -> Real (Trig.Asech(1.0/x))
        | Asech, Complex x -> Complex (Trig.Asech(x))
        | Acoth, Real x -> Real (Trig.Acoth(x))
        | Acoth, Complex x -> Complex (Trig.Acoth(x))
        | AiryAi, Real x -> Real (SpecialFunctions.AiryAi(x))
        | AiryAi, Complex x -> Complex (SpecialFunctions.AiryAi(x))
        | AiryAiPrime, Real x -> Real (SpecialFunctions.AiryAiPrime(x))
        | AiryAiPrime, Complex x -> Complex (SpecialFunctions.AiryAiPrime(x))
        | AiryBi, Real x -> Real (SpecialFunctions.AiryBi(x))
        | AiryBi, Complex x -> Complex (SpecialFunctions.AiryBi(x))
        | AiryBiPrime, Real x -> Real (SpecialFunctions.AiryBiPrime(x))
        | AiryBiPrime, Complex x -> Complex (SpecialFunctions.AiryBiPrime(x))
        | _ -> failwith "not supported"

    let fapplyN f xs =
        match f, xs with
        | Atan2, [Real x; Real y] -> Real (Math.Atan2(x, y))
        | Atan2, [Complex x; Real y] -> Complex (Complex.atan (x / (complex y 0.0)))
        | Atan2, [Complex x; Complex y] -> Complex (Complex.atan (x / y))
        | Atan2, [Real x; Complex y] -> Complex (Complex.atan ((complex x 0.0) / y))
        | Log, [Real b; Real x] -> Real (Math.Log(x, b))
        | Log, [Real b; Complex x] -> Complex (Complex.log b x)
        | Log, [Complex b; Complex x] -> Complex (Complex.ln x / Complex.ln b)
        | Log, [Complex b; Real x] -> Complex (Complex.ln (complex x 0.0) / Complex.ln b)
        | BesselJ, [Real nu; Real x] -> Real (SpecialFunctions.BesselJ (nu, x))
        | BesselJ, [Real nu; Complex x] -> Complex (SpecialFunctions.BesselJ (nu, x))
        | BesselY, [Real nu; Real x] -> Real (SpecialFunctions.BesselY (nu, x))
        | BesselY, [Real nu; Complex x] -> Complex (SpecialFunctions.BesselY (nu, x))
        | BesselI, [Real nu; Real x] -> Real (SpecialFunctions.BesselI (nu, x))
        | BesselI, [Real nu; Complex x] -> Complex (SpecialFunctions.BesselI (nu, x))
        | BesselK, [Real nu; Real x] -> Real (SpecialFunctions.BesselK (nu, x))
        | BesselK, [Real nu; Complex x] -> Complex (SpecialFunctions.BesselK (nu, x))
        | BesselIRatio, [Real nu; Real x] -> Real (SpecialFunctions.BesselIScaled (nu + 1.0, x) / SpecialFunctions.BesselIScaled (nu, x))
        | BesselIRatio, [Real nu; Complex x] -> Complex (SpecialFunctions.BesselIScaled (nu + 1.0, x) / SpecialFunctions.BesselIScaled (nu, x))
        | BesselKRatio, [Real nu; Real x] -> Real (SpecialFunctions.BesselKScaled (nu + 1.0, x) / SpecialFunctions.BesselKScaled (nu, x))
        | BesselKRatio, [Real nu; Complex x] -> Complex (SpecialFunctions.BesselKScaled (nu + 1.0, x) / SpecialFunctions.BesselKScaled (nu, x))
        | HankelH1, [Real nu; Real x] -> Complex (SpecialFunctions.HankelH1 (nu, complex x 0.0))
        | HankelH1, [Real nu; Complex x] -> Complex (SpecialFunctions.HankelH1 (nu, x))
        | HankelH2, [Real nu; Real x] -> Complex (SpecialFunctions.HankelH2 (nu, complex x 0.0))
        | HankelH2, [Real nu; Complex x] -> Complex (SpecialFunctions.HankelH2 (nu, x))
        | _ -> failwith "not supported"

    let obj2FloatPoint (rst: obj) =
        match rst with
        | :? float as f -> f |> Real
        | :? FloatingPoint as fp -> fp
        | :? Vector<float> as v -> v |> RealVector
        | :? Matrix<float> as v -> v |> RealMatrix
#if TENSOR_SUPPORT
        | :? Tensor as t -> WTensor (DSTensor t)
#endif
        | :? Value as v ->
            match v with
            | MathNet.Symbolics.Value.Approximation r ->
                match r with
                | Approximation.Real rr ->
                    rr |> Real
#if TENSOR_SUPPORT
            | MathNet.Symbolics.Value.DSTen dt ->
                WTensor (DSTensor dt)
#endif
            | MathNet.Symbolics.Value.RealVec rv ->
                RealVector rv
        | _ ->
            failwithf "orz 0005"

    let renameSymbols (args: Symbol list, expr: MathNet.Symbolics.Expression) : MathNet.Symbolics.Expression * Symbol list =
        // 建立從原 Symbol 到新 Symbol 的替換對應
        let replacementPairs =
            args |> List.mapi (fun i s -> s, Symbol (sprintf "p%d" i))

        let substMap = Map.ofList replacementPairs
        let newSymbols = replacementPairs |> List.map snd

        // 內部遞迴替換函數
        let rec rename expr =
            match expr with
            | Identifier sym when substMap.ContainsKey sym ->
                Identifier (substMap.[sym])
            | Argument sym when substMap.ContainsKey sym ->
                Argument (substMap.[sym])
            | Sum terms -> Sum (terms |> List.map rename)
            | Product terms -> Product (terms |> List.map rename)
            | Power (a, b) -> Power(rename a, rename b)
            | PointwiseMul (a, b) -> PointwiseMul(rename a, rename b)
            | Function (f, x) -> Function(f, rename x)
            | FunctionN (fn, args) -> FunctionN(fn, args |> List.map rename)
            | FunInvocation (name, args) -> FunInvocation(name, args |> List.map rename)
            | _ -> expr

        rename expr, newSymbols


    ///Expression 定義的函數，找不到的參數會優先從 evaluate 傳入的 symbol values 查找
    [<CompiledName("Evaluate2_with_dict_svv")>]
    let rec evaluate2_with_dict_svv (symbolValues:ConcurrentDictionary<string, FloatingPoint>, sysVarValuesOpt:IDictionary<string, FloatingPoint> option) = function
        | Number n -> Real (float n) |> fnormalize
        | Undefined -> Undef
        | ComplexInfinity -> ComplexInf
        | PositiveInfinity -> PosInf
        | NegativeInfinity -> NegInf
        | Constant E -> Real (Constants.E)
        | Constant Pi -> Real (Constants.Pi)
        | Constant I -> Complex (Complex.onei)
        | Approximation (Approximation.Real fp) -> Real fp
        | Approximation (Approximation.Complex fp) -> Complex fp
        | Identifier (Symbol s) ->
            
                if sysVarValuesOpt.IsNone then
                    match symbolValues.TryGetValue s with
                    | true, a -> a |> fnormalize
                    | _ ->
                        failwithf  "Failed to find symbol %s" s
                else
                    match sysVarValuesOpt.Value.TryGetValue s with
                    | true, a -> a |> fnormalize
                    | _ ->
                        match symbolValues.TryGetValue s with
                        | true, a -> a |> fnormalize
                        | _ ->
                            failwithf  "Failed to find symbol %s" s
        | Argument (Symbol s) -> failwithf  "Cannot evaluate a argument %s" s
        | Sum xs -> xs |> List.map (evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt)) |> List.reduce fadd |> fnormalize
        | Product xs ->
            let evall = xs |> List.map (evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt))
            let reducel = evall |> List.reduce fmultiply
            reducel |> fnormalize
        | PointwiseMul (l, r) ->
                let lv = evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) l
                let rv = evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) r
                try
                    lv .* rv
                with ex ->
                    failwithf "PointwiseMul evaluation failed:\nLeft = %A\nRight = %A\nError = %s" lv rv ex.Message
        | Power (r, p) -> fpower (evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) r) (evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) p) |> fnormalize
        | Function (f, x) -> fapply f (evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) x) |> fnormalize
        | FunctionN (f, xs) -> xs |> List.map (evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt)) |> fapplyN f |> fnormalize
        | FunInvocation (Symbol parentFxName, paramValueExprList) ->
            let cal_param_fd_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) paramValueExpr
                )

            let cal_param_obj_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) paramValueExpr |> box
                )
                |> Array.ofList

            let cal_param_real_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    match evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) paramValueExpr with
                    | (FloatingPoint.Real v) -> v
                    | (FloatingPoint.Int v) -> float v
                    | (FloatingPoint.Decimal v) -> float v
                    | _ -> Double.NaN
                )
                |> Array.ofList
            let cal_param_vec_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    match evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) paramValueExpr with
                    | (RealVector v) -> v
                    | _ -> failwithf "vector parameter is required for %s" parentFxName
                )
                |> Array.ofList
            let cal_param_mat_vec_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    match evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) paramValueExpr with
                    | (FloatingPoint.RealVector v) -> FloatingPoint.RealVector v
                    | (FloatingPoint.RealMatrix v) -> FloatingPoint.RealMatrix v
                    | _ -> failwithf "vector parameter is required for %s" parentFxName
                )
                |> Array.ofList

            let cal_param_list_of_vec_val () : TensorWrapper list =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    let evalrst = evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) paramValueExpr
                    match evalrst with
                    | (FloatingPoint.RealVector v) ->
                        VecInTensor v //計算結果WTensor                    
                    | (FloatingPoint.WTensor tw) ->  tw
                    | _ -> failwithf "vector or WTensor parameter is required for %s" parentFxName
                )

            if keyWord.ContainsKey parentFxName then
                let mbr () =
                    let param_val = cal_param_vec_val ()
                    let m2 = DenseMatrix.zero<float> (param_val.Length) (param_val.[0].Count)
                    param_val
                    |> Array.iteri (fun i v ->
                        m2.SetRow(i, v)
                    )
                    m2
                match parentFxName with
                | "lo"
                | "list_of" -> //無法知道自己是否是最上層，所以不能回傳 tensor
                    //htensor(list_of(list_of(list_of(vec(), vec()), list_of(vec(), vec()))))
                    let param_val = cal_param_list_of_vec_val ()
                    WTensor <| ListOf param_val
                    //failwithf "haven't yet implemented"
                | "vec" ->
                    let param_val = cal_param_real_val ()
                    
                    RealVector <| vector param_val
                | "mat_by_row" ->
                    RealMatrix (mbr ())
                | "mat_by_col" ->
                    let m2 = mbr()
                    RealMatrix <| m2.Transpose()
                | "htensor" -> //可以知道自己是最上層，回傳 tensor
#if TENSOR_SUPPORT
                    let param_val = cal_param_list_of_vec_val ()
                    if param_val.Length <> 1 then                        
                        failwithf "htensor only takes single list_of expression as input"
                    WTensor (DSTensor <| listOf2DSTensor param_val.[0])
#else
                    failwithf "Tensor not supported"
#endif
                //| "htensor2" -> //可以知道自己是最上層，回傳 tensor
                //    let param_val = cal_param_list_of_vec_val ()
                //    if param_val.Length <> 2 then                        
                //        failwithf "htensor2 takes 2 list_of expression as input"
                //    let v1 = param_val.[0]
                //    WTensor (DSTensor <| listOf2DSTensor )
                | "gtensor" ->
                    failwithf "haven't yet implemented"
                | "sym_ctensor" ->
                    failwithf "haven't yet implemented"
                | "mat_multiply" ->
                    let param_val = cal_param_mat_vec_val ()
                    param_val
                    |> Array.skip 1
                    |> Array.fold (fun s a ->
                        match s with
                        | RealVector vs ->
                            match a with
                            | RealVector va ->
                                let r = vs * va
                                Real r
                            | RealMatrix ma ->
                                let r = vs * ma
                                RealVector r
                            | Real ra ->
                                RealVector (vs * ra)
                            | Int ra ->
                                RealVector (vs * float ra)
                            | Decimal ra ->
                                RealVector (vs * float ra)
                            | _ ->
                                failwithf "orz 0001"
                        | RealMatrix ms ->
                            match a with
                            | RealVector va ->
                                let r = ms * va
                                RealVector r
                            | RealMatrix ma ->
                                let r = ms * ma
                                RealMatrix r
                            | Real ra ->
                                let r = ra * ms
                                RealMatrix r
                            | Int ra ->
                                RealMatrix (ms * float ra)
                            | Decimal ra ->
                                RealMatrix (ms * float ra)
                            | _ ->
                                failwithf "orz 0002"
                        | Real rs ->
                            match a with
                            | RealVector va ->
                                let r = rs * va
                                RealVector r
                            | RealMatrix ma ->
                                let r = rs * ma
                                RealMatrix r
                            | Real ra ->
                                let r = ra * rs
                                Real r
                            | Int ra ->
                                Real (rs * float ra)
                            | Decimal ra ->
                                Real (rs * float ra)
                            | _ ->
                                failwithf "orz 0003"
                        | Int rs ->
                            match a with
                            | RealVector va ->
                                let r = (float rs) * va
                                RealVector r
                            | RealMatrix ma ->
                                let r = (float rs) * ma
                                RealMatrix r
                            | Real ra ->
                                let r = ra * float rs
                                Real r
                            | Int ra ->
                                Real (float rs * float ra)
                            | Decimal ra ->
                                Real (float rs * float ra)
                            | _ ->
                                failwithf "orz 0004"
                        | Decimal rs ->
                            match a with
                            | RealVector va ->
                                let r = (float rs) * va
                                RealVector r
                            | RealMatrix ma ->
                                let r = (float rs) * ma
                                RealMatrix r
                            | Real ra ->
                                let r = ra * float rs
                                Real r
                            | Int ra ->
                                Real (float rs * float ra)
                            | Decimal ra ->
                                Real (float rs * float ra)
                            | _ ->
                                failwithf "orz 0005"
                        | _ ->
                            failwithf "orz 0006"
                    ) param_val.[0]
                | _ ->
                    failwithf $"omg fnm {parentFxName}!!!"
            else

                let rec nestedFxHandler
                    (sl: Symbol list) //fxExpr 中 sl 的變數需要
                    (fxExpr: MathNet.Symbolics.Expression)
                    //(paramValueExprList_:MathNet.Symbolics.Expression list option)
                    (symbolValues_: ConcurrentDictionary<string, FloatingPoint>)
                    (sysVarValues_: IDictionary<string, FloatingPoint> option) //代換為這裡的值
                    : (Symbol list) * (MathNet.Symbolics.Expression) =

                    let exprMap sl_ (exprs:MathNet.Symbolics.Expression list) =
                        exprs
                        |> List.fold (fun (symL, uExprs) expr ->
                            let usl, uExpr = nestedFxHandler symL expr symbolValues_ sysVarValues_
                            usl, uExprs @ [uExpr]
                        ) (sl_, [])

                    let traverse sl_ expr =
                        match expr with
                        | Sum terms ->
                            let updatedSL, uExprs = exprMap sl_ terms
                            updatedSL, Sum uExprs
                        | Product terms ->
                            let updatedSL, uExprs = exprMap sl_ terms
                            updatedSL, Product uExprs
                        | Power (baseExpr, expExpr) ->
                            let updatedSL, uExpr = nestedFxHandler sl_ baseExpr symbolValues_ sysVarValues_
                            let updatedSL2, uExpExpr = nestedFxHandler updatedSL expExpr symbolValues_ sysVarValues_
                            updatedSL2, Power (uExpr, uExpExpr)
                        | Function (func, arg) ->
                            let updatedSL, uExpr = nestedFxHandler sl_ arg symbolValues_ sysVarValues_
                            updatedSL, Function (func, uExpr)
                        | FunctionN (func, args) ->
                            let updatedSL, uExprs = exprMap sl_ args
                            updatedSL, FunctionN (func, uExprs)
                        | _ ->
                            sl_, expr

                    match fxExpr with
                    | FunInvocation ((Symbol sb), origParamExp) when Definition.funDict.ContainsKey sb ->
                        let evaluatedValue =
                            origParamExp
                            |> List.map (fun param ->
                                let newSymbolName = $"__{sb}_{Guid.NewGuid().ToString()}__"
                                let newSymbol = Symbol newSymbolName
                                let paramValue = evaluate2_with_dict_svv (symbolValues_, sysVarValues_) param
                                symbolValues_.TryAdd(newSymbolName, paramValue) |> ignore
                                Identifier newSymbol
                            )
                        
                        //sl, FunInvocation ((Symbol sb), evaluatedValue)

                        let newSymbolNameAggRst = $"__{sb}_{Guid.NewGuid().ToString()}__"
                        let newSymbolAggRst = Symbol newSymbolNameAggRst
                        //let evaluatedFunValue = evaluate2_with_dict_svv (symbolValues_, sysVarValues_) (FunInvocation ((Symbol sb), evaluatedValue))
                        let evaluatedFunValue = evaluate2_with_dict_svv (symbolValues_, None) (FunInvocation ((Symbol sb), evaluatedValue))
                        symbolValues_.TryAdd(newSymbolNameAggRst, evaluatedFunValue) |> ignore
                        FAkka.Microsoft.FSharp.Core.LeveledPrintf.frintfn FAkka.Microsoft.FSharp.Core.LeveledPrintf.PRINTLEVEL.PWARN "Dynamic symbol added: %A" newSymbolAggRst
                        sl, Identifier newSymbolAggRst

                    | FunInvocation _ ->
                        failwith $"Undefined func {fxExpr}"
                        
                    | _ ->
                        let updatedSL, traversed = traverse sl fxExpr
                        let allSymbols = ExpressionHelpFun.collectIdentifiers traversed |> Seq.toList
                        allSymbols
                        |> List.except updatedSL
                        |> List.append updatedSL
                        |> fun u ->
                            //if u.Length > allSymbols.Length then
                            //    FAkka.Microsoft.FSharp.Core.LeveledPrintf.frintfn FAkka.Microsoft.FSharp.Core.LeveledPrintf.PRINTLEVEL.PWARN "Dynamic symbol list occured:\r\nOriginal: %A\r\n Updated: %A" allSymbols u
                            u, traversed

                let exprsInFuncParamEvaluation (symbols:Symbol list) (exprs:MathNet.Symbolics.Expression list) =
                    symbols
                    |> Seq.mapi (fun i sb ->
                        sb.SymbolName, evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt) exprs[i]
                    )


                match funDict.[parentFxName] with
                //       x1, y1    dup0(paramValueExprList)
                | DTExp (parentFxParamSymbols, parentFxBody) ->
                    if parentFxParamSymbols.Length <> paramValueExprList.Length then
                        failwithf "%s parameter length not matched %A <-> %A" parentFxName parentFxParamSymbols paramValueExprList
                         
                    let evaluatedArgsOfParentCall = exprsInFuncParamEvaluation parentFxParamSymbols paramValueExprList
                        

                    match parentFxBody with
                    | Identifier aSymbol ->
                        symbolValues[aSymbol.SymbolName]
                    | FunInvocation _ ->
                        evaluate2_with_dict_svv (symbolValues, (Some (dict evaluatedArgsOfParentCall))) parentFxBody
                    | _ ->
                        let uSL, frv =
                            nestedFxHandler parentFxParamSymbols parentFxBody symbolValues (Some (dict evaluatedArgsOfParentCall))
                        let rFrv, rUSl = renameSymbols (uSL, frv) //20250413 symbol 名稱統一化後，快取才有意義

                        let expr, cmpl = Compile.compileExpressionOrThrow2 rFrv rUSl
                        let param_val = cal_param_obj_val ()
                        
                        let rst =
                            cmpl.DynamicInvoke(
                                //20250413 symbol 名稱統一化後，取值仍需要用原先的變數名，所以上面的 uSL 不能少
                                Array.append param_val (uSL |> List.skip parentFxParamSymbols.Length |> List.map (fun s -> box symbolValues[s.SymbolName]) |> List.toArray)
                            )
                        obj2FloatPoint rst

                //| DTProc procList ->
                    //let runOneProc (paramSymbols, defBody, outputSymbols) =
                    //    // 將輸入 Symbol list 轉成對應的 FloatingPoint list
                    //    let inputValues =
                    //        paramSymbols
                    //        |> List.map (fun sym ->
                    //            match symbolValues.TryGetValue(sym.SymbolName) with
                    //            | true, v ->
                    //                match v with
                    //                | Floating f -> f
                    //                | _ -> failwithf "DTProc input symbol %s must be Floating" sym.SymbolName
                    //            | _ -> failwithf "DTProc input symbol %s not found" sym.SymbolName
                    //        )

                    //    // 建立一個空白環境（或者從 symbolValues 建立？）
                    //    let env = ConcurrentDictionary<string, FloatingPoint>()

                    //    // 評估 DefBody
                    //    match defBody with
                    //    | DBFun f ->
                    //        let updatedEnv = f env inputValues
                    //        outputSymbols
                    //        |> List.map (fun sym ->
                    //            match updatedEnv.TryGetValue(sym.SymbolName) with
                    //            | true, fp -> Floating fp
                    //            | _ -> failwithf "DTProc output symbol %s not found" sym.SymbolName
                    //        )
                    //    | DBExp exprArr ->
                    //        // 用目前 symbolValues 映射成 IDictionary<string, FloatingPoint> 供 evaluate 使用
                    //        let localEnv =
                    //            symbolValues
                    //            |> Seq.choose (fun kvp ->
                    //                match kvp.Value with
                    //                | Floating f -> Some (kvp.Key, f)
                    //                | _ -> None
                    //            )
                    //            |> dict

                    //        let results =
                    //            exprArr
                    //            |> Array.map (fun expr -> Linq.ExprHelper.evaluate localEnv expr)

                    //        if results.Length <> outputSymbols.Length then
                    //            failwithf "DTProc DBExp output length mismatch: expected %d but got %d" outputSymbols.Length results.Length

                    //        Array.zip outputSymbols results
                    //        |> Array.map (fun (sym, f) -> Floating f)
                    //        |> Array.toList
                    //// collect 所有 proc 結果
                    //procList
                    //|> List.collect runOneProc
                    //|> ValueList
                    //match fx_real with
                    //| Choice1Of2 (extraParams, frv) ->
                    //    let expr, cmpl = Compile.compileExpressionOrThrow2 frv (List.append param extraParams)
                    //    let param_val =
                    //        Array.append (cal_param_obj_val ()) 
                    //    //let rst = cmpl.DynamicInvoke(param_val:obj[])
                    //    //obj2FloatPoint rst
                    //    failwith "orz123"
                    //| Choice2Of2 (extraParams, frv) ->
                    //    evaluate2_with_dict_svv (symbolValues_, sysVarValues) frv
#if DTPROC_old
                | DTProc procList ->
                    let procScope _ = ConcurrentDictionary<string, FloatingPoint>() |> Context //供圖靈機 IO
                    let psId = System.Guid.NewGuid().ToString()
                    let _ = symbolValues.GetOrAdd(psId, procScope)

                    let rec evalProc (procScopeId:string) (sds:((Symbol list) * DefBody) list) (prevBodyOpt: ((Symbol list) * DefBody) option) (previousOutputOpt:ConcurrentDictionary<string, FloatingPoint> option) =
                        match sds with
                        | [] ->
                            match prevBodyOpt with
                            | Some (sbl, DBExp (expr,defOut)) ->

                        | (_params, body)::rest ->
                            let evaluatedArgsOfParentCall = exprsInFuncParamEvaluation _params paramValueExprList
                            match body with
                            | DBExp (fxs, scopedOut) ->
                                let param_val:obj[] = cal_param_obj_val ()
                                previousOutputOpt.Value
                            | DBFun f ->
                                let gc = 
                               
                    let _ = evalProc psId procList None None
                    Undef
#endif
#if DTPROC_Gemini_001 // Conditional compilation flag for DTProc feature
                 | DTProc procList -> // DTProc of ((Symbol list) * DefBody * (Symbol list)) list
                     // --- DTProc Execution Logic ---
                     // 1. Create a new scope for this procedure execution.
                     //    This scope inherits from the current scope (symbolValues)
                     //    but modifications within the proc won't affect the outer scope directly
                     //    unless explicitly using SetGlobal.
                     let procScope = ConcurrentDictionary<string, FloatingPoint>(symbolValues) // Inherit outer scope

                     // Add a reference to the global scope (needed for Set/GetGlobal)
                     match symbolValues.TryGetValue("global") with
                     | true, globalCtx -> procScope.TryAdd("global", globalCtx) |> ignore
                     | _ -> failwith "Global context not found during DTProc evaluation"

                     // Add arguments to the new scope
                     if paramValueExprList.Length <> (fst procList.[0]).Length then // Assuming all procs in the list have same input signature
                          failwithf "DTProc %s parameter count mismatch. Expected %d, Got %d" parentFxName (fst procList.[0]).Length paramValueExprList.Length

                     let evaluatedArgs = paramValueExprList |> List.map (evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt))

                     List.zip (fst procList.[0]) evaluatedArgs
                     |> List.iter (fun (sym, value) -> procScope.[sym.SymbolName] <- value)


                     // 2. Execute the sequence of procedures (DefBody) within the new scope.
                     //    This requires iterating through the procList and evaluating each DefBody.
                     //    The exact evaluation depends on whether DefBody is DBExp or DBFun.
                     let mutable lastResult: FloatingPoint = Undef // Procedures might implicitly return the last value

                     for (inSymbols, body) in procList do
                         // (Re-verify inSymbols match? Or assume they are consistent for a given DTProc name)

                         match body with
                         | DBExp (expr, defOut) ->
                             // Evaluate the expression within the procScope
                             // This nested call uses the procScope
                             lastResult <- evaluate2_with_dict_svv (procScope, None) expr // Evaluate within the proc scope

                             match defOut with
                             | OutVar outSymbols ->
                             // Handle potential output symbol assignment (if DefBody carried output info)
                             // NOTE: The original DTProc definition had output symbols.
                             // If a single DBExp is meant to produce outputs, how is it specified?
                             // Assuming for now DBExp implicitly returns its value, and maybe assigns to ONE output symbol if specified.
                                 if outSymbols.Length = 1 then
                                     procScope.[(List.head outSymbols).SymbolName] <- lastResult
                                 elif outSymbols.Length > 1 then
                                      printfn "Warning: DBExp in DTProc %s has multiple output symbols but returns single value. Assigning to first symbol only." parentFxName
                                      procScope.[(List.head outSymbols).SymbolName] <- lastResult

                         | DBFun func ->
                             // The function `func` needs access to the procScope to Get/Set scoped variables.
                             // This requires `func`'s signature to accept the scope.
                             // Let's redefine DBFun slightly for this:
                             // type DefBody = ... | DBFun of (ConcurrentDictionary<string, FloatingPoint> -> FloatingPoint)
                             // This allows the function to interact with its environment.
                             lastResult <- func procScope // Execute the function, passing the scope

                             // Output assignment is handled *within* the DBFun implementation
                             // (e.g., by modifying the passed-in procScope)

                         | _ -> failwith "Unsupported DefBody type within DTProc"


                     // 3. Return the final result.
                     //    What DTProc returns is debatable. Options:
                     //    a) The value of the last expression/function evaluated.
                     //    b) A specific "return" value set within the scope.
                     //    c) A record/map of the output symbols.
                     //    Let's assume it returns the value of the last evaluated body for now.
                     lastResult // Return the result of the last step

#endif // DTPROC End
#if DTPROC_GPT
                | DTProc procList ->
                    // --- DTProc Evaluation (修正版 for FloatingPoint.Context) ---

                    // 1. 建立新的 procScope，繼承自外層 symbolValues (單純copy，不是parent link)
                    let procScope = ConcurrentDictionary<string, FloatingPoint>()
                    let procId = Guid.NewGuid().ToString()

                    // 2. 確保 procScope 中 "global" 存在（用來支援 SetGlobal/GetGlobal）
                    match symbolValues.TryGetValue("scoped") with
                    | true, globalCtx -> 
                        procScope.TryAdd("scoped", globalCtx) |> ignore
                    | _ -> failwith "DTProc 執行時找不到 global scope，請先建立全域環境。"

                    // 3. 處理參數綁定
                    let (paramSyms, _) = procList.Head
                    if paramSyms.Length <> paramValueExprList.Length then
                        failwithf "DTProc 參數數量錯誤。預期 %d 個，實際收到 %d 個。" paramSyms.Length paramValueExprList.Length

                    let evaluatedArgs = paramValueExprList |> List.map (evaluate2_with_dict_svv (symbolValues, sysVarValuesOpt))

                    List.zip paramSyms evaluatedArgs
                    |> List.iter (fun (sym, value) -> procScope.[sym.SymbolName] <- value)

                    // 4. 執行每個 DefBody
                    let mutable lastResult: FloatingPoint = Undef

                    for (inSyms, body) in procList do
                        match body with
                        | DBExp (exprList, defOut) ->
                            let mutable lastExprVal = Undef
                            for expr in exprList do
                                lastExprVal <- evaluate2_with_dict_svv (procScope, sysVarValuesOpt) expr
                            // 處理 OutVar/OutFP/OutCtx
                            match defOut with
                            | OutVar outSyms ->
                                match outSyms, lastExprVal with
                                | [outSym], _ ->
                                    procScope.[outSym.SymbolName] <- lastExprVal
                                | outSyms, FloatingPoint.NestedMap m when outSyms.Length = m.Count ->
                                    outSyms
                                    |> List.iter (fun sym ->
                                        match m.TryGetValue(sym.SymbolName) with
                                        | true, v -> procScope.[sym.SymbolName] <- v
                                        | _ -> failwithf "NestedMap 中找不到欄位 %s" sym.SymbolName)
                                | [], _ -> () // 無輸出
                                | _ -> failwith "DBExp 輸出符號數量與回傳值不匹配。"
                            | OutFP -> ()
                            | OutCtx -> ()
                            lastResult <- lastExprVal

                        | DBFun almightyFun ->
                            lastResult <- almightyFun (Some symbolValues) None None procScope

                        | _ -> failwith "未知 DefBody 型別，無法處理。"



                    lastResult
#endif

#if MANUS
                | DTProc procList ->
                    // 創建一個新的作用域上下文
                    let procScope = ConcurrentDictionary<string, FloatingPoint>()
                    let psId = System.Guid.NewGuid().ToString()
                    let globalContext = symbolValues // 全局上下文
    
                    // 遞迴處理procList中的每個過程定義
                    let rec evalProc (procList: ((Symbol list) * DefBody) list) (prevOutput: FloatingPoint) (currentScopedContext: ConcurrentDictionary<string, FloatingPoint>) =
                        match procList with
                        | [] -> 
                            // 所有過程處理完畢，返回最後的輸出
                            prevOutput
            
                        | (paramSymbols, defBody) :: restProcs ->
                            // 檢查參數數量是否匹配
                            if paramSymbols.Length <> paramValueExprList.Length then
                                failwithf "%s parameter length not matched %A <-> %A" parentFxName paramSymbols paramValueExprList
            
                            // 創建新的作用域上下文（如果尚未存在）
                            //let currentScopedContext = 
                            //    match scopedContext with
                            //    | Some ctx -> ctx
                            //    | None -> ConcurrentDictionary<string, FloatingPoint>()
            
                            // 評估參數並將其添加到作用域上下文
                            for i = 0 to paramSymbols.Length - 1 do
                                let paramSymbol = paramSymbols.[i]
                                let paramValue = evaluate2_with_dict_svv (globalContext, None) paramValueExprList.[i]
                                currentScopedContext.[paramSymbol.SymbolName] <- paramValue
            
                            // 根據DefBody類型處理
                            let newOutput = 
                                match defBody with
                                | DBExp (exprList, defOutput) ->
                                    // 評估表達式列表
                                    let results = 
                                        exprList 
                                        |> List.map (fun expr -> evaluate2_with_dict_svv (globalContext, Some (currentScopedContext :> IDictionary<string, FloatingPoint>)) expr)
                    
                                    // 根據DefOutput類型處理輸出
                                    match defOutput with
                                    | OutVar symbols ->
                                        // 從作用域上下文中獲取指定變數的值
                                        if symbols.IsEmpty then
                                            // 如果沒有指定輸出變數，則返回最後一個表達式的結果
                                            List.last results
                                        else
                                            // 從作用域上下文中獲取指定變數的值
                                            let outputValues = 
                                                symbols 
                                                |> List.map (fun sym -> 
                                                    match currentScopedContext.TryGetValue(sym.SymbolName) with
                                                    | true, value -> value
                                                    | _ -> failwithf "Output symbol %s not found in scoped context" sym.SymbolName)
                            
                                            // 如果只有一個輸出變數，直接返回其值
                                            if outputValues.Length = 1 then
                                                outputValues.[0]
                                            else
                                                // 否則返回嵌套列表
                                                NestedList outputValues
                    
                                    | OutFP ->
                                        // 返回最後一個表達式的結果
                                        List.last results
                    
                                    | OutCtx ->
                                        // 返回整個作用域上下文
                                        Context currentScopedContext
                
                                | DBFun almightFun ->
                                    // 執行AlmightFun函數
                                    // 參數：全局上下文、前一個作用域上下文（可選）、前一個輸出、當前作用域上下文
                                    let scopedContextOutput = 
                                        almightFun globalContext scopedContext (Some prevOutput) currentScopedContext
                    
                                    // 返回函數的輸出
                                    scopedContextOutput
            
                            // 繼續處理剩餘的過程定義
                            evalProc restProcs newOutput (Some currentScopedContext)
    
                    // 開始處理過程列表，初始輸出為Undef，初始作用域上下文為None
                    let finalOutput = evalProc procList Undef None
                    finalOutput
#endif
                | DTFunI1toI1 f ->
                    let param_val = cal_param_real_val ()
                    f (int param_val.[0]) |> float |> Real
                | DTFunF2toV1 f ->
                    let param_val = cal_param_real_val ()
                    f param_val.[0] param_val.[1] |> RealVector
                | DTCurF2toV1 (f, (Symbol sym)) ->
                    let param_val = cal_param_real_val ()
                    let cur = symbolValues.[sym].DecimalValue
                    f cur param_val.[0] param_val.[1] |> RealVector
                | DTCurF3toV1 (f, (Symbol sym)) ->
                    let param_val = cal_param_real_val ()
                    let cur = symbolValues.[sym].DecimalValue
                    f cur param_val.[0] param_val.[1] param_val.[2] |> RealVector
                | DTFunAction f ->
                    f ()
                    Undef


    ///Expression 定義的函數，找不到的參數會優先從呼叫函數 (例如 f 定義中呼叫了 g，則 f 為呼叫函數) 的 stack 中查找，而不是優先使用 evaluate 傳入的 symbol values
    (*
    有幾層則最外層函數就會用套過幾層的參數值，所以錯很大

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
        define "dup31" ([Symbol "x"; Symbol "y"],
            SymbolicExpression.XParse "x + y * y + z")
    let _ =
        define "dup41" ([Symbol "x"; Symbol "y"],
            SymbolicExpression.XParse "dup31(x+1,y*2)")

    SymbolicExpression.Parse("dup4(7,8)").EvaluateMode0(dict ["z", FloatingPoint.Real -8.0]) //5889 = 9 + 32 * (8 + 11 * 16) - 8 (不正確，應該等於 2944)
    SymbolicExpression.Parse("dup3(8,16)").EvaluateMode0(dict ["z", FloatingPoint.Real -8.0]) //2944 = 8 + 16 * (8 + 11 * 16) - 8 (正確)
    SymbolicExpression.Parse("dup41(7,8)").EvaluateMode0(dict ["z", FloatingPoint.Real -8.0]) //1025 = 9 + 32 * 32 - 8 (不正確，應該等於 256)
    SymbolicExpression.Parse("dup31(8,16)").EvaluateMode0(dict ["z", FloatingPoint.Real -8.0]) //256 = 8 + 16 * 16 - 8 (正確)

    SymbolicExpression.Parse("dup4(7,8)").Evaluate(dict ["z", FloatingPoint.Real -8.0]) 
    SymbolicExpression.Parse("dup3(8,16)").Evaluate(dict ["z", FloatingPoint.Real -8.0]) 
    SymbolicExpression.Parse("dup41(7,8)").Evaluate(dict ["z", FloatingPoint.Real -8.0]) 
    SymbolicExpression.Parse("dup31(8,16)").Evaluate(dict ["z", FloatingPoint.Real -8.0])
    *)
    let stackValueProgrammingMode (svv:ConcurrentStack<ConcurrentDictionary<string, FloatingPoint> option>) =
        //20250426: 這樣會造成外層參數名被內層用到，這樣不對(應該吧)
        svv.ToArray() |> Array.choose id |> Array.collect (fun d -> d |> Seq.map (fun kv -> kv.Key, kv.Value) |> Seq.toArray) |> Array.rev |> dict |> ConcurrentDictionary<_, _>
        //match svv.TryPeek() with
        //| true, Some d ->
        //    d |> Seq.map (fun kv -> kv.Key, kv.Value) |> Seq.toArray |> Map
        //| _, _ ->
        //    Map []

    let stackValueMathMode (svv:ConcurrentStack<ConcurrentDictionary<string, FloatingPoint> option>) =
        match svv.TryPeek() with
        | true, Some d ->
            //d |> Seq.map (fun kv -> kv.Key, kv.Value) |> Seq.toArray |> Map
            d
        | _, _ ->
            ConcurrentDictionary<_, _>()

    let stackValueProgrammingModeI (svv:ConcurrentStack<IDictionary<string, FloatingPoint> option>) =
        //20250426: 這樣會造成外層參數名被內層用到，這樣不對(應該吧)
        svv.ToArray() |> Array.choose id |> Array.collect (fun d -> d |> Seq.map (fun kv -> kv.Key, kv.Value) |> Seq.toArray) |> Array.rev |> dict
        //match svv.TryPeek() with
        //| true, Some d ->
        //    d |> Seq.map (fun kv -> kv.Key, kv.Value) |> Seq.toArray |> Map
        //| _, _ ->
        //    Map []

    let stackValueMathModeI (svv:ConcurrentStack<IDictionary<string, FloatingPoint> option>) =
        match svv.TryPeek() with
        | true, Some d ->
            //d |> Seq.map (fun kv -> kv.Key, kv.Value) |> Seq.toArray |> Map
            d
        | _, _ ->
            dict []

    //type ConcurrentStack<'T> with
    //    member this.StackValueMode0 : Map<string, FloatingPoint> =
    //        stackValueProgrammingMode (box this :?> ConcurrentStack<IDictionary<string, FloatingPoint> option>)

    //    member this.StackValueMode1 : Map<string, FloatingPoint> =
    //        stackValueMathMode        (box this :?> ConcurrentStack<IDictionary<string, FloatingPoint> option>)

    [<Extension>]
    type SpecializedStack =
        [<Extension>]
        static member StackValueMode0(cs:ConcurrentStack<ConcurrentDictionary<string, FloatingPoint> option>) =
            stackValueProgrammingMode cs

        [<Extension>]
        static member StackValueMode1(cs:ConcurrentStack<ConcurrentDictionary<string, FloatingPoint> option>) =
            stackValueMathMode cs

        [<Extension>]
        static member StackValueMode0(cs:ConcurrentStack<IDictionary<string, FloatingPoint> option>) =
            stackValueProgrammingModeI cs

        [<Extension>]
        static member StackValueMode1(cs:ConcurrentStack<IDictionary<string, FloatingPoint> option>) =
            stackValueMathModeI cs

        [<Extension>]
        static member GetValue (cs:ConcurrentStack<ConcurrentDictionary<string, FloatingPoint> option>, s) =
            match cs.StackValueMode1().TryGetValue s with
                | true, a -> a |> fnormalize |> Some
                | _ -> None

        [<Extension>]
        static member TryAdds (cd:ConcurrentDictionary<string, FloatingPoint>, added: (string * FloatingPoint) seq) =
            added
            |> Seq.iter (fun (k, v) ->
                cd.TryAdd(k, v) |> ignore
            )




    let scopeCtx _ = ConcurrentDictionary<string, FloatingPoint>() |> Context //供圖靈機 IO

    [<CompiledName("Evaluate2")>]
    let rec evaluate2 (
            symbolValues:ConcurrentDictionary<string, FloatingPoint>
            , sysVarValueStack:ConcurrentStack<ConcurrentDictionary<string, FloatingPoint> option>
            , postFunOpt: (unit -> unit) option
            , ifTop: bool
    ) =
        let pop () = sysVarValueStack.TryPop () |> ignore
        let getValue s =
            match sysVarValueStack.StackValueMode1().TryGetValue s with
                | true, a -> a |> fnormalize
                | _ ->
                    match symbolValues.TryGetValue s with
                    | true, a -> a |> fnormalize
                    | _ ->
                        failwithf  "Failed to find symbol %s" s
        function
        | Number n -> Real (float n) |> fnormalize
        | Undefined -> Undef
        | ComplexInfinity -> ComplexInf
        | PositiveInfinity -> PosInf
        | NegativeInfinity -> NegInf
        | Constant E -> Real (Constants.E)
        | Constant Pi -> Real (Constants.Pi)
        | Constant I -> Complex (Complex.onei)
        | Approximation (Approximation.Real fp) -> Real fp
        | Approximation (Approximation.Complex fp) -> Complex fp
        | Identifier (Symbol s) ->
                //if sysVarValueStack.IsNone then
                //    match symbolValues.TryGetValue s with
                //    | true, a -> a |> fnormalize
                //    | _ ->
                //        failwithf  "Failed to find symbol %s" s
                //else
                getValue s
                    //match sysVarValueStack.StackValueMode1().TryGetValue s with
                    //| true, a -> a |> fnormalize
                    //| _ ->
                    //    match symbolValues.TryGetValue s with
                    //    | true, a -> a |> fnormalize
                    //    | _ ->
                    //        failwithf  "Failed to find symbol %s" s
        | Argument (Symbol s) -> failwithf  "Cannot evaluate a argument %s" s
        | Sum xs -> xs |> List.map (evaluate2 (symbolValues, sysVarValueStack, None, ifTop)) |> List.reduce fadd |> fnormalize
        | Product xs ->
            let evall = xs |> List.map (evaluate2 (symbolValues, sysVarValueStack, None, ifTop))
            let reducel = evall |> List.reduce fmultiply
            reducel |> fnormalize
        | PointwiseMul (l, r) ->
                let lv = evaluate2 (symbolValues, sysVarValueStack, None, ifTop) l
                let rv = evaluate2 (symbolValues, sysVarValueStack, None, ifTop) r
                try
                    lv .* rv
                with ex ->
                    failwithf "PointwiseMul evaluation failed:\nLeft = %A\nRight = %A\nError = %s" lv rv ex.Message
        | Power (r, p) -> fpower (evaluate2 (symbolValues, sysVarValueStack, None, ifTop) r) (evaluate2 (symbolValues, sysVarValueStack, None, ifTop) p) |> fnormalize
        | Function (f, x) -> fapply f (evaluate2 (symbolValues, sysVarValueStack, None, ifTop) x) |> fnormalize
        | FunctionN (f, xs) -> xs |> List.map (evaluate2 (symbolValues, sysVarValueStack, None, ifTop)) |> fapplyN f |> fnormalize
        | FunInvocation (Symbol parentFxName, paramValueExprList) ->
            let cal_param_fd_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    evaluate2 (symbolValues, sysVarValueStack, None, ifTop) paramValueExpr
                )

            let cal_param_obj_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    evaluate2 (symbolValues, sysVarValueStack, None, ifTop) paramValueExpr |> box
                )
                |> Array.ofList

            let cal_param_real_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    match evaluate2 (symbolValues, sysVarValueStack, None, ifTop) paramValueExpr with
                    | (FloatingPoint.Real v) -> v
                    | (FloatingPoint.Int v) -> float v
                    | (FloatingPoint.Decimal v) -> float v
                    | _ -> Double.NaN
                )
                |> Array.ofList
            let cal_param_vec_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    match evaluate2 (symbolValues, sysVarValueStack, None, ifTop) paramValueExpr with
                    | (RealVector v) -> v
                    | _ -> failwithf "vector parameter is required for %s" parentFxName
                )
                |> Array.ofList
            let cal_param_mat_vec_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    match evaluate2 (symbolValues, sysVarValueStack, None, ifTop) paramValueExpr with
                    | (FloatingPoint.RealVector v) -> FloatingPoint.RealVector v
                    | (FloatingPoint.RealMatrix v) -> FloatingPoint.RealMatrix v
                    | _ -> failwithf "vector parameter is required for %s" parentFxName
                )
                |> Array.ofList

            let cal_param_list_of_vec_val () : TensorWrapper list =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    let evalrst = evaluate2 (symbolValues, sysVarValueStack, None, ifTop) paramValueExpr
                    match evalrst with
                    | (FloatingPoint.RealVector v) ->
                        VecInTensor v //計算結果WTensor                    
                    | (FloatingPoint.WTensor tw) ->  tw
                    | _ -> failwithf "vector or WTensor parameter is required for %s" parentFxName
                )

            if keyWord.ContainsKey parentFxName then
                let mbr () =
                    let param_val = cal_param_vec_val ()
                    let m2 = DenseMatrix.zero<float> (param_val.Length) (param_val.[0].Count)
                    param_val
                    |> Array.iteri (fun i v ->
                        m2.SetRow(i, v)
                    )
                    m2
                let f () =
                    match parentFxName with
                    | "str" ->
                        match paramValueExprList[0] with
                        | Identifier (Symbol s) -> Str s
                        | _ ->
                            failwithf "Invalid str expression! %A" paramValueExprList
                    | "lo"
                    | "list_of" -> //無法知道自己是否是最上層，所以不能回傳 tensor
                        //htensor(list_of(list_of(list_of(vec(), vec()), list_of(vec(), vec()))))
                        let param_val = cal_param_list_of_vec_val ()
                        WTensor <| ListOf param_val
                        //failwithf "haven't yet implemented"
                    | "vec" ->
                        let param_val = cal_param_real_val ()
                    
                        RealVector <| vector param_val
                    | "mat_by_row" ->
                        RealMatrix (mbr ())
                    | "mat_by_col" ->
                        let m2 = mbr()
                        RealMatrix <| m2.Transpose()
                    | "htensor" -> //可以知道自己是最上層，回傳 tensor
#if TENSOR_SUPPORT
                        let param_val = cal_param_list_of_vec_val ()
                        if param_val.Length <> 1 then                        
                            failwithf "htensor only takes single list_of expression as input"
                        WTensor (DSTensor <| listOf2DSTensor param_val.[0])
#else
                        failwithf "Tensor not supported"
#endif
                    //| "htensor2" -> //可以知道自己是最上層，回傳 tensor
                    //    let param_val = cal_param_list_of_vec_val ()
                    //    if param_val.Length <> 2 then                        
                    //        failwithf "htensor2 takes 2 list_of expression as input"
                    //    let v1 = param_val.[0]
                    //    WTensor (DSTensor <| listOf2DSTensor )
                    | "gtensor" ->
                        failwithf "haven't yet implemented"
                    | "sym_ctensor" ->
                        failwithf "haven't yet implemented"
                    | "mat_multiply" ->
                        let param_val = cal_param_mat_vec_val ()
                        param_val
                        |> Array.skip 1
                        |> Array.fold (fun s a ->
                            match s with
                            | RealVector vs ->
                                match a with
                                | RealVector va ->
                                    let r = vs * va
                                    Real r
                                | RealMatrix ma ->
                                    let r = vs * ma
                                    RealVector r
                                | Real ra ->
                                    RealVector (vs * ra)
                                | Int ra ->
                                    RealVector (vs * float ra)
                                | Decimal ra ->
                                    RealVector (vs * float ra)
                                | _ ->
                                    failwithf "orz 0001"
                            | RealMatrix ms ->
                                match a with
                                | RealVector va ->
                                    let r = ms * va
                                    RealVector r
                                | RealMatrix ma ->
                                    let r = ms * ma
                                    RealMatrix r
                                | Real ra ->
                                    let r = ra * ms
                                    RealMatrix r
                                | Int ra ->
                                    RealMatrix (ms * float ra)
                                | Decimal ra ->
                                    RealMatrix (ms * float ra)
                                | _ ->
                                    failwithf "orz 0002"
                            | Real rs ->
                                match a with
                                | RealVector va ->
                                    let r = rs * va
                                    RealVector r
                                | RealMatrix ma ->
                                    let r = rs * ma
                                    RealMatrix r
                                | Real ra ->
                                    let r = ra * rs
                                    Real r
                                | Int ra ->
                                    Real (rs * float ra)
                                | Decimal ra ->
                                    Real (rs * float ra)
                                | _ ->
                                    failwithf "orz 0003"
                            | Int rs ->
                                match a with
                                | RealVector va ->
                                    let r = (float rs) * va
                                    RealVector r
                                | RealMatrix ma ->
                                    let r = (float rs) * ma
                                    RealMatrix r
                                | Real ra ->
                                    let r = ra * float rs
                                    Real r
                                | Int ra ->
                                    Real (float rs * float ra)
                                | Decimal ra ->
                                    Real (float rs * float ra)
                                | _ ->
                                    failwithf "orz 0004"
                            | Decimal rs ->
                                match a with
                                | RealVector va ->
                                    let r = (float rs) * va
                                    RealVector r
                                | RealMatrix ma ->
                                    let r = (float rs) * ma
                                    RealMatrix r
                                | Real ra ->
                                    let r = ra * float rs
                                    Real r
                                | Int ra ->
                                    Real (float rs * float ra)
                                | Decimal ra ->
                                    Real (float rs * float ra)
                                | _ ->
                                    failwithf "orz 0005"
                            | _ ->
                                failwithf "orz 0006"
                        ) param_val.[0]

                    | "expr"
                    | "param" ->
                        NestedExpr paramValueExprList
                    | _ ->
                        failwithf $"omg fnm {parentFxName}!!!"

                match postFunOpt with
                | Some p ->
                    let r = f ()
                    p ()
                    r
                | None ->
                    f ()

            else
                
                let fd, postFunOpt_, sctx =
                    if ifTop || postFunOpt.IsNone then
                        let fd_ = FunDict(funDict)
                        let ctx = scopeCtx().ctx
                        ctx["funDict"] <- FD fd_
                        sysVarValueStack.Push (Some ctx)
                        fd_, (Some pop), ctx
                    else 
                        let ctx = sysVarValueStack.StackValueMode1()
                        match ctx.TryGetValue "funDict" with
                        | true, fd__ ->
                            fd__.funDict, postFunOpt, ctx
                        | _ ->
                            let fd_ = FunDict(funDict)
                            ctx["funDict"] <- FD fd_
                            fd_, postFunOpt, ctx
                        

                let rec nestedFxHandler
                    (sl: Symbol list) //fxExpr 中 sl 的變數需要
                    (fxExpr: MathNet.Symbolics.Expression)
                    //(paramValueExprList_:MathNet.Symbolics.Expression list option)
                    (symbolValues_: ConcurrentDictionary<string, FloatingPoint>)
                    //(sysVarValues_: IDictionary<string, FloatingPoint> option) //代換為這裡的值
                    (sysVarValueStack_:ConcurrentStack<ConcurrentDictionary<string, FloatingPoint> option>)
                    (postFun_: (unit -> unit) option)
                    : (Symbol list) * (MathNet.Symbolics.Expression) =

                    let exprMap sl_ (exprs:MathNet.Symbolics.Expression list) =
                        exprs
                        |> List.fold (fun (symL, uExprs) expr ->
                            let usl, uExpr = nestedFxHandler symL expr symbolValues_ sysVarValueStack_ None
                            usl, uExprs @ [uExpr]
                        ) (sl_, [])

                    let traverse sl_ expr =
                        match expr with
                        | Sum terms ->
                            let updatedSL, uExprs = exprMap sl_ terms
                            updatedSL, Sum uExprs
                        | Product terms ->
                            let updatedSL, uExprs = exprMap sl_ terms
                            updatedSL, Product uExprs
                        | Power (baseExpr, expExpr) ->
                            let updatedSL, uExpr = nestedFxHandler sl_ baseExpr symbolValues_ sysVarValueStack_ None
                            let updatedSL2, uExpExpr = nestedFxHandler updatedSL expExpr symbolValues_ sysVarValueStack_ None
                            updatedSL2, Power (uExpr, uExpExpr)
                        | Function (func, arg) ->
                            let updatedSL, uExpr = nestedFxHandler sl_ arg symbolValues_ sysVarValueStack_ None
                            updatedSL, Function (func, uExpr)
                        | FunctionN (func, args) ->
                            let updatedSL, uExprs = exprMap sl_ args
                            updatedSL, FunctionN (func, uExprs)
                        | _ ->
                            sl_, expr

                    let r = 
                        match fxExpr with
                        | FunInvocation ((Symbol sb), origParamExp) when fd.ContainsKey sb ->
                            let evaluatedValue =
                                origParamExp
                                |> List.map (fun param ->
                                    let newSymbolName = $"__{sb}_{Guid.NewGuid().ToString()}__"
                                    let newSymbol = Symbol newSymbolName
                                    let paramValue = evaluate2 (symbolValues_, sysVarValueStack_, None, false) param
                                    symbolValues_.TryAdd(newSymbolName, paramValue) |> ignore
                                    Identifier newSymbol
                                )
                        
                        

                            let newSymbolNameAggRst = $"__{sb}_{Guid.NewGuid().ToString()}__"
                            let newSymbolAggRst = Symbol newSymbolNameAggRst
                        
                            let evaluatedFunValue = evaluate2 (symbolValues_, sysVarValueStack_, None, false) (FunInvocation ((Symbol sb), evaluatedValue))
                            symbolValues_.TryAdd(newSymbolNameAggRst, evaluatedFunValue) |> ignore
                            FAkka.Microsoft.FSharp.Core.LeveledPrintf.frintfn FAkka.Microsoft.FSharp.Core.LeveledPrintf.PRINTLEVEL.PWARN "Dynamic symbol added: %A" newSymbolAggRst
                            sl, Identifier newSymbolAggRst

                        | FunInvocation _ ->
                            failwith $"Undefined func {fxExpr}"
                        
                        | _ ->
                            let updatedSL, traversed = traverse sl fxExpr
                            let allSymbols = ExpressionHelpFun.collectIdentifiers traversed |> Seq.toList
                            allSymbols
                            |> List.except updatedSL
                            |> List.append updatedSL
                            |> fun u ->
                                //if u.Length > allSymbols.Length then
                                //    FAkka.Microsoft.FSharp.Core.LeveledPrintf.frintfn FAkka.Microsoft.FSharp.Core.LeveledPrintf.PRINTLEVEL.PWARN "Dynamic symbol list occured:\r\nOriginal: %A\r\n Updated: %A" allSymbols u
                                u, traversed
                    match postFun_ with
                    | Some p -> p ()
                    | None -> ()
                    r

                let exprsInFuncParamEvaluation (symbols:Symbol list) (exprs:MathNet.Symbolics.Expression list) ifTop =
                    symbols
                    |> Seq.mapi (fun i sb ->
                        sb.SymbolName, evaluate2 (symbolValues, sysVarValueStack, None, ifTop) exprs[i]
                    )
                
                let r = 
                    match fd.[parentFxName] with
                    //       x1, y1    dup0(paramValueExprList)
                    | DTExp (parentFxParamSymbols, parentFxBody) ->
                        if parentFxParamSymbols.Length <> paramValueExprList.Length then
                            failwithf "%s parameter length not matched %A <-> %A" parentFxName parentFxParamSymbols paramValueExprList
                         
                        let evaluatedArgsOfParentCall = exprsInFuncParamEvaluation parentFxParamSymbols paramValueExprList ifTop
                        //sysVarValueStack.Push (Some (ConcurrentDictionary<_, _> (dict evaluatedArgsOfParentCall)))
                        sctx.TryAdds evaluatedArgsOfParentCall

                        match parentFxBody with
                        | Identifier aSymbol ->
                            symbolValues[aSymbol.SymbolName]
                        | FunInvocation _ ->                       
                            
                            evaluate2 (symbolValues, sysVarValueStack, (Some pop), false) parentFxBody
                            //evaluate2 (symbolValues, sysVarValueStack, (Some (fun () -> sysVarValueStack.TryPop() |> ignore))) parentFxBody
                        | _ ->
                            let uSL, frv =
                                nestedFxHandler parentFxParamSymbols parentFxBody symbolValues sysVarValueStack (Some pop)
                            let rFrv, rUSl = renameSymbols (uSL, frv) //20250413 symbol 名稱統一化後，快取才有意義

                            let expr, cmpl = Compile.compileExpressionOrThrow2 rFrv rUSl
                            let param_val = cal_param_obj_val ()
                        
                            let rst =
                                cmpl.DynamicInvoke(
                                    //20250413 symbol 名稱統一化後，取值仍需要用原先的變數名，所以上面的 uSL 不能少
                                    Array.append param_val (uSL |> List.skip parentFxParamSymbols.Length |> List.map (fun s -> box symbolValues[s.SymbolName]) |> List.toArray)
                                )
                            obj2FloatPoint rst
#if MINE
                //| DTProc procList ->
                    //let runOneProc (paramSymbols, defBody, outputSymbols) =
                    //    // 將輸入 Symbol list 轉成對應的 FloatingPoint list
                    //    let inputValues =
                    //        paramSymbols
                    //        |> List.map (fun sym ->
                    //            match symbolValues.TryGetValue(sym.SymbolName) with
                    //            | true, v ->
                    //                match v with
                    //                | Floating f -> f
                    //                | _ -> failwithf "DTProc input symbol %s must be Floating" sym.SymbolName
                    //            | _ -> failwithf "DTProc input symbol %s not found" sym.SymbolName
                    //        )

                    //    // 建立一個空白環境（或者從 symbolValues 建立？）
                    //    let env = ConcurrentDictionary<string, FloatingPoint>()

                    //    // 評估 DefBody
                    //    match defBody with
                    //    | DBFun f ->
                    //        let updatedEnv = f env inputValues
                    //        outputSymbols
                    //        |> List.map (fun sym ->
                    //            match updatedEnv.TryGetValue(sym.SymbolName) with
                    //            | true, fp -> Floating fp
                    //            | _ -> failwithf "DTProc output symbol %s not found" sym.SymbolName
                    //        )
                    //    | DBExp exprArr ->
                    //        // 用目前 symbolValues 映射成 IDictionary<string, FloatingPoint> 供 evaluate 使用
                    //        let localEnv =
                    //            symbolValues
                    //            |> Seq.choose (fun kvp ->
                    //                match kvp.Value with
                    //                | Floating f -> Some (kvp.Key, f)
                    //                | _ -> None
                    //            )
                    //            |> dict

                    //        let results =
                    //            exprArr
                    //            |> Array.map (fun expr -> Linq.ExprHelper.evaluate localEnv expr)

                    //        if results.Length <> outputSymbols.Length then
                    //            failwithf "DTProc DBExp output length mismatch: expected %d but got %d" outputSymbols.Length results.Length

                    //        Array.zip outputSymbols results
                    //        |> Array.map (fun (sym, f) -> Floating f)
                    //        |> Array.toList
                    //// collect 所有 proc 結果
                    //procList
                    //|> List.collect runOneProc
                    //|> ValueList
                    //match fx_real with
                    //| Choice1Of2 (extraParams, frv) ->
                    //    let expr, cmpl = Compile.compileExpressionOrThrow2 frv (List.append param extraParams)
                    //    let param_val =
                    //        Array.append (cal_param_obj_val ()) 
                    //    //let rst = cmpl.DynamicInvoke(param_val:obj[])
                    //    //obj2FloatPoint rst
                    //    failwith "orz123"
                    //| Choice2Of2 (extraParams, frv) ->
                    //    evaluate2 (symbolValues_, sysVarValues) frv
#endif
#if DTPROC_old
                | DTProc procList ->
                    let procScope _ = ConcurrentDictionary<string, FloatingPoint>() |> Context //供圖靈機 IO
                    let psId = System.Guid.NewGuid().ToString()
                    let _ = symbolValues.GetOrAdd(psId, procScope)

                    let rec evalProc (procScopeId:string) (sds:((Symbol list) * DefBody) list) (prevBodyOpt: ((Symbol list) * DefBody) option) (previousOutputOpt:ConcurrentDictionary<string, FloatingPoint> option) =
                        match sds with
                        | [] ->
                            match prevBodyOpt with
                            | Some (sbl, DBExp (expr,defOut)) ->

                        | (_params, body)::rest ->
                            let evaluatedArgsOfParentCall = exprsInFuncParamEvaluation _params paramValueExprList
                            match body with
                            | DBExp (fxs, scopedOut) ->
                                let param_val:obj[] = cal_param_obj_val ()
                                previousOutputOpt.Value
                            | DBFun f ->
                                let gc = 
                               
                    let _ = evalProc psId procList None None
                    Undef
#endif
#if DTPROC_Gemini_001 // Conditional compilation flag for DTProc feature
                 | DTProc procList -> // DTProc of ((Symbol list) * DefBody * (Symbol list)) list
                     // --- DTProc Execution Logic ---
                     // 1. Create a new scope for this procedure execution.
                     //    This scope inherits from the current scope (symbolValues)
                     //    but modifications within the proc won't affect the outer scope directly
                     //    unless explicitly using SetGlobal.
                     let procScope = ConcurrentDictionary<string, FloatingPoint>(symbolValues) // Inherit outer scope

                     // Add a reference to the global scope (needed for Set/GetGlobal)
                     match symbolValues.TryGetValue("global") with
                     | true, globalCtx -> procScope.TryAdd("global", globalCtx) |> ignore
                     | _ -> failwith "Global context not found during DTProc evaluation"

                     // Add arguments to the new scope
                     if paramValueExprList.Length <> (fst procList.[0]).Length then // Assuming all procs in the list have same input signature
                          failwithf "DTProc %s parameter count mismatch. Expected %d, Got %d" parentFxName (fst procList.[0]).Length paramValueExprList.Length

                     let evaluatedArgs = paramValueExprList |> List.map (evaluate2 (symbolValues, sysVarValuesOpt))

                     List.zip (fst procList.[0]) evaluatedArgs
                     |> List.iter (fun (sym, value) -> procScope.[sym.SymbolName] <- value)


                     // 2. Execute the sequence of procedures (DefBody) within the new scope.
                     //    This requires iterating through the procList and evaluating each DefBody.
                     //    The exact evaluation depends on whether DefBody is DBExp or DBFun.
                     let mutable lastResult: FloatingPoint = Undef // Procedures might implicitly return the last value

                     for (inSymbols, body) in procList do
                         // (Re-verify inSymbols match? Or assume they are consistent for a given DTProc name)

                         match body with
                         | DBExp (expr, defOut) ->
                             // Evaluate the expression within the procScope
                             // This nested call uses the procScope
                             lastResult <- evaluate2 (procScope, None) expr // Evaluate within the proc scope

                             match defOut with
                             | OutVar outSymbols ->
                             // Handle potential output symbol assignment (if DefBody carried output info)
                             // NOTE: The original DTProc definition had output symbols.
                             // If a single DBExp is meant to produce outputs, how is it specified?
                             // Assuming for now DBExp implicitly returns its value, and maybe assigns to ONE output symbol if specified.
                                 if outSymbols.Length = 1 then
                                     procScope.[(List.head outSymbols).SymbolName] <- lastResult
                                 elif outSymbols.Length > 1 then
                                      printfn "Warning: DBExp in DTProc %s has multiple output symbols but returns single value. Assigning to first symbol only." parentFxName
                                      procScope.[(List.head outSymbols).SymbolName] <- lastResult

                         | DBFun func ->
                             // The function `func` needs access to the procScope to Get/Set scoped variables.
                             // This requires `func`'s signature to accept the scope.
                             // Let's redefine DBFun slightly for this:
                             // type DefBody = ... | DBFun of (ConcurrentDictionary<string, FloatingPoint> -> FloatingPoint)
                             // This allows the function to interact with its environment.
                             lastResult <- func procScope // Execute the function, passing the scope

                             // Output assignment is handled *within* the DBFun implementation
                             // (e.g., by modifying the passed-in procScope)

                         | _ -> failwith "Unsupported DefBody type within DTProc"


                     // 3. Return the final result.
                     //    What DTProc returns is debatable. Options:
                     //    a) The value of the last expression/function evaluated.
                     //    b) A specific "return" value set within the scope.
                     //    c) A record/map of the output symbols.
                     //    Let's assume it returns the value of the last evaluated body for now.
                     lastResult // Return the result of the last step

#endif // DTPROC End
#if DTPROC_GPT
                | DTProc procList ->
                    // --- DTProc Evaluation (修正版 for FloatingPoint.Context) ---

                    // 1. 建立新的 procScope，繼承自外層 symbolValues (單純copy，不是parent link)
                    let procScope = ConcurrentDictionary<string, FloatingPoint>()
                    let procId = Guid.NewGuid().ToString()

                    // 2. 確保 procScope 中 "global" 存在（用來支援 SetGlobal/GetGlobal）
                    match symbolValues.TryGetValue("scoped") with
                    | true, globalCtx -> 
                        procScope.TryAdd("scoped", globalCtx) |> ignore
                    | _ -> failwith "DTProc 執行時找不到 global scope，請先建立全域環境。"

                    // 3. 處理參數綁定
                    let (paramSyms, _) = procList.Head
                    if paramSyms.Length <> paramValueExprList.Length then
                        failwithf "DTProc 參數數量錯誤。預期 %d 個，實際收到 %d 個。" paramSyms.Length paramValueExprList.Length

                    let evaluatedArgs = paramValueExprList |> List.map (evaluate2 (symbolValues, sysVarValuesOpt))

                    List.zip paramSyms evaluatedArgs
                    |> List.iter (fun (sym, value) -> procScope.[sym.SymbolName] <- value)

                    // 4. 執行每個 DefBody
                    let mutable lastResult: FloatingPoint = Undef

                    for (inSyms, body) in procList do
                        match body with
                        | DBExp (exprList, defOut) ->
                            let mutable lastExprVal = Undef
                            for expr in exprList do
                                lastExprVal <- evaluate2 (procScope, sysVarValuesOpt) expr
                            // 處理 OutVar/OutFP/OutCtx
                            match defOut with
                            | OutVar outSyms ->
                                match outSyms, lastExprVal with
                                | [outSym], _ ->
                                    procScope.[outSym.SymbolName] <- lastExprVal
                                | outSyms, FloatingPoint.NestedMap m when outSyms.Length = m.Count ->
                                    outSyms
                                    |> List.iter (fun sym ->
                                        match m.TryGetValue(sym.SymbolName) with
                                        | true, v -> procScope.[sym.SymbolName] <- v
                                        | _ -> failwithf "NestedMap 中找不到欄位 %s" sym.SymbolName)
                                | [], _ -> () // 無輸出
                                | _ -> failwith "DBExp 輸出符號數量與回傳值不匹配。"
                            | OutFP -> ()
                            | OutCtx -> ()
                            lastResult <- lastExprVal

                        | DBFun almightyFun ->
                            lastResult <- almightyFun (Some symbolValues) None None procScope

                        | _ -> failwith "未知 DefBody 型別，無法處理。"



                    lastResult
#endif
                    | DTProc procList ->
                        let procStepId = System.Guid.NewGuid().ToString()
                        
                        let rec evalProc
                            (procList_: ((Symbol list) * DefBody) list)
                            (prevOutputOpt: FloatingPoint option)
                            (scopedContextOpt: ConcurrentDictionary<string, FloatingPoint> option)
                            (paramValueExprListOpt: MathNet.Symbolics.Expression list option (*第0層非空*))
                            (ifTopInProc:bool)
                            (procStepId_:string)
                            =
                            match procList_ with
                            | [] ->
                                pop()
                                // 所有過程處理完畢，返回最後的輸出
                                prevOutputOpt.Value
                            | (paramSymbols, defBody) :: restProcList ->
                                if paramValueExprListOpt.IsSome then
                                    //頂層函數吃到的表達式傳入
                                    let paramValueExprList_ = paramValueExprListOpt.Value
                                    let evaluatedArgsOfParentCall = exprsInFuncParamEvaluation paramSymbols paramValueExprList_ ifTop
                                    evaluatedArgsOfParentCall
                                else
                                    //第一層 defBody 輸出綁 第二層 paramSymbols
                                    let input = 
                                        if paramSymbols.Length > 1 then
                                            match prevOutputOpt.Value with
                                            | (NestedList l) ->
                                                l
                                            | (NestedExpr l) ->
                                                failwith "尚未實作輸出為 Expr list 的部分"
                                            | _ ->
                                                failwith "輸出輸入不匹配"
                                        elif paramSymbols.Length = 1 then
                                            [prevOutputOpt.Value]
                                        else
                                            []
                                        |> fun outFPList ->
                                            ((paramSymbols |> List.map (fun s -> s.SymbolName)), outFPList)
                                            ||> List.zip
                                    input
                                |> Seq.append (seq["stepId", Str procStepId_])
                                |> fun s ->
                                    if ifTop then
                                        sctx.TryAdds s
                                    else
                                        dict s
                                        |> ConcurrentDictionary<_, _>
                                        |> Some
                                        |> sysVarValueStack.Push (* 會在
                                                            match procList_ with
                                                            | [] ->
                                                                somePop.Value()
                                                            pop 掉
                                *)
                                        
                                let currentScopedContext = //for this DefBody
                                    if scopedContextOpt.IsNone then
                                        scopeCtx().ctx
                                    else
                                        scopedContextOpt.Value
                    
                                let rst =
                                    match defBody with
                                    | DBFun almightFun ->
                                        let (Context gsc) = symbolValues["global"]
                                        let sv = almightFun gsc currentScopedContext prevOutputOpt sysVarValueStack paramValueExprListOpt ifTopInProc
                                        currentScopedContext["it"] <- sv
                                        sv
                                    | DBExp (exprList, defOut) ->
                                        let scopedSymbolValues = ConcurrentDictionary<string, FloatingPoint> currentScopedContext
                                        scopedSymbolValues["global"] <- symbolValues["global"]
                                        let sv =
                                            exprList
                                            |> List.fold (fun s a ->
                                                let sv = evaluate2 (scopedSymbolValues, sysVarValueStack, None, false) a
                                                scopedSymbolValues["it"] <- sv
                                                sv
                                            ) Undef

                                        scopedSymbolValues["it"] <- sv

                                        match defOut with
                                        | OutCtx ->
                                            Context scopedSymbolValues
                                        | OutFP ->
                                            sv
                                        | OutVar vl ->
                                            vl |> List.map (fun s -> getValue s.SymbolName) |> NestedList


                                evalProc restProcList (Some rst) (Some currentScopedContext) None ifTopInProc (System.Guid.NewGuid().ToString())

                        let finalOutput =
                                evalProc     procList  None       None                      (Some paramValueExprList) ifTop procStepId
                        finalOutput
#if DTPROC_MANUS        
//#else
                    | DTProc procList ->
                        // 創建一個新的作用域上下文
                        let procScope = ConcurrentDictionary<string, FloatingPoint>()
                        let psId = System.Guid.NewGuid().ToString()
                        let globalContext = symbolValues // 全局上下文
    
                        // 遞迴處理procList中的每個過程定義
                        let rec evalProc (procList: ((Symbol list) * DefBody) list) (prevOutput: FloatingPoint) (scopedContext: ConcurrentDictionary<string, FloatingPoint> option) =
                            match procList with
                            | [] -> 
                                // 所有過程處理完畢，返回最後的輸出
                                prevOutput
            
                            | (paramSymbols, defBody) :: restProcs ->
                                // 檢查參數數量是否匹配
                                if paramSymbols.Length <> paramValueExprList.Length then
                                    failwithf "%s parameter length not matched %A <-> %A" parentFxName paramSymbols paramValueExprList
            
                                // 創建新的作用域上下文（如果尚未存在）
                                let currentScopedContext = 
                                    match scopedContext with
                                    | Some ctx -> ctx
                                    | None -> ConcurrentDictionary<string, FloatingPoint>()
            
                                // 評估參數並將其添加到作用域上下文
                                for i = 0 to paramSymbols.Length - 1 do
                                    let paramSymbol = paramSymbols.[i]
                                    let paramValue = evaluate2 (globalContext, sysVarValueStack, None) paramValueExprList.[i]
                                    currentScopedContext.[paramSymbol.SymbolName] <- paramValue
            
                                // 根據DefBody類型處理
                                let newOutput = 
                                    match defBody with
                                    | DBExp (exprList, defOutput) ->
                                        // 評估表達式列表
                                        let results = 
                                            exprList 
                                            |> List.map (fun expr -> evaluate2 (globalContext, sysVarValueStack, None) expr)
                    
                                        // 根據DefOutput類型處理輸出
                                        match defOutput with
                                        | OutVar symbols ->
                                            // 從作用域上下文中獲取指定變數的值
                                            if symbols.IsEmpty then
                                                // 如果沒有指定輸出變數，則返回最後一個表達式的結果
                                                List.last results
                                            else
                                                // 從作用域上下文中獲取指定變數的值
                                                let outputValues = 
                                                    symbols 
                                                    |> List.map (fun sym -> 
                                                        match currentScopedContext.TryGetValue(sym.SymbolName) with
                                                        | true, value -> value
                                                        | _ -> failwithf "Output symbol %s not found in scoped context" sym.SymbolName)
                            
                                                // 如果只有一個輸出變數，直接返回其值
                                                if outputValues.Length = 1 then
                                                    outputValues.[0]
                                                else
                                                    // 否則返回嵌套列表
                                                    NestedList outputValues
                    
                                        | OutFP ->
                                            // 返回最後一個表達式的結果
                                            List.last results
                    
                                        | OutCtx ->
                                            // 返回整個作用域上下文
                                            Context currentScopedContext
                
                                    | DBFun almightFun ->
                                        // 執行AlmightFun函數
                                        // 參數：全局上下文、前一個作用域上下文（可選）、前一個輸出、當前作用域上下文
                                        let scopedContextOutput = 
                                            almightFun globalContext scopedContext prevOutput currentScopedContext
                    
                                        // 返回函數的輸出
                                        scopedContextOutput
            
                                // 繼續處理剩餘的過程定義
                                evalProc restProcs newOutput (Some currentScopedContext)
    
                        // 開始處理過程列表，初始輸出為Undef，初始作用域上下文為None
                        let finalOutput = evalProc procList Undef None
                        finalOutput
#endif
                    | DTFunI1toI1 f ->
                        let param_val = cal_param_real_val ()
                        f (int param_val.[0]) |> float |> Real
                    | DTFunF2toV1 f ->
                        let param_val = cal_param_real_val ()
                        f param_val.[0] param_val.[1] |> RealVector
                    | DTCurF2toV1 (f, (Symbol sym)) ->
                        let param_val = cal_param_real_val ()
                        let cur = symbolValues.[sym].DecimalValue
                        f cur param_val.[0] param_val.[1] |> RealVector
                    | DTCurF3toV1 (f, (Symbol sym)) ->
                        let param_val = cal_param_real_val ()
                        let cur = symbolValues.[sym].DecimalValue
                        f cur param_val.[0] param_val.[1] param_val.[2] |> RealVector
                    | DTFunAction f ->
                        f ()
                        Undef

                match postFunOpt_ with
                | Some p -> p ()
                | None -> ()
                r

    let evaluate2_
        (symbolValues:ConcurrentDictionary<string, FloatingPoint>)
        (sysVarValuesStack:ConcurrentStack<ConcurrentDictionary<string, FloatingPoint> option>) ifTop =
        evaluate2 (symbolValues, sysVarValuesStack, None, ifTop)

    

    [<CompiledName("Evaluate")>]
    let rec evaluate (symbolValues_:IDictionary<string, FloatingPoint>) =
        let sysVarValuesStack = ConcurrentStack<_>() //最頂層
        let symbolValues = ConcurrentDictionary<string, FloatingPoint> symbolValues_
        //let globalScope _ = ConcurrentDictionary<string, FloatingPoint>() |> Context //供圖靈機 IO
        let curGS = symbolValues.GetOrAdd("global", scopeCtx)
        match curGS with
        | Context _ -> ()
        | _ ->
            failwith "invalid GlobalContext!"
        evaluate2 (symbolValues, sysVarValuesStack, None, true)
        


    [<CompiledName("EvaluateCorrect")>]
    let rec evaluate_correct (symbols:IDictionary<string, FloatingPoint>) =
        let symbolValues = ConcurrentDictionary<string, FloatingPoint> symbols
        let globalScope _ = ConcurrentDictionary<string, FloatingPoint>() |> Context //供圖靈機 IO
        let curGS = symbolValues.GetOrAdd("global", globalScope)
        match curGS with
        | Context _ -> ()
        | _ ->
            failwith "invalid GlobalContext!"
        evaluate2_with_dict_svv (symbolValues, None)


    Linq.ExprHelper.evaluate <- evaluate



    ///很愚蠢的 Mode0 實驗
    [<CompiledName("Evaluate2Mode0")>]
    //let rec evaluate2 (symbolValues:ConcurrentDictionary<string, FloatingPoint>, sysVarValueStack:ConcurrentStack<IDictionary<string, FloatingPoint> option>, postFun: (unit -> unit) option) = function
    let rec evaluate2Mode0 (symbolValues:ConcurrentDictionary<string, FloatingPoint>, sysVarValueStack:ConcurrentStack<IDictionary<string, FloatingPoint> option>) = function
        | Number n -> Real (float n) |> fnormalize
        | Undefined -> Undef
        | ComplexInfinity -> ComplexInf
        | PositiveInfinity -> PosInf
        | NegativeInfinity -> NegInf
        | Constant E -> Real (Constants.E)
        | Constant Pi -> Real (Constants.Pi)
        | Constant I -> Complex (Complex.onei)
        | Approximation (Approximation.Real fp) -> Real fp
        | Approximation (Approximation.Complex fp) -> Complex fp
        | Identifier (Symbol s) ->
                //if sysVarValueStack.IsNone then
                //    match symbolValues.TryGetValue s with
                //    | true, a -> a |> fnormalize
                //    | _ ->
                //        failwithf  "Failed to find symbol %s" s
                //else
                    match sysVarValueStack.StackValueMode0().TryGetValue s with
                    | true, a -> a |> fnormalize
                    | _ ->
                        match symbolValues.TryGetValue s with
                        | true, a -> a |> fnormalize
                        | _ ->
                            failwithf  "Failed to find symbol %s" s
        | Argument (Symbol s) -> failwithf  "Cannot evaluate a argument %s" s
        //| Sum xs -> xs |> List.map (evaluate2 (symbolValues, sysVarValueStack, None)) |> List.reduce fadd |> fnormalize
        | Sum xs -> xs |> List.map (evaluate2Mode0 (symbolValues, sysVarValueStack)) |> List.reduce fadd |> fnormalize
        | Product xs ->
            //let evall = xs |> List.map (evaluate2 (symbolValues, sysVarValueStack, None))
            let evall = xs |> List.map (evaluate2Mode0 (symbolValues, sysVarValueStack))
            let reducel = evall |> List.reduce fmultiply
            reducel |> fnormalize
        | PointwiseMul (l, r) ->
                //let lv = evaluate2 (symbolValues, sysVarValueStack, None) l
                let lv = evaluate2Mode0 (symbolValues, sysVarValueStack) l
                //let rv = evaluate2 (symbolValues, sysVarValueStack, None) r
                let rv = evaluate2Mode0 (symbolValues, sysVarValueStack) r
                try
                    lv .* rv
                with ex ->
                    failwithf "PointwiseMul evaluation failed:\nLeft = %A\nRight = %A\nError = %s" lv rv ex.Message
        //| Power (r, p) -> fpower (evaluate2 (symbolValues, sysVarValueStack, None) r) (evaluate2 (symbolValues, sysVarValueStack, None) p) |> fnormalize
        | Power (r, p) -> fpower (evaluate2Mode0 (symbolValues, sysVarValueStack) r) (evaluate2Mode0 (symbolValues, sysVarValueStack) p) |> fnormalize
        //| Function (f, x) -> fapply f (evaluate2 (symbolValues, sysVarValueStack, None) x) |> fnormalize
        | Function (f, x) -> fapply f (evaluate2Mode0 (symbolValues, sysVarValueStack) x) |> fnormalize
        //| FunctionN (f, xs) -> xs |> List.map (evaluate2 (symbolValues, sysVarValueStack, None)) |> fapplyN f |> fnormalize
        | FunctionN (f, xs) -> xs |> List.map (evaluate2Mode0 (symbolValues, sysVarValueStack)) |> fapplyN f |> fnormalize
        | FunInvocation (Symbol parentFxName, paramValueExprList) ->
            let cleanStack () = sysVarValueStack.TryPop() |> ignore
            let cal_param_fd_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    //evaluate2 (symbolValues, sysVarValueStack, None) paramValueExpr
                    evaluate2Mode0 (symbolValues, sysVarValueStack) paramValueExpr
                )

            let cal_param_obj_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    //evaluate2 (symbolValues, sysVarValueStack, None) paramValueExpr |> box
                    evaluate2Mode0 (symbolValues, sysVarValueStack) paramValueExpr |> box
                )
                |> Array.ofList

            let cal_param_real_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    //match evaluate2 (symbolValues, sysVarValueStack, None) paramValueExpr with
                    match evaluate2Mode0 (symbolValues, sysVarValueStack) paramValueExpr with
                    | (FloatingPoint.Real v) -> v
                    | (FloatingPoint.Int v) -> float v
                    | (FloatingPoint.Decimal v) -> float v
                    | _ -> Double.NaN
                )
                |> Array.ofList
            let cal_param_vec_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    //match evaluate2 (symbolValues, sysVarValueStack, None) paramValueExpr with
                    match evaluate2Mode0 (symbolValues, sysVarValueStack) paramValueExpr with
                    | (RealVector v) -> v
                    | _ -> failwithf "vector parameter is required for %s" parentFxName
                )
                |> Array.ofList
            let cal_param_mat_vec_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    //match evaluate2 (symbolValues, sysVarValueStack, None) paramValueExpr with
                    match evaluate2Mode0 (symbolValues, sysVarValueStack) paramValueExpr with
                    | (FloatingPoint.RealVector v) -> FloatingPoint.RealVector v
                    | (FloatingPoint.RealMatrix v) -> FloatingPoint.RealMatrix v
                    | _ -> failwithf "vector parameter is required for %s" parentFxName
                )
                |> Array.ofList

            let cal_param_list_of_vec_val () : TensorWrapper list =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    //let evalrst = evaluate2 (symbolValues, sysVarValueStack, None) paramValueExpr
                    let evalrst = evaluate2Mode0 (symbolValues, sysVarValueStack) paramValueExpr
                    match evalrst with
                    | (FloatingPoint.RealVector v) ->
                        VecInTensor v //計算結果WTensor                    
                    | (FloatingPoint.WTensor tw) ->  tw
                    | _ -> failwithf "vector or WTensor parameter is required for %s" parentFxName
                )

            if keyWord.ContainsKey parentFxName then
                let mbr () =
                    let param_val = cal_param_vec_val ()
                    let m2 = DenseMatrix.zero<float> (param_val.Length) (param_val.[0].Count)
                    param_val
                    |> Array.iteri (fun i v ->
                        m2.SetRow(i, v)
                    )
                    m2
                let f () =
                    match parentFxName with
                    | "str" ->
                        match paramValueExprList[0] with
                        | Identifier (Symbol s) -> Str s
                        | _ ->
                            failwithf "Invalid str expression! %A" paramValueExprList
                    | "lo"
                    | "list_of" -> //無法知道自己是否是最上層，所以不能回傳 tensor
                        //htensor(list_of(list_of(list_of(vec(), vec()), list_of(vec(), vec()))))
                        let param_val = cal_param_list_of_vec_val ()
                        WTensor <| ListOf param_val
                        //failwithf "haven't yet implemented"
                    | "vec" ->
                        let param_val = cal_param_real_val ()
                    
                        RealVector <| vector param_val
                    | "mat_by_row" ->
                        RealMatrix (mbr ())
                    | "mat_by_col" ->
                        let m2 = mbr()
                        RealMatrix <| m2.Transpose()
                    | "htensor" -> //可以知道自己是最上層，回傳 tensor
#if TENSOR_SUPPORT
                        let param_val = cal_param_list_of_vec_val ()
                        if param_val.Length <> 1 then                        
                            failwithf "htensor only takes single list_of expression as input"
                        WTensor (DSTensor <| listOf2DSTensor param_val.[0])
#else
                        failwithf "Tensor not supported"
#endif
                    //| "htensor2" -> //可以知道自己是最上層，回傳 tensor
                    //    let param_val = cal_param_list_of_vec_val ()
                    //    if param_val.Length <> 2 then                        
                    //        failwithf "htensor2 takes 2 list_of expression as input"
                    //    let v1 = param_val.[0]
                    //    WTensor (DSTensor <| listOf2DSTensor )
                    | "gtensor" ->
                        failwithf "haven't yet implemented"
                    | "sym_ctensor" ->
                        failwithf "haven't yet implemented"
                    | "mat_multiply" ->
                        let param_val = cal_param_mat_vec_val ()
                        param_val
                        |> Array.skip 1
                        |> Array.fold (fun s a ->
                            match s with
                            | RealVector vs ->
                                match a with
                                | RealVector va ->
                                    let r = vs * va
                                    Real r
                                | RealMatrix ma ->
                                    let r = vs * ma
                                    RealVector r
                                | Real ra ->
                                    RealVector (vs * ra)
                                | Int ra ->
                                    RealVector (vs * float ra)
                                | Decimal ra ->
                                    RealVector (vs * float ra)
                                | _ ->
                                    failwithf "orz 0001"
                            | RealMatrix ms ->
                                match a with
                                | RealVector va ->
                                    let r = ms * va
                                    RealVector r
                                | RealMatrix ma ->
                                    let r = ms * ma
                                    RealMatrix r
                                | Real ra ->
                                    let r = ra * ms
                                    RealMatrix r
                                | Int ra ->
                                    RealMatrix (ms * float ra)
                                | Decimal ra ->
                                    RealMatrix (ms * float ra)
                                | _ ->
                                    failwithf "orz 0002"
                            | Real rs ->
                                match a with
                                | RealVector va ->
                                    let r = rs * va
                                    RealVector r
                                | RealMatrix ma ->
                                    let r = rs * ma
                                    RealMatrix r
                                | Real ra ->
                                    let r = ra * rs
                                    Real r
                                | Int ra ->
                                    Real (rs * float ra)
                                | Decimal ra ->
                                    Real (rs * float ra)
                                | _ ->
                                    failwithf "orz 0003"
                            | Int rs ->
                                match a with
                                | RealVector va ->
                                    let r = (float rs) * va
                                    RealVector r
                                | RealMatrix ma ->
                                    let r = (float rs) * ma
                                    RealMatrix r
                                | Real ra ->
                                    let r = ra * float rs
                                    Real r
                                | Int ra ->
                                    Real (float rs * float ra)
                                | Decimal ra ->
                                    Real (float rs * float ra)
                                | _ ->
                                    failwithf "orz 0004"
                            | Decimal rs ->
                                match a with
                                | RealVector va ->
                                    let r = (float rs) * va
                                    RealVector r
                                | RealMatrix ma ->
                                    let r = (float rs) * ma
                                    RealMatrix r
                                | Real ra ->
                                    let r = ra * float rs
                                    Real r
                                | Int ra ->
                                    Real (float rs * float ra)
                                | Decimal ra ->
                                    Real (float rs * float ra)
                                | _ ->
                                    failwithf "orz 0005"
                            | _ ->
                                failwithf "orz 0006"
                        ) param_val.[0]
                    | _ ->
                        failwithf $"omg fnm {parentFxName}!!!"

                //match postFun with
                //| Some p ->
                //    let r = f ()
                //    p ()
                //    r
                //| None ->
                //    f ()
                f ()

            else

                let rec nestedFxHandler
                    (sl: Symbol list) //fxExpr 中 sl 的變數需要
                    (fxExpr: MathNet.Symbolics.Expression)
                    //(paramValueExprList_:MathNet.Symbolics.Expression list option)
                    (symbolValues_: ConcurrentDictionary<string, FloatingPoint>)
                    //(sysVarValues_: IDictionary<string, FloatingPoint> option) //代換為這裡的值
                    //(sysVarValueStack_:ConcurrentStack<IDictionary<string, FloatingPoint> option>)
                    (postFun_: (unit -> unit) option)
                    : (Symbol list) * (MathNet.Symbolics.Expression) =

                    let exprMap sl_ (exprs:MathNet.Symbolics.Expression list) =
                        exprs
                        |> List.fold (fun (symL, uExprs) expr ->
                            //let usl, uExpr = nestedFxHandler symL expr symbolValues_ sysVarValueStack_ None
                            let usl, uExpr = nestedFxHandler symL expr symbolValues_ None
                            usl, uExprs @ [uExpr]
                        ) (sl_, [])

                    let traverse sl_ expr =
                        match expr with
                        | Sum terms ->
                            let updatedSL, uExprs = exprMap sl_ terms
                            updatedSL, Sum uExprs
                        | Product terms ->
                            let updatedSL, uExprs = exprMap sl_ terms
                            updatedSL, Product uExprs
                        | Power (baseExpr, expExpr) ->
                            //let updatedSL, uExpr = nestedFxHandler sl_ baseExpr symbolValues_ sysVarValueStack_ None
                            let updatedSL, uExpr = nestedFxHandler sl_ baseExpr symbolValues_ None
                            //let updatedSL2, uExpExpr = nestedFxHandler updatedSL expExpr symbolValues_ sysVarValueStack_ None
                            let updatedSL2, uExpExpr = nestedFxHandler updatedSL expExpr symbolValues_ None
                            updatedSL2, Power (uExpr, uExpExpr)
                        | Function (func, arg) ->
                            //let updatedSL, uExpr = nestedFxHandler sl_ arg symbolValues_ sysVarValueStack_ None
                            let updatedSL, uExpr = nestedFxHandler sl_ arg symbolValues_ None
                            updatedSL, Function (func, uExpr)
                        | FunctionN (func, args) ->
                            let updatedSL, uExprs = exprMap sl_ args
                            updatedSL, FunctionN (func, uExprs)
                        | _ ->
                            sl_, expr

                    let r = 
                        match fxExpr with
                        | FunInvocation ((Symbol sb), origParamExp) when Definition.funDict.ContainsKey sb ->
                            let evaluatedValue =
                                origParamExp
                                |> List.map (fun param ->
                                    let newSymbolName = $"__{sb}_{Guid.NewGuid().ToString()}__"
                                    let newSymbol = Symbol newSymbolName
                                    //let paramValue = evaluate2 (symbolValues_, sysVarValueStack, None) param
                                    let paramValue = evaluate2Mode0 (symbolValues_, sysVarValueStack) param
                                    symbolValues_.TryAdd(newSymbolName, paramValue) |> ignore
                                    Identifier newSymbol
                                )
                        
                        

                            let newSymbolNameAggRst = $"__{sb}_{Guid.NewGuid().ToString()}__"
                            let newSymbolAggRst = Symbol newSymbolNameAggRst
                        
                            //let evaluatedFunValue = evaluate2 (symbolValues_, sysVarValueStack_, (Some (fun () -> sysVarValueStack_.TryPop() |> ignore))) (FunInvocation ((Symbol sb), evaluatedValue))
                            //let evaluatedFunValue = evaluate2 (symbolValues_, sysVarValueStack, None) (FunInvocation ((Symbol sb), evaluatedValue))
                            let evaluatedFunValue = evaluate2Mode0 (symbolValues_, sysVarValueStack) (FunInvocation ((Symbol sb), evaluatedValue))
                            symbolValues_.TryAdd(newSymbolNameAggRst, evaluatedFunValue) |> ignore
                            FAkka.Microsoft.FSharp.Core.LeveledPrintf.frintfn FAkka.Microsoft.FSharp.Core.LeveledPrintf.PRINTLEVEL.PWARN "Dynamic symbol added: %A" newSymbolAggRst
                            sl, Identifier newSymbolAggRst

                        | FunInvocation _ ->
                            failwith $"Undefined func {fxExpr}"
                        
                        | _ ->
                            let updatedSL, traversed = traverse sl fxExpr
                            let allSymbols = ExpressionHelpFun.collectIdentifiers traversed |> Seq.toList
                            allSymbols
                            |> List.except updatedSL
                            |> List.append updatedSL
                            |> fun u ->
                                //if u.Length > allSymbols.Length then
                                //    FAkka.Microsoft.FSharp.Core.LeveledPrintf.frintfn FAkka.Microsoft.FSharp.Core.LeveledPrintf.PRINTLEVEL.PWARN "Dynamic symbol list occured:\r\nOriginal: %A\r\n Updated: %A" allSymbols u
                                u, traversed
                    //match postFun_ with
                    //| Some p -> p ()
                    //| None -> ()
                    r

                let exprsInFuncParamEvaluation (symbols:Symbol list) (exprs:MathNet.Symbolics.Expression list) =
                    symbols
                    |> Seq.mapi (fun i sb ->
                        //sb.SymbolName, evaluate2 (symbolValues, sysVarValueStack, None) exprs[i]
                        sb.SymbolName, evaluate2Mode0 (symbolValues, sysVarValueStack) exprs[i]
                    )

                //let r =
                if false then
                    failwith "not happened"
                else
                    match funDict.[parentFxName] with
                    //       x1, y1    dup0(paramValueExprList)
                    | DTExp (parentFxParamSymbols, parentFxBody) ->
                        if parentFxParamSymbols.Length <> paramValueExprList.Length then
                            failwithf "%s parameter length not matched %A <-> %A" parentFxName parentFxParamSymbols paramValueExprList
                         
                        let evaluatedArgsOfParentCall = exprsInFuncParamEvaluation parentFxParamSymbols paramValueExprList
                        sysVarValueStack.Push (Some (ConcurrentDictionary<_, _> (dict evaluatedArgsOfParentCall)))

                        match parentFxBody with
                        | Identifier aSymbol ->
                            symbolValues[aSymbol.SymbolName]
                        | FunInvocation _ ->                       
                        
                            //evaluate2 (symbolValues, sysVarValueStack, (Some (sysVarValueStack.TryPop >> ignore))) parentFxBody
                            //evaluate2 (symbolValues, sysVarValueStack, (Some (fun () -> sysVarValueStack.TryPop() |> ignore))) parentFxBody
                            let r = evaluate2Mode0 (symbolValues, sysVarValueStack) parentFxBody
                            cleanStack ()
                            r
                        | _ ->
                            let uSL, frv =
                                //nestedFxHandler parentFxParamSymbols parentFxBody symbolValues sysVarValueStack (Some (sysVarValueStack.TryPop >> ignore))
                                //nestedFxHandler parentFxParamSymbols parentFxBody symbolValues sysVarValueStack (Some (fun () -> sysVarValueStack.TryPop() |> ignore))
                                //nestedFxHandler parentFxParamSymbols parentFxBody symbolValues (Some (fun () -> sysVarValueStack.TryPop() |> ignore))
                                nestedFxHandler parentFxParamSymbols parentFxBody symbolValues None
                            let rFrv, rUSl = renameSymbols (uSL, frv) //20250413 symbol 名稱統一化後，快取才有意義

                            let expr, cmpl = Compile.compileExpressionOrThrow2 rFrv rUSl
                            let param_val = cal_param_obj_val ()
                        
                            let rst =
                                cmpl.DynamicInvoke(
                                    //20250413 symbol 名稱統一化後，取值仍需要用原先的變數名，所以上面的 uSL 不能少
                                    Array.append param_val (uSL |> List.skip parentFxParamSymbols.Length |> List.map (fun s -> box symbolValues[s.SymbolName]) |> List.toArray)
                                )
                            obj2FloatPoint rst
                    | DTFunI1toI1 f ->
                        let param_val = cal_param_real_val ()
                        f (int param_val.[0]) |> float |> Real
                    | DTFunF2toV1 f ->
                        let param_val = cal_param_real_val ()
                        f param_val.[0] param_val.[1] |> RealVector
                    | DTCurF2toV1 (f, (Symbol sym)) ->
                        let param_val = cal_param_real_val ()
                        let cur = symbolValues.[sym].DecimalValue
                        f cur param_val.[0] param_val.[1] |> RealVector
                    | DTCurF3toV1 (f, (Symbol sym)) ->
                        let param_val = cal_param_real_val ()
                        let cur = symbolValues.[sym].DecimalValue
                        f cur param_val.[0] param_val.[1] param_val.[2] |> RealVector
                    | DTFunAction f ->
                        f ()
                        Undef

    let evaluate2Mode0_ (symbolValues:ConcurrentDictionary<string, FloatingPoint>) (sysVarValuesOpt:ConcurrentStack<IDictionary<string, FloatingPoint> option>) =
        evaluate2Mode0 (symbolValues, sysVarValuesOpt)

    [<CompiledName("EvaluateMode0")>]
    let rec evaluateMode0 (symbols:IDictionary<string, FloatingPoint>) =
        let sysVarValuesStack = ConcurrentStack<_>()
        let symbolValues = ConcurrentDictionary<string, FloatingPoint> symbols
        let globalScope _ = ConcurrentDictionary<string, FloatingPoint>() |> Context //供圖靈機 IO
        let curGS = symbolValues.GetOrAdd("global", globalScope)
        match curGS with
        | Context _ -> ()
        | _ ->
            failwith "invalid GlobalContext!"
        evaluate2Mode0 (symbolValues, sysVarValuesStack)
