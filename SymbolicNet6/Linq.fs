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
open DiffSharp


type TensorWrapper =
| DSTensor of Tensor
| VecInTensor of Vector<float>
| ListOf of TensorWrapper list

and [<NoComparison>] FloatingPoint =
    | Real of float
    | Complex of complex
    | RealVector of Vector<float>
    | ComplexVector of Vector<complex>
    | RealMatrix of Matrix<float>
    | ComplexMatrix of Matrix<complex>
    | Undef
    | PosInf
    | NegInf
    | ComplexInf
    | WTensor of TensorWrapper

    // Simpler usage in C#
    static member op_Implicit (x:float) = Real x
    static member op_Implicit (x:float32) = Real (float x)
    static member op_Implicit (x:complex) = Complex x
    static member op_Implicit (x:complex32) = Complex (Primitive.complex x)
    static member op_Implicit (x:Vector<float>) = RealVector x
    static member op_Implicit (x:Vector<complex>) = ComplexVector x
    static member op_Implicit (x:Matrix<float>) = RealMatrix x
    static member op_Implicit (x:Matrix<complex>) = ComplexMatrix x
    static member op_Implicit (x:Tensor) = WTensor <| DSTensor x
    static member (*) ((a:FloatingPoint), (b: FloatingPoint)) =
        Real 0
    static member (*) ((a:float), (b: FloatingPoint)) =
        Real 0
    static member (*) ((a:FloatingPoint), (b: float)) =
        Real 0 
    member x.RealValue =
        match x with
        | Real x -> x
        | Complex x when x.IsReal() -> x.Real
        | _ -> failwith "Value not convertible to a real number."
    member x.ComplexValue =
        match x with
        | Real x -> complex x 0.0
        | Complex x -> x
        | _ -> failwith "Value not convertible to a complex number."
    member x.RealVectorValue =
        match x with
        | RealVector x -> x
        | _ -> failwith "Value not convertible to a real vector."
    member x.ComplexVectorValue =
        match x with
        | ComplexVector x -> x
        | _ -> failwith "Value not convertible to a complex vector."
    member x.RealMatrixValue =
        match x with
        | RealMatrix x -> x
        | _ -> failwith "Value not convertible to a real matrix."
    member x.ComplexMatrixValue =
        match x with
        | ComplexMatrix x -> x
        | _ -> failwith "Value not convertible to a complex matrix."
    member x.DTensorValue =
        match x with
        | WTensor (DSTensor x) -> x
        | _ -> failwith "Value not convertible to a DSTensor."


[<RequireQualifiedAccess>]
module Linq =
    open Microsoft.FSharp.Linq.RuntimeHelpers
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

    [<CompiledName("Parse")>]
    let rec parse (q:Expression) : MathNet.Symbolics.Expression =
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
        | _ -> failwith "not supported"

    let rec private numerator = function
        | NegPower _ -> one
        | Product ax -> product <| List.map numerator ax
        | z -> z

    let rec private denominator = function
        | NegPower (r, p) -> r ** -p
        | Product ax -> product <| List.map denominator ax
        | _ -> one

    let rec translateExpr (linq:Expression) = 
        match linq with
        | :? MethodCallExpression as mc ->
            let le = mc.Arguments.[0] :?> LambdaExpression
            let args, body = translateExpr le.Body
            le.Parameters.[0] :: args, body
        | _ -> [], linq

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
            | :? Value -> (j :?> Value) 
            | _ when j.GetType() = typeof<float> ->
                //failwith "orz"
                //MathNet.Symbolics.Value.fromDouble  0.0
                Value.Approximation (Approximation.Real (j :?> float))
            | :? Vector<float> ->
                Value.RealVec (j :?> Vector<float>)
            | :? Matrix<float> ->
                Value.RealMat (j :?> Matrix<float>)
            | _ ->
                failwithf "orz010: %s, %A" (j.GetType().FullName) j
            )
            :> Expression :?> LambdaExpression

           
    let exprFloatingPoint2ValueToInject = 
        ExprHelper.Quote<Func<FloatingPoint, MathNet.Symbolics.Value>> (fun j ->
            match j with
            | Real r -> Value.Approximation (Approximation.Real r)
            | Complex c -> Value.fromComplex c
            | RealVector rv ->
                Value.RealVec rv
            | RealMatrix rm ->
                Value.RealMat rm
            | WTensor (DSTensor dt) -> Value.DSTen dt
            | _ ->
                failwithf "exprFloatingPoint2ValueToInject not supported!!! %A" j
            )
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
                | _ ->
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
                let b = convertExpr (Power(n, m))
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
                let vv =
                    match exprv with
                    | Some exprvv -> exprvv
                    | None ->
                        Unchecked.defaultof<Expression>
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

    and [<CompiledName("FormatValueLambda")>] formatValueLambda (expr : MathNet.Symbolics.Expression) (args : Symbol list) : LambdaExpression option =
        let value = function
            | Value.Approximation a -> Some (Expression.Constant a.RealValue :> Expression)
            | Value.NegativeInfinity -> Some (Expression.Constant System.Double.NegativeInfinity :> Expression)
            | Value.PositiveInfinity -> Some (Expression.Constant System.Double.PositiveInfinity :> Expression)
            | Value.Number n -> Some (Expression.Constant (float n) :> Expression)
            | Value.RealVec v ->
                Some (Expression.Constant v :> Expression)
            | _ ->
                None
        let constant = function
            | E -> Some (Expression.Constant Constants.E :> Expression)
            | Pi -> Some (Expression.Constant Constants.Pi :> Expression)
            | _ -> None
        let valueType = typeof<float>
        let mathType = typeof<System.Math>
        let add a b = Expression.Add(a, b) :> Expression
        let mul = sharedMul
        let div a b = Expression.Divide(a, b) :> Expression
        let mathCall1 (name : string) (a : Expression) = Expression.Call(mathType.GetMethod(name, [| valueType |]), a) :> Expression
        let mathCall2 (name : string) (a : Expression) (b : Expression) = Expression.Call(mathType.GetMethod(name, [| valueType; valueType |]), a, b) :> Expression
        let pow = mathCall2 "Pow"
        let atan2 = mathCall2 "Atan2"
        let log a b = mathCall2 "Log" b a
        let abs = mathCall1 "Abs"
        formatLambdaBase expr args valueType mathType (Some typeof<Value>) mathCall2 constant value add mul div pow atan2 log abs
    
    and [<CompiledName("FormatLambda")>] formatLambda (expr : MathNet.Symbolics.Expression) (args : Symbol list) : LambdaExpression option =
        let value = function
            | Value.Approximation a -> Some (Expression.Constant a.RealValue :> Expression)
            | Value.NegativeInfinity -> Some (Expression.Constant System.Double.NegativeInfinity :> Expression)
            | Value.PositiveInfinity -> Some (Expression.Constant System.Double.PositiveInfinity :> Expression)
            | Value.Number n -> Some (Expression.Constant (float n) :> Expression)
            | _ -> None
        let constant = function
            | E -> Some (Expression.Constant Constants.E :> Expression)
            | Pi -> Some (Expression.Constant Constants.Pi :> Expression)
            | _ -> None
        let valueType = typeof<float>
        let mathType = typeof<System.Math>
        let add a b = Expression.Add(a, b) :> Expression
        let mul = sharedMul
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

        let div a b = Expression.Divide(a, b) :> Expression
        let mathCall1 (name : string) (a : Expression) = Expression.Call(mathType.GetMethod(name, [| valueType |]), a) :> Expression
        let mathCall2 (name : string) (a : Expression) (b : Expression) = Expression.Call(mathType.GetMethod(name, [| valueType; valueType |]), a, b) :> Expression
        let pow = mathCall2 "Pow"
        let atan2 = mathCall2 "Atan2"
        let log a b = mathCall2 "Log" b a
        let abs = mathCall1 "Abs"
        formatLambdaBase expr args valueType mathType None mathCall2 constant value add mul div pow atan2 log abs

    and [<CompiledName("FormatLambdaBase")>] formatLambdaBase (expr : MathNet.Symbolics.Expression) (args : Symbol list)
            valueType mathType (funcInvokTyp : Type option) mathCall2 constant value add mul div pow atan2 log abs
            : LambdaExpression option =        
        let besselj = mathCall2 "BesselJ"
        let bessely = mathCall2 "BesselY"
        let besseli = mathCall2 "BesselI"
        let besselk = mathCall2 "BesselK"
        let besseliratio = mathCall2 "BesselIRatio"
        let besselkratio = mathCall2 "BesselKRatio"
        let hankelh1 = mathCall2 "HankelH1"
        let hankelh2 = mathCall2 "HankelH2"
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
        let valueType = typeof<complex>
        let mathType = typeof<complex>
        let mathCall1 (name : string) (a : Expression) = Expression.Call(mathType.GetMethod(name, [| valueType |]), a) :> Expression
        let mathCall2 (name : string) (a : Expression) (b : Expression) = Expression.Call(mathType.GetMethod(name, [| valueType; valueType |]), a, b) :> Expression
        let add = mathCall2 "Add"
        let mul = mathCall2 "Multiply"
        let div = mathCall2 "Divide"
        let pow = mathCall2 "Pow"
        let atan2 a b = mathCall1 "Atan" (div a b)
        let log a b =
            let ln = mathCall1 "Log"
            div (ln b) (ln a)
        let abs a = Expression.Convert(mathCall1 "Abs" a, valueType) :> Expression
        formatLambdaBase expr args valueType mathType None mathCall2 constant value add mul div pow atan2 log abs
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

    let compileExpression expr args = Option.map (fun (x : LambdaExpression) -> x.Compile()) (Linq.formatLambda expr args)
    let compileComplexExpression expr args = Option.map (fun (x : LambdaExpression) -> x.Compile()) (Linq.formatComplexLambda expr args)

    let compileExpressionOrThrow expr args =
        let exprv = (Linq.formatLambda expr args).Value
        let cmpl = exprv.Compile()
        cmpl
    let compileExpressionOrThrow2 expr args =
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


        let cmpl = exprv.Compile()
        exprv, cmpl
    let compileComplexExpressionOrThrow expr args = (Linq.formatComplexLambda expr args).Value.Compile()

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
        let fArray, shapeReversed = listOf2Obj (wt0, [])
        dsharp.view ((dsharp.tensor fArray), shapeReversed |> Seq.rev)

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
        | Real x, WTensor (DSTensor t) -> WTensor (DSTensor (x * t))
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

    

    [<CompiledName("Evaluate")>]
    let rec evaluate (symbols:IDictionary<string, FloatingPoint>) = function
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
            match symbols.TryGetValue s with
            | true, a -> a |> fnormalize
            | _ -> failwithf  "Failed to find symbol %s" s
        | Argument (Symbol s) -> failwithf  "Cannot evaluate a argument %s" s
        | Sum xs -> xs |> List.map (evaluate symbols) |> List.reduce fadd |> fnormalize
        | Product xs ->
            let evall = xs |> List.map (evaluate symbols)
            let reducel = evall |> List.reduce fmultiply
            reducel |> fnormalize
        | Power (r, p) -> fpower (evaluate symbols r) (evaluate symbols p) |> fnormalize
        | Function (f, x) -> fapply f (evaluate symbols x) |> fnormalize
        | FunctionN (f, xs) -> xs |> List.map (evaluate symbols) |> fapplyN f |> fnormalize
        | FunInvocation (Symbol fnm, xs) ->
            let cal_param_obj_val () =
                xs
                |> List.map (fun exp ->
                    evaluate symbols exp |> box//formatValueLambda 吃 value 傳入值
                    //match evaluate symbols exp with
                    //| (Real v) -> box v
                    //| WTensor (DSTensor t) ->
                    //    box t
                    //| _ -> null
                )
                |> Array.ofList
            let cal_param_real_val () =
                xs
                |> List.map (fun exp ->
                    match evaluate symbols exp with
                    | (FloatingPoint.Real v) -> v
                    | _ -> Double.NaN
                )
                |> Array.ofList
            let cal_param_vec_val () =
                xs
                |> List.map (fun exp ->
                    match evaluate symbols exp with
                    | (RealVector v) -> v
                    | _ -> failwithf "vector parameter is required for %s" fnm
                )
                |> Array.ofList
            let cal_param_mat_vec_val () =
                xs
                |> List.map (fun exp ->
                    match evaluate symbols exp with
                    | (FloatingPoint.RealVector v) -> FloatingPoint.RealVector v
                    | (FloatingPoint.RealMatrix v) -> FloatingPoint.RealMatrix v
                    | _ -> failwithf "vector parameter is required for %s" fnm
                )
                |> Array.ofList

            let cal_param_list_of_vec_val () : TensorWrapper list =
                xs
                |> List.map (fun exp ->
                    let evalrst = evaluate symbols exp
                    match evalrst with
                    | (FloatingPoint.RealVector v) ->
                        VecInTensor v //計算結果WTensor                    
                    | (FloatingPoint.WTensor tw) ->  tw
                    | _ -> failwithf "vector or WTensor parameter is required for %s" fnm
                )

            if keyWord.ContainsKey fnm then
                let mbr () =
                    let param_val = cal_param_vec_val ()
                    let m2 = DenseMatrix.zero<float> (param_val.Length) (param_val.[0].Count)
                    param_val
                    |> Array.iteri (fun i v ->
                        m2.SetRow(i, v)
                    )
                    m2
                match fnm with
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
                    let param_val = cal_param_list_of_vec_val ()
                    if param_val.Length <> 1 then                        
                        failwithf "htensor only takes single list_of expression as input"
                    WTensor (DSTensor <| listOf2DSTensor param_val.[0])
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
                            | _ ->
                                failwithf "orz 0003"
                        | _ ->
                            failwithf "orz 0004"
                    ) param_val.[0]
                | _ ->
                    failwithf "omg fnm!!!"
            else
                match funDict.[fnm] with
                | DTExp (param, fx) ->
                    let param_val = cal_param_obj_val ()
                    let rec analysisFx (fxExpr:MathNet.Symbolics.Expression) =
                        match fxExpr with
                        | FunInvocation ((Symbol sb), _) when funDict.ContainsKey sb ->
                            match funDict.[sb] with
                            | DTExp (param2, fx2) -> analysisFx fx2
                            | _ ->
                                Choice2Of2 fxExpr
                        | FunInvocation _ ->
                            Choice2Of2 fxExpr
                        | _ -> Choice1Of2 fxExpr
                    let fx_real = analysisFx fx
                    match fx_real with
                    | Choice1Of2 frv ->
                        let expr, cmpl = Compile.compileExpressionOrThrow2 frv param
                        //let corrected_expr =
                        //    expr.Parameters
                        //    |> Seq.fold (fun s a ->
                        //        (Linq.replaceType a.Name s) :?> LambdaExpression
                        //    ) expr
                        let rst = cmpl.DynamicInvoke(param_val:obj[])
                        match rst with
                        | :? float as f -> f |> Real
                        | :? Vector<float> as v -> v |> RealVector
                        | :? Matrix<float> as v -> v |> RealMatrix
                        | :? Tensor as t -> WTensor (DSTensor t)
                        | :? Value as v ->
                            match v with
                            | MathNet.Symbolics.Value.Approximation r ->
                                match r with
                                | Approximation.Real rr ->
                                    rr |> Real
                            | MathNet.Symbolics.Value.DSTen dt ->
                                WTensor (DSTensor dt)
                        | _ ->
                                failwithf "orz 0005"
                    | Choice2Of2 frv ->
                        evaluate symbols frv
                | DTFunI1toI1 f ->
                    let param_val = cal_param_real_val ()
                    f (int param_val.[0]) |> float |> Real
                | DTFunF2toV1 f ->
                    let param_val = cal_param_real_val ()
                    f param_val.[0] param_val.[1] |> RealVector
                | DTCurF2toV1 (f, (Symbol sym)) ->
                    let param_val = cal_param_real_val ()
                    let cur = symbols.[sym].RealValue
                    f cur param_val.[0] param_val.[1] |> RealVector
                | DTCurF3toV1 (f, (Symbol sym)) ->
                    let param_val = cal_param_real_val ()
                    let cur = symbols.[sym].RealValue
                    f cur param_val.[0] param_val.[1] param_val.[2] |> RealVector

    Linq.ExprHelper.evaluate <- evaluate
