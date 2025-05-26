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
open System
//open PersistedConcurrentSortedList
//open Deedle
open System.Runtime.InteropServices
open System.Runtime.CompilerServices



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

    let matmulFoldHandler s a =
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
                    |> Array.fold matmulFoldHandler param_val.[0]
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


    [<Extension>]
    type SpecializedCD =
        [<Extension>]
        static member TryAdds (cd:ConcurrentDictionary<string, FloatingPoint>, added: (string * FloatingPoint) seq) =
            added
            |> Seq.iter (fun (k, v) ->
                cd.TryAdd(k, v) |> ignore
            )

    let scopeCtxNewC p = NamedContext.New(p, None) |> Context 
    let scopeCtxC p c = NamedContext.New(p, Some c) |> Context
    let scopeCtxNew p = NamedContext.New(p, None) //|> Context 
    let scopeCtx p c = NamedContext.New(p, Some c) //|> Context

    let scopeId () =
#if NET9_0_OR_GREATER
        System.Guid.CreateVersion7()
#else   
        System.Guid.NewGuid()
#endif

    let rec nestedFxHandler
        (symbolValues_: SymbolValues)
        (sysVarValueStack_:Stack)
        (fd_:FunDict)
        (sid:Guid option)
        (eval: Guid option -> SymbolValues -> Stack -> (MathNet.Symbolics.Expression -> FloatingPoint))
        (sl: Symbol list) //fxExpr 中 sl 的變數需要
        (fxExpr: MathNet.Symbolics.Expression)
        : (Symbol list) * (MathNet.Symbolics.Expression) =
    
        let reNestedFxHandle = nestedFxHandler symbolValues_ sysVarValueStack_ fd_ sid eval
    
        let exprMap sl_ (exprs:MathNet.Symbolics.Expression list) =
            exprs
            |> List.fold (fun (symL, uExprs) expr ->
                let usl, uExpr = reNestedFxHandle symL expr //symbolValues_ sysVarValueStack_ //None
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
                let updatedSL, uExpr = reNestedFxHandle sl_ baseExpr //None
                let updatedSL2, uExpExpr = reNestedFxHandle updatedSL expExpr //None
                updatedSL2, Power (uExpr, uExpExpr)
            | Function (func, arg) ->
                let updatedSL, uExpr = reNestedFxHandle sl_ arg //symbolValues_ sysVarValueStack_ //None
                updatedSL, Function (func, uExpr)
            | FunctionN (func, args) ->
                let updatedSL, uExprs = exprMap sl_ args
                updatedSL, FunctionN (func, uExprs)
            | _ ->
                sl_, expr
    
        let r = 
            match fxExpr with
            | FunInvocation ((Symbol sb), origParamExp) when fd_.ContainsKey sb ->
                let evaluatedValue =
                    origParamExp
                    |> List.map (fun param ->
                        let newSymbolName = $"__{sb}_{Guid.NewGuid().ToString()}__"
                        let newSymbol = Symbol newSymbolName
                        let paramValue = eval sid symbolValues_ sysVarValueStack_ param
                        symbolValues_.TryAdd(newSymbolName, paramValue) |> ignore
                        Identifier newSymbol
                    )
            
            
    
                let newSymbolNameAggRst = $"__{sb}_{Guid.NewGuid().ToString()}__"
                let newSymbolAggRst = Symbol newSymbolNameAggRst
            
                let evaluatedFunValue = eval sid symbolValues_ sysVarValueStack_ (FunInvocation ((Symbol sb), evaluatedValue))
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
    
        r


    [<CompiledName("Evaluate2")>]
    let rec evaluate2 (
            parentScopeIdOpt: Guid option
            , gContext: GlobalContext //Evaluation 共享 (user 宣告之變數值)
            , sContext: ScopedContext //DTProc 共享 (user 宣告之變數值)
            , symbolValues:SymbolValues //PassedIn
            , sysVarValueStack:Stack //參數位置 expr 的 evaluation result -->  SymbolicExpression 參數以及 FuncInvocation 專用
            //, postFunOpt: (unit -> unit) option
    ) =
        //let pop () = sysVarValueStack.TryPop () |> ignore
        let getStackValue s =
            if sysVarValueStack.IsSome then
                match sysVarValueStack.Value.TryGetValue s with
                | true, a -> a |> fnormalize |> Some
                | _ -> None
            else
                None
        let getPassedInSymbolValue s =
            match symbolValues.TryGetValue s with
            | true, a -> a |> fnormalize
            | _ ->
                failwithf  "Failed to find symbol %s" s

        let getScopedContextValue s =
            if sContext.IsNone then
                None
            else
                match sContext.Value.ctx.TryGetValue s with
                | true, a -> a |> fnormalize |> Some
                | _ ->
                    None

        let getGlobalContextValue s =
            match gContext.ctx.TryGetValue s with
            | true, a -> a |> fnormalize |> Some
            | _ ->
                None

        let getValue s =
            match getStackValue s with
            | Some v -> v
            | None ->
                match getScopedContextValue s with
                | Some v -> v
                | None ->
                    match getGlobalContextValue s with
                    | Some v -> v
                    | None ->
                        getPassedInSymbolValue s

        let reEvaluate v = evaluate2 (parentScopeIdOpt, gContext, sContext, symbolValues, sysVarValueStack) v
        let reEvaluate1 sysVarValueStack_ = evaluate2 (parentScopeIdOpt, gContext, sContext, symbolValues, sysVarValueStack_)
        let reEvaluate2 symbolValues_ sysVarValueStack_ = evaluate2 (parentScopeIdOpt, gContext, sContext, symbolValues_, sysVarValueStack_)
        let reEvaluate3 parentScopeIdOpt_ symbolValues_ sysVarValueStack_ = evaluate2 (parentScopeIdOpt_, gContext, sContext, symbolValues_, sysVarValueStack_)

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
        | Identifier (Symbol s) -> getValue s
        | Argument (Symbol s) -> failwithf  "Cannot evaluate an argument %s" s
        | Sum xs -> xs |> List.map reEvaluate |> List.reduce fadd |> fnormalize
        | Product xs ->
            let evall = xs |> List.map reEvaluate
            let reducel = evall |> List.reduce fmultiply
            reducel |> fnormalize
        | PointwiseMul (l, r) ->
                let lv = reEvaluate l
                let rv = reEvaluate r
                try
                    lv .* rv
                with ex ->
                    failwithf "PointwiseMul evaluation failed:\nLeft = %A\nRight = %A\nError = %s" lv rv ex.Message
        | Power (r, p) -> fpower (reEvaluate r) (reEvaluate p) |> fnormalize
        | Function (f, x) -> fapply f (reEvaluate x) |> fnormalize
        | FunctionN (f, xs) -> xs |> List.map reEvaluate |> fapplyN f |> fnormalize
        | FunInvocation (Symbol parentFxName, paramValueExprList) ->
            let cal_param_fd_val () = paramValueExprList |> List.map reEvaluate

            let cal_param_obj_val () =
                paramValueExprList
                |> List.map (reEvaluate >> box)
                |> List.toArray

            let cal_param_real_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    match reEvaluate paramValueExpr with
                    | (FloatingPoint.Real v) -> v
                    | (FloatingPoint.Int v) -> float v
                    | (FloatingPoint.Decimal v) -> float v
                    | _ -> Double.NaN
                )
                |> Array.ofList
            let cal_param_vec_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    match reEvaluate paramValueExpr with
                    | (RealVector v) -> v
                    | _ -> failwithf "vector parameter is required for %s" parentFxName
                )
                |> Array.ofList
            let cal_param_mat_vec_val () =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    match reEvaluate paramValueExpr with
                    | (FloatingPoint.RealVector v) -> FloatingPoint.RealVector v
                    | (FloatingPoint.RealMatrix v) -> FloatingPoint.RealMatrix v
                    | _ -> failwithf "vector parameter is required for %s" parentFxName
                )
                |> Array.ofList

            let cal_param_list_of_vec_val () : TensorWrapper list =
                paramValueExprList
                |> List.map (fun paramValueExpr ->
                    let evalrst = reEvaluate paramValueExpr
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
                        | Number n ->
                            Str (BigRational.ToDouble(n).ToString())
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
                        |> Array.fold matmulFoldHandler param_val.[0]

                    | "expr"
                    | "param" ->
                        NestedExpr paramValueExprList
                    | _ ->
                        failwithf $"omg fnm {parentFxName}!!!"
                f ()
            else

                let sid = Some (scopeId ())
                let sCtxFF = scopeCtxNew parentScopeIdOpt 
                let fd = (getValue "funDict").funDict



                let exprsInFuncParamEvaluation (symbols:Symbol list) (exprs:MathNet.Symbolics.Expression list) skip =
                    symbols
                    |> Seq.skip skip
                    |> Seq.mapi (fun i sb ->
                        sb.SymbolName, reEvaluate exprs[i + skip]
                    )


                let r = 
                    match fd.[parentFxName] with
                    //       x1, y1    dup0(paramValueExprList)
                    | DTExp (parentFxParamSymbols, parentFxBody) ->
                        if parentFxParamSymbols.Length <> paramValueExprList.Length then
                            failwithf "%s parameter length not matched %A <-> %A" parentFxName parentFxParamSymbols paramValueExprList

                        let evaluatedArgsOfParentCall = exprsInFuncParamEvaluation parentFxParamSymbols paramValueExprList 0
                        //sysVarValueStack.Push (Some (ConcurrentDictionary<_, _> (dict evaluatedArgsOfParentCall)))
                        let updatedStack = dict evaluatedArgsOfParentCall |> CD<_, _> |> Some

                        match parentFxBody with
                        | Identifier aSymbol ->
                            symbolValues[aSymbol.SymbolName]
                        | FunInvocation _ ->                       
                            
                            reEvaluate3 sid symbolValues updatedStack parentFxBody
                            //evaluate2 (symbolValues, sysVarValueStack, (Some (fun () -> sysVarValueStack.TryPop() |> ignore))) parentFxBody
                        | _ ->
                            let uSL, frv = nestedFxHandler symbolValues updatedStack fd sid reEvaluate3 parentFxParamSymbols parentFxBody
                            let rFrv, rUSl = renameSymbols (uSL, frv) //20250413 symbol 名稱統一化後，快取才有意義

                            let expr, cmpl = Compile.compileExpressionOrThrow2 rFrv rUSl
                            let param_val = cal_param_obj_val ()
                        
                            let rst =
                                cmpl.DynamicInvoke(
                                    //20250413 symbol 名稱統一化後，取值仍需要用原先的變數名，所以上面的 uSL 不能少
                                    Array.append param_val (uSL |> List.skip parentFxParamSymbols.Length |> List.map (fun s -> box symbolValues[s.SymbolName]) |> List.toArray)
                                )
                            obj2FloatPoint rst

                    | DTProc (procList, skip) -> //超級重要一點：在 Proc 內部是不會知曉 evaluate 時候的 symbol values 的！(只能是是 param 傳進 expr)
                        let procStepId () = System.Guid.NewGuid()
                        
                        let rec evalProc
                            (procList_: ((Symbol list) * DefBody) list)
                            (prevOutputOpt: FloatingPoint option)
                            (scopedContextOpt: ScopedContext)
                            (stack: Stack) //針對這個函數而言，stack 就是<外部傳入的 param expr list> evaluate後的結果
                            (paramValueExprListOpt: MathNet.Symbolics.Expression list option (*第0層非空*))
                            //(ifTopInProc:bool)
                            (procStepId_:Guid)
                            =
                            match procList_ with
                            | [] ->
                                //pop()
                                // 所有過程處理完畢，返回最後的輸出
                                prevOutputOpt.Value
                            | (paramSymbols, defBody) :: restProcList ->
                                let updatedStack : Stack =
                                    if paramValueExprListOpt.IsSome then
                                        //頂層函數吃到的表達式傳入
                                        let paramValueExprList_ = paramValueExprListOpt.Value
                                        let evaluatedArgsOfParentCall = exprsInFuncParamEvaluation paramSymbols paramValueExprList_ skip //ifTop
                                        evaluatedArgsOfParentCall
                                        |> Seq.append (seq["stepId", Str (procStepId_.ToString())])
                                        |> dict
                                        |> CD<_, _>
                                        |> Some
                                    else
                                        stack
                                        ////第一層 defBody 輸出綁 第二層 paramSymbols
                                        //let input = 
                                        //    if paramSymbols.Length > 1 then
                                        //        match prevOutputOpt.Value with
                                        //        | (NestedList l) ->
                                        //            l
                                        //        | (NestedExpr l) ->
                                        //            failwith "尚未實作輸出為 Expr list 的部分"
                                        //        | _ ->
                                        //            failwith "輸出輸入不匹配"
                                        //    elif paramSymbols.Length = 1 then
                                        //        [prevOutputOpt.Value]
                                        //    else
                                        //        []
                                        //    |> fun outFPList ->
                                        //        ((paramSymbols |> List.map (fun s -> s.SymbolName)), outFPList)
                                        //        ||> List.zip
                                        //input
                                    //|> Seq.append (seq["stepId", Str procStepId_.ToString()])
                                    //|> fun s ->
                                    //    //if ifTop then
                                    //    //    sctx.TryAdds s
                                    //    //else
                                    //        dict s
                                    //        |> ConcurrentDictionary<_, _>
                                    //        //|> scopeCtx parentScopeIdOpt 
                                    //        |> Some

                    
                                let rst =
                                    match defBody with
                                    | DBFun (almightFun, defOut) ->
                                        let sv = almightFun gContext sContext prevOutputOpt updatedStack paramValueExprListOpt (sysVarValueStack.IsNone)
                                        if sContext.IsSome then
                                            sContext.Value.ctx["it"] <- sv
                                        match defOut with
                                        | OutCtx ->
                                            Context sContext.Value
                                        | OutFP ->
                                            sv
                                        | OutVar vl ->
                                            vl |> List.map (fun s -> getValue s.SymbolName) |> NestedList
                                    | DBExp (exprList, defOut) ->
                                        //failwith "haven't yet impl"
                                        //let scopedSymbolValues = ConcurrentDictionary<string, FloatingPoint> currentScopedContext
                                        //scopedSymbolValues["global"] <- symbolValues["global"]
                                        let fp, _, sv, _ =
                                            exprList
                                            |> List.fold (fun (s, sid_, symbolValues_, updatedStack_) a ->
                                                let sv = reEvaluate3 sid_ symbolValues_ updatedStack_ a
                                                scopedContextOpt.Value.ctx["it"] <- sv
                                                sv, (Some (procStepId())), symbolValues_, updatedStack_
                                            ) (Undef, None, symbolValues, None)

                                        scopedContextOpt.Value.ctx["it"] <- fp

                                        match defOut with
                                        | OutCtx ->
                                            Context sContext.Value
                                        | OutFP ->
                                            fp
                                        | OutVar vl ->
                                            vl |> List.map (fun s -> getValue s.SymbolName) |> NestedList


                                evalProc restProcList (Some rst) scopedContextOpt updatedStack          None                      (procStepId())

                        let finalOutput =
                                evalProc     procList  None      (Some sCtxFF)    sysVarValueStack     (Some paramValueExprList)   (procStepId())
                        finalOutput
                       
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

                r

    let evaluate2_
        (parentScopeIdOpt: Guid option)
        (gContext: GlobalContext) //Evaluation 共享 (user 宣告之變數值)
        (sContext: ScopedContext)
        (symbolValues:ConcurrentDictionary<string, FloatingPoint>)
        (sysVarValuesStack:Stack) = //ifTop =
        evaluate2 (parentScopeIdOpt, gContext, sContext, symbolValues, sysVarValuesStack) //, None, ifTop)

    

    [<CompiledName("Evaluate")>]
    let rec evaluate (symbolValues_:IDictionary<string, FloatingPoint>) =
        let symbolValues = ConcurrentDictionary<string, FloatingPoint> symbolValues_
        //let globalScope _ = ConcurrentDictionary<string, FloatingPoint>() |> Context //供圖靈機 IO

        let gCtx = scopeCtxNew None
        symbolValues.TryAdd("funDict", FD funDict) |> ignore
        evaluate2 (None, gCtx, None, symbolValues, None)
        


    [<CompiledName("EvaluateCorrect")>]
    let rec evaluate_correct (symbols:IDictionary<string, FloatingPoint>) =
        let symbolValues = ConcurrentDictionary<string, FloatingPoint> symbols
        let globalScope _ = ConcurrentDictionary<string, FloatingPoint>() |> ContextC //供圖靈機 IO
        let curGS = symbolValues.GetOrAdd("global", globalScope)
        match curGS with
        | ContextC _ -> ()
        | _ ->
            failwith "invalid GlobalContext!"
        evaluate2_with_dict_svv (symbolValues, None)


    Linq.ExprHelper.evaluate <- evaluate
