namespace MathNet.Symbolics

open System
open MathNet.Numerics
open MathNet.Numerics.LinearAlgebra
open FAkka.Microsoft.FSharp.Core
open LeveledPrintf
#if TENSOR_SUPPORT
open DiffSharp
#endif

type BigInteger = System.Numerics.BigInteger


[<RequireQualifiedAccess>]
type Value =
    | Number of BigRational
    | Approximation of Approximation
    | ComplexInfinity
    | PositiveInfinity
    | NegativeInfinity
    | Undefined
    | RealVec of Vector<float>
    | ComplexVec of Vector<complex>
    | RealMat of Matrix<float>
    | ComplexMat of Matrix<complex>
    | Empty
#if TENSOR_SUPPORT
    | DSTen of Tensor
#endif
    with 
        static member (+) (vl : Value, vr : Value) =
#if DEBUG
            frintf PRINTLEVEL.PTRACE "%A + %A => " vl vr
#endif
            match vl with
            | Number vlv ->
                match vr with
                | Number vrv ->
#if DEBUG
                    frintfn PRINTLEVEL.PTRACE "%A" <| Number (vlv * vrv)
#endif
                    Number (vlv * vrv)
            | RealVec vlv ->
                match vr with
                | Approximation (Real vrv) ->
#if DEBUG
                    frintfn PRINTLEVEL.PTRACE "%A" <| RealVec (vlv + vrv)
#endif
                    RealVec (vlv + vrv)
                | RealVec vrv ->
#if DEBUG
                    frintfn PRINTLEVEL.PTRACE "%A" <| RealVec (vlv + vrv)
#endif
                    RealVec (vlv + vrv)
            | Approximation (Real vlv) ->
                match vr with
                | Approximation (Real vrv) ->
#if DEBUG
                    frintfn PRINTLEVEL.PTRACE "%A" <| Approximation (Real (vlv + vrv))
#endif
                    Approximation (Real (vlv + vrv))
                | RealVec vrv ->
#if DEBUG
                    frintfn PRINTLEVEL.PTRACE "%A" <| RealVec (vrv + vlv)
#endif
                    RealVec (vrv + vlv)
#if TENSOR_SUPPORT
                | DSTen dt ->
#if DEBUG
                    frintfn PRINTLEVEL.PTRACE "%A" <| DSTen (vlv + dt)
#endif
                    DSTen (vlv + dt)
#endif
        static member (*) (vl : Value, vr : float) =
#if DEBUG
            frintf PRINTLEVEL.PTRACE "%A * %A => " vl vr
#endif
            match vl with
            | Approximation (Real vlv) ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Approximation (Real (vlv * vr))
#endif
                Approximation (Real (vlv * vr))
            | RealVec lv ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| RealVec (lv * vr)
#endif
                RealVec (lv * vr)
        static member (*) (vl : float, vr : Value) =
#if DEBUG
            frintf PRINTLEVEL.PTRACE "%A * %A => " vl vr
#endif
            match vr with
            | Approximation (Real vrv) ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Approximation (Real (vl * vrv)) 
#endif
                Approximation (Real (vl * vrv))
            | RealVec rv ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| RealVec (rv * vl)
#endif
                RealVec (rv * vl)
        static member (+) (vl : Value, vr : float) =
#if DEBUG
            frintf PRINTLEVEL.PTRACE "%A + %A => " vl vr
#endif
            match vl with
            | Approximation (Real vlv) ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Approximation (Real (vlv + vr))
#endif
                Approximation (Real (vlv + vr))
            | RealVec vlv ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| RealVec (vlv + vr)
#endif
                RealVec (vlv + vr)
#if TENSOR_SUPPORT
            | DSTen dt ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| DSTen (vr + dt)
#endif
                DSTen (vr + dt)
#endif
        static member (+) (vl : float, vr : Value) =
#if DEBUG
            frintf PRINTLEVEL.PTRACE "%A + %A => " vl vr
#endif
            match vr with
            | Approximation vrv ->
                match vrv with
                | Approximation.Real vrvv ->
#if DEBUG
                    frintfn PRINTLEVEL.PTRACE "%A" <| Approximation (Real (vl + vrvv))
#endif
                    Approximation (Real (vl + vrvv))
            | RealVec rv ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| RealVec (rv + vl)
#endif
                RealVec (rv + vl)
#if TENSOR_SUPPORT
            | DSTen dt ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| DSTen (vl + dt)
#endif
                DSTen (vl + dt)
#endif

        static member (.*) (a: Value, b: Value) =
#if DEBUG
            frintf PRINTLEVEL.PTRACE "%A * %A => " a b
#endif
            match a, b with
            | Value.RealVec x, Value.RealVec y ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Value.RealVec (x.PointwiseMultiply y)
#endif
                Value.RealVec (x.PointwiseMultiply y)
            | _ ->
                failwithf "PointwiseMultiply not supported for these:\r\na: %A\r\nb: %A" a b

        static member (*) (a: Value, b: Value) =
#if DEBUG
            frintf PRINTLEVEL.PTRACE "%A * %A => " a b
#endif
            match a, b with
            | Value.Approximation (Complex c), Value.Approximation y ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Value.Approximation (Complex (c * y.ComplexValue))
#endif
                Value.Approximation (Complex (c * y.ComplexValue))
            | Value.Approximation x, Value.Approximation (Complex c) ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Value.Approximation (Complex (x.ComplexValue * c))
#endif
                Value.Approximation (Complex (x.ComplexValue * c))
            | Value.Approximation (Real x), Value.Approximation (Real y) ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Value.Approximation (Real (x * y))
#endif
                Value.Approximation (Real (x * y))
            | Value.RealVec x, Value.Approximation (Real y) ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Value.RealVec (x * y)
#endif
                Value.RealVec (x * y)
            | Value.Approximation (Real x), Value.RealVec y ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Value.RealVec (x * y)
#endif
                Value.RealVec (x * y)
#if TENSOR_SUPPORT
            | Value.Approximation (Real x), Value.DSTen t ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Value.DSTen (x * t)
#endif
                Value.DSTen (x * t)
            | Value.DSTen t, Value.Approximation (Real x) ->
#if DEBUG
                frintfn PRINTLEVEL.PTRACE "%A" <| Value.DSTen (t * x)
#endif
                Value.DSTen (t * x)
#endif
            | _ ->
                failwithf "Multiply not supported for these:\r\na: %A\r\nb: %A" a b


[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Value =

    let fromDouble (x:float) =
        if Double.IsPositiveInfinity x then Value.PositiveInfinity
        elif Double.IsNegativeInfinity x then Value.NegativeInfinity
        elif Double.IsNaN x then Value.Undefined
        else Value.Approximation (Approximation.fromDouble x)

    let fromSingle (x:float32) =
        if Single.IsPositiveInfinity x then Value.PositiveInfinity
        elif Single.IsNegativeInfinity x then Value.NegativeInfinity
        elif Single.IsNaN x then Value.Undefined
        else Value.Approximation (Approximation.fromSingle x)

    let fromComplex (x:complex) =
        if x.IsReal() then fromDouble x.Real
        elif x.IsInfinity() then Value.ComplexInfinity
        elif x.IsNaN() then Value.Undefined
        else Value.Approximation (Approximation.fromComplex x)

    let fromComplex32 (x:complex32) =
        if x.IsReal() then fromSingle x.Real
        elif x.IsInfinity() then Value.ComplexInfinity
        elif x.IsNaN() then Value.Undefined
        else Value.Approximation (Approximation.fromComplex32 x)

    let approx = function
        | Real d -> fromDouble d
        | Complex c -> fromComplex c

    let zero = Value.Number (BigRational.Zero)
    let one = Value.Number (BigRational.One)

    let (|Zero|_|) = function
        | Value.Number n when n.IsZero -> Some Zero
        | _ -> None

    let (|One|_|) = function
        | Value.Number n when n.IsOne -> Some One
        | _ -> None

    let (|MinusOne|_|) = function
        | Value.Number n when n.IsInteger && n.Numerator = BigInteger.MinusOne -> Some MinusOne
        | _ -> None

    let (|Positive|_|) = function
        | Value.Number n when n.IsPositive -> Some Positive
        | Value.Approximation x when Approximation.isPositive x -> Some Positive
        | Value.PositiveInfinity -> Some Positive
        | _ -> None

    let (|Negative|_|) = function
        | Value.Number n when n.IsNegative -> Some Negative
        | Value.Approximation x when Approximation.isNegative x -> Some Negative
        | Value.NegativeInfinity -> Some Negative
        | _ -> None

    let isZero = function | Zero -> true | _ -> false
    let isOne = function | One -> true | _ -> false
    let isMinusOne = function | MinusOne -> true | _ -> false
    let isPositive = function | Positive -> true | _ -> false
    let isNegative = function | Negative -> true | _ -> false

    let negate = function
        | Value.Number a -> Value.Number (-a)
        | Value.Approximation a -> Approximation.negate a |> approx
        | Value.NegativeInfinity -> Value.PositiveInfinity
        | Value.PositiveInfinity -> Value.NegativeInfinity
        | Value.ComplexInfinity -> Value.ComplexInfinity
        | Value.Undefined -> Value.Undefined

    let abs = function
        | Value.Number a when a.IsNegative -> Value.Number (-a)
        | Value.Number _ as x -> x
        | Value.Approximation a -> Approximation.abs a |> approx
        | Value.NegativeInfinity | Value.PositiveInfinity | Value.ComplexInfinity -> Value.PositiveInfinity
        | Value.Undefined -> Value.Undefined

    let sum = function
        | Value.Undefined, _ | _, Value.Undefined -> Value.Undefined
        | Zero, b | b, Zero -> b
        | Value.Number a, Value.Number b -> Value.Number (a + b)
        | Value.Approximation a, Value.Approximation b -> Approximation.sum (a, b) |> approx
        | Value.Number a, Value.Approximation b | Value.Approximation b, Value.Number a -> Approximation.sum (Approximation.fromRational a, b) |> approx
        | Value.ComplexInfinity, (Value.ComplexInfinity | Value.PositiveInfinity | Value.NegativeInfinity) -> Value.Undefined
        | (Value.ComplexInfinity | Value.PositiveInfinity | Value.NegativeInfinity),  Value.ComplexInfinity -> Value.Undefined
        | Value.ComplexInfinity, _ | _, Value.ComplexInfinity -> Value.ComplexInfinity
        | Value.PositiveInfinity, Value.PositiveInfinity -> Value.PositiveInfinity
        | Value.PositiveInfinity, Value.NegativeInfinity | Value.NegativeInfinity, Value.PositiveInfinity -> Value.Undefined
        | Value.PositiveInfinity, _ | _, Value.PositiveInfinity -> Value.PositiveInfinity
        | Value.NegativeInfinity, Value.NegativeInfinity -> Value.NegativeInfinity
        | Value.NegativeInfinity, _ | _, Value.NegativeInfinity -> Value.NegativeInfinity

    let product = function
        | Value.Undefined, _ | _, Value.Undefined -> Value.Undefined
        | One, b | b, One -> b
        | Zero, (Value.ComplexInfinity | Value.PositiveInfinity | Value.NegativeInfinity) -> Value.Undefined
        | (Value.ComplexInfinity | Value.PositiveInfinity | Value.NegativeInfinity), Zero -> Value.Undefined
        | Zero, _ | _, Zero -> zero
        | Value.Number a, Value.Number b -> Value.Number (a * b)
        | Value.Approximation a, Value.Approximation b -> Approximation.product (a, b) |> approx
        | Value.Number a, Value.Approximation b | Value.Approximation b, Value.Number a -> Approximation.product (Approximation.fromRational a, b) |> approx
        | Value.ComplexInfinity, _ | _, Value.ComplexInfinity -> Value.ComplexInfinity
        | Value.PositiveInfinity, Positive | Positive, Value.PositiveInfinity -> Value.PositiveInfinity
        | Value.PositiveInfinity, Negative | Negative, Value.PositiveInfinity -> Value.NegativeInfinity
        | Value.NegativeInfinity, Positive | Positive, Value.NegativeInfinity -> Value.NegativeInfinity
        | Value.NegativeInfinity, Negative | Negative, Value.NegativeInfinity -> Value.PositiveInfinity
        | Value.NegativeInfinity, _ | _, Value.NegativeInfinity -> Value.NegativeInfinity
        | Value.PositiveInfinity, _ | _, Value.PositiveInfinity -> Value.PositiveInfinity

    let invert = function
        | Zero -> Value.ComplexInfinity
        | Value.Number a -> Value.Number (BigRational.Reciprocal a)
        | Value.Approximation a -> Approximation.invert a |> approx
        | Value.ComplexInfinity | Value.PositiveInfinity | Value.NegativeInfinity -> zero
        | Value.Undefined -> Value.Undefined

    let power = function
        | Value.Undefined, _ | _, Value.Undefined -> Value.Undefined
        | Zero, Zero -> Value.Undefined
        | Zero, (Value.ComplexInfinity | Value.PositiveInfinity) -> zero
        | Zero, Value.NegativeInfinity -> Value.ComplexInfinity
        | Zero, Positive -> zero
        | Zero, Negative -> Value.ComplexInfinity
        | (Value.ComplexInfinity | Value.PositiveInfinity | Value.NegativeInfinity), Zero -> Value.Undefined
        | (Value.ComplexInfinity | Value.PositiveInfinity | Value.NegativeInfinity), Value.PositiveInfinity -> Value.ComplexInfinity
        | (Value.ComplexInfinity | Value.PositiveInfinity | Value.NegativeInfinity), Value.Number b when b.IsNegative -> zero
        | Value.ComplexInfinity, Positive -> Value.ComplexInfinity
        | Value.PositiveInfinity, Positive -> Value.PositiveInfinity
        | Value.NegativeInfinity, Value.Number b when b.IsPositive && b.IsInteger ->
            if (b.Numerator % 2I).IsZero then Value.PositiveInfinity else Value.NegativeInfinity
        | One, (Value.ComplexInfinity | Value.PositiveInfinity | Value.NegativeInfinity) | MinusOne, (Value.ComplexInfinity | Value.PositiveInfinity | Value.NegativeInfinity) -> Value.Undefined
        | One, _ | _, Zero -> one
        | _, Zero -> one
        | a, One -> a
        | One, _ -> one
        | Positive, Value.PositiveInfinity -> Value.PositiveInfinity
        | Negative, Value.PositiveInfinity -> Value.ComplexInfinity
        | _, Value.NegativeInfinity -> zero
        | _, Value.ComplexInfinity -> Value.Undefined
        | Value.Number a, Value.Number b when b.IsInteger ->
            if b.IsNegative then
                if a.IsZero then Value.ComplexInfinity
                // workaround bug in BigRational with negative powers - drop after upgrading to > v3.0.0-alpha9
                else Value.Number (BigRational.Pow(BigRational.Reciprocal a, -int(b.Numerator)))
            else Value.Number (BigRational.Pow(a, int(b.Numerator)))
        | Value.Approximation a, Value.Approximation b -> Approximation.pow (a, b) |> approx
        | Value.Number a, Value.Number b -> Approximation.pow (Approximation.fromRational a, Approximation.fromRational b) |> approx
        | Value.Approximation a, Value.Number b -> Approximation.pow (a, Approximation.fromRational b) |> approx
        | Value.Number a, Value.Approximation b -> Approximation.pow (Approximation.fromRational a, b) |> approx
        | _ -> Value.Undefined // TODO

    let apply f = function
        | Value.Approximation a -> Approximation.apply f a |> approx
        | Value.Number a -> Approximation.fromRational a |> Approximation.apply f |> approx
        | Value.Undefined _ -> Value.Undefined
        | Value.ComplexInfinity -> Value.Undefined // TODO
        | Value.PositiveInfinity -> Value.Undefined // TODO
        | Value.NegativeInfinity -> Value.Undefined // TODO

