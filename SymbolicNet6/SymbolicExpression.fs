﻿namespace MathNet.Symbolics

open MathNet.Numerics
open MathNet.Symbolics

open Operators

[<RequireQualifiedAccess>]
type SymbolicExpressionType =
    | RationalNumber = 1
    | RealNumber = 2
    | ComplexNumber = 3
    | Variable = 4
    | Sum = 5
    | Product = 6
    | Power = 7
    | Function = 9
    | ComplexInfinity = 10
    | PositiveInfinity = 11
    | NegativeInfinity = 12
    | Undefined = 13

[<ProtoBuf.ProtoContract>]
[<StructuredFormatDisplay("{Expression}")>]
type SymbolicExpression(expression:Expression) =

    let unpack (s:SymbolicExpression) = s.Expression
    let pack (s:Expression) = SymbolicExpression(s)

    let unpackArrayToSet (items:SymbolicExpression array) = System.Collections.Generic.HashSet(items |> Seq.map unpack, HashIdentity.Structural)

    member this.Expression = expression

    member this.Type =
        match expression with
        | Number _ -> SymbolicExpressionType.RationalNumber
        | Approximation (Approximation.Real _) -> SymbolicExpressionType.RealNumber
        | Approximation (Approximation.Complex _) -> SymbolicExpressionType.ComplexNumber
        | Identifier _ -> SymbolicExpressionType.Variable
        | Argument _ -> SymbolicExpressionType.Variable
        | Constant I -> SymbolicExpressionType.ComplexNumber
        | Constant _ -> SymbolicExpressionType.RealNumber
        | Sum _ -> SymbolicExpressionType.Sum
        | PointwiseMul _ | Product _ -> SymbolicExpressionType.Product
        | Power _ -> SymbolicExpressionType.Power
        | FunInvocation _ | Function _ | FunctionN _ -> SymbolicExpressionType.Function
        | ComplexInfinity -> SymbolicExpressionType.ComplexInfinity
        | PositiveInfinity -> SymbolicExpressionType.PositiveInfinity
        | NegativeInfinity -> SymbolicExpressionType.NegativeInfinity
        | Undefined -> SymbolicExpressionType.Undefined

    member this.RationalNumberValue =
        match expression with
        | Number n -> n
        | _ -> failwith "Not a rational number"

    member this.RealNumberValue =
        match expression with
        | Approximation (Approximation.Real fp) -> fp
        | Constant Pi -> Constants.Pi
        | Constant E -> Constants.E
        | Number n -> float n
        | _ -> failwith "Not a real number"

    member this.ComplexNumberValue =
        match expression with
        | Approximation (Approximation.Complex fp) -> fp
        | Approximation (Approximation.Real fp) -> complex fp 0.0
        | Constant I -> Complex.onei
        | Constant Pi -> complex Constants.Pi 0.0
        | Constant E -> complex Constants.E 0.0
        | Number n -> complex (float n) 0.0
        | _ -> failwith "Not a complex number"

    member this.VariableName =
        match expression with
        | Identifier (Symbol s) -> s
        | Argument (Symbol s) -> s
        | _ -> failwith "Not a variable"

    interface System.IComparable with
        member this.CompareTo(otherObj) =
            match otherObj with
            | :? SymbolicExpression as other ->
                compare (this.Expression.ToString()) (other.Expression.ToString())
                //let keyCompare = compare (this._idx.KeysSafe |> Seq.toArray) (other._idx.KeysSafe |> Seq.toArray)
                //if keyCompare = 0 then
                //    compare (this._base.ValuesSafe |> Seq.toArray) (other._base.ValuesSafe |> Seq.toArray)
                //else
                //    keyCompare
            | _ -> invalidArg "otherObj" $"Not a SymbolicExpression"

    // LEAFS - Integer
    static member Zero = SymbolicExpression(zero)
    static member One = SymbolicExpression(one)
    static member Two = SymbolicExpression(two)
    static member MinusOne = SymbolicExpression(minusOne)

    static member Int32(x:int32) = SymbolicExpression(fromInt32 x)
    static member Int64(x:int64) = SymbolicExpression(fromInt64 x)
    static member Integer(x:BigInteger) = SymbolicExpression(fromInteger x)
    static member IntegerFraction(n:BigInteger, d:BigInteger) = SymbolicExpression(fromIntegerFraction n d)
    static member Rational(x:BigRational) = SymbolicExpression(fromRational x)

    static member Decimal(x:decimal) = SymbolicExpression(fromDecimal x)

    // LEAFS - Approximations
    static member Real(approximation:float) = SymbolicExpression(fromDouble approximation)
    static member Real32(approximation:float32) = SymbolicExpression(fromSingle approximation)
    static member Complex(approximation:complex) = SymbolicExpression(fromComplex approximation)
    static member Complex32(approximation:complex32) = SymbolicExpression(fromComplex32 approximation)

    // LEAFS - Constants
    static member I = SymbolicExpression(I)
    static member E = SymbolicExpression(E)
    static member Pi = SymbolicExpression(Pi)

    // LEAFS - Mathematical Symbols
    static member PositiveInfinity = SymbolicExpression(Expression.PositiveInfinity)
    static member NegativeInfinity = SymbolicExpression(Expression.NegativeInfinity)
    static member ComplexInfinity = SymbolicExpression(Expression.ComplexInfinity)
    static member Undefined = SymbolicExpression(Expression.Undefined)

    // LEAFS - Symbols
    static member Variable(name:string) = SymbolicExpression(symbol name)


    // PARSING

    static member Parse(infix:string) : SymbolicExpression =
        SymbolicExpression(Infix.parseOrThrow infix)

    static member XParse(infix:string) : Expression =
        SymbolicExpression(Infix.parseOrThrow infix).Expression

    static member ParseMathML(mathml:string) : SymbolicExpression =
        SymbolicExpression(MathML.parse mathml)

    static member ParseExpression(expression:System.Linq.Expressions.Expression) : SymbolicExpression =
        SymbolicExpression(Linq.parse expression)

    static member ParseQuotation(quotation:Microsoft.FSharp.Quotations.Expr) : SymbolicExpression =
        SymbolicExpression(Quotations.parse quotation)


    // FORMATTING

    override this.ToString() : string =
        Infix.format expression

    member this.ToCustomString(?compactPowersOfFunctions:bool) : string =
        let defaults = Infix.defaultStyle
        Infix.formatStyle
            { CompactPowersOfFunctions = defaultArg compactPowersOfFunctions defaults.CompactPowersOfFunctions }
            expression

    member this.ToLaTeX() : string =
        LaTeX.format expression

    member this.ToCustomLaTeX(?compactPowersOfFunctions:bool) : string =
        let defaults = LaTeX.defaultStyle
        LaTeX.formatStyle
            { CompactPowersOfFunctions = defaultArg compactPowersOfFunctions defaults.CompactPowersOfFunctions }
            expression

    member this.ToMathML() : string =
        MathML.formatContentStrict expression

    member this.ToSemanticMathML() : string =
        MathML.formatSemanticsAnnotated expression


    // EVALUATION

    member this.Evaluate(symbols:System.Collections.Generic.IDictionary<string, FloatingPoint>) = Evaluate.evaluate symbols expression
    member this.EvaluateBase(symbols:System.Collections.Generic.IDictionary<string, FloatingPoint>) = Evaluate.evaluateBase symbols expression
    member this.EvaluateNoThrow(symbols:System.Collections.Generic.IDictionary<string, FloatingPoint>) =
        try
            Evaluate.evaluate symbols expression |> Choice1Of2
        with
        | exn ->
            Choice2Of2 exn.Message
    member this.EvaluateCorrect(symbols:System.Collections.Generic.IDictionary<string, FloatingPoint>) = Evaluate.evaluate_correct symbols expression
 

    // COMPILATION
    member this.Compile ([<System.ParamArray>] args: string array) = Compile.compileExpressionOrThrow expression (args |> Array.map Symbol |> Array.toList)
    member this.Compile (arg:string) = Compile.compileExpression1OrThrow expression (Symbol arg)
    member this.Compile (arg1:string, arg2:string) = Compile.compileExpression2OrThrow expression (Symbol arg1) (Symbol arg2)
    member this.Compile (arg1:string, arg2:string, arg3:string) = Compile.compileExpression3OrThrow expression (Symbol arg1) (Symbol arg2) (Symbol arg3)
    member this.Compile (arg1:string, arg2:string, arg3:string, arg4:string) = Compile.compileExpression4OrThrow expression (Symbol arg1) (Symbol arg2) (Symbol arg3) (Symbol arg4)

    member this.CompileComplex ([<System.ParamArray>] args: string array) = Compile.compileComplexExpressionOrThrow expression (args |> Array.map Symbol |> Array.toList)
    member this.CompileComplex (arg:string) = Compile.compileComplexExpression1OrThrow expression (Symbol arg)
    member this.CompileComplex (arg1:string, arg2:string) = Compile.compileComplexExpression2OrThrow expression (Symbol arg1) (Symbol arg2)
    member this.CompileComplex (arg1:string, arg2:string, arg3:string) = Compile.compileComplexExpression3OrThrow expression (Symbol arg1) (Symbol arg2) (Symbol arg3)
    member this.CompileComplex (arg1:string, arg2:string, arg3:string, arg4:string) = Compile.compileComplexExpression4OrThrow expression (Symbol arg1) (Symbol arg2) (Symbol arg3) (Symbol arg4)


    // CASTING

    static member op_Implicit (x:Expression) : SymbolicExpression = SymbolicExpression(x)
    static member op_Implicit (x:string) : SymbolicExpression = SymbolicExpression.Parse(x)

    static member op_Implicit (x:int32) : SymbolicExpression = SymbolicExpression(fromInt32 x)
    static member op_Implicit (x:int64) : SymbolicExpression = SymbolicExpression(fromInt64 x)
    static member op_Implicit (x:BigInteger) : SymbolicExpression = SymbolicExpression(fromInteger x)
    static member op_Implicit (x:BigRational) : SymbolicExpression = SymbolicExpression(fromRational x)

    static member op_Implicit (x:decimal) : SymbolicExpression = SymbolicExpression(fromDecimal x)

    static member op_Implicit (x:float) : SymbolicExpression = SymbolicExpression(fromDouble x)
    static member op_Implicit (x:float32) : SymbolicExpression = SymbolicExpression(fromSingle x)
    static member op_Implicit (x:complex) : SymbolicExpression = SymbolicExpression(fromComplex x)
    static member op_Implicit (x:complex32) : SymbolicExpression = SymbolicExpression(fromComplex32 x)

    // bad idea, don't do this
    // static member op_Implicit (x:SymbolicExpression) : Expression = x.Expression


    // OPERATORS

    static member ( ~+ ) (x:SymbolicExpression) : SymbolicExpression = SymbolicExpression(+x.Expression)
    static member ( ~- ) (x:SymbolicExpression) : SymbolicExpression = SymbolicExpression(-x.Expression)
    static member ( + ) ((x:SymbolicExpression), (y:SymbolicExpression)) : SymbolicExpression = SymbolicExpression(x.Expression + y.Expression)
    static member ( - ) ((x:SymbolicExpression), (y:SymbolicExpression)) : SymbolicExpression = SymbolicExpression(x.Expression - y.Expression)
    static member ( * ) ((x:SymbolicExpression), (y:SymbolicExpression)) : SymbolicExpression = SymbolicExpression(x.Expression * y.Expression)
    static member ( / ) ((x:SymbolicExpression), (y:SymbolicExpression)) : SymbolicExpression = SymbolicExpression(x.Expression / y.Expression)

    static member Sum([<System.ParamArray>] summands : SymbolicExpression array) = SymbolicExpression(summands |> Seq.map (fun x -> x.Expression) |> sumSeq)
    static member Sum(summands : SymbolicExpression seq) = SymbolicExpression(summands |> Seq.map (fun x -> x.Expression) |> sumSeq)
    static member Product([<System.ParamArray>] factors : SymbolicExpression array) = SymbolicExpression(factors |> Seq.map (fun x -> x.Expression) |> productSeq)
    static member Product(factors : SymbolicExpression seq) = SymbolicExpression(factors |> Seq.map (fun x -> x.Expression) |> productSeq)

    member this.Negate() = -this
    member this.Add(x:SymbolicExpression) = this + x
    member this.Subtract(x:SymbolicExpression) = this - x
    member this.Multiply(x:SymbolicExpression) = this * x
    member this.Divide(x:SymbolicExpression) = this / x

    member this.Pow(power:SymbolicExpression) = SymbolicExpression(Expression.Pow(expression, power.Expression))
    member this.Invert() = SymbolicExpression(invert expression)

    member this.Abs() = SymbolicExpression(abs expression)

    member this.Root(n:SymbolicExpression) = SymbolicExpression(root n.Expression expression)
    member this.Sqrt() = SymbolicExpression(sqrt expression)

    member this.Exp() = SymbolicExpression(exp expression)
    member this.Ln() = SymbolicExpression(ln expression)
    member this.Log() = SymbolicExpression(lg expression)
    member this.Log(basis:SymbolicExpression) = SymbolicExpression(log basis.Expression expression)

    member this.Sin() = SymbolicExpression(sin expression)
    member this.Cos() = SymbolicExpression(cos expression)
    member this.Tan() = SymbolicExpression(tan expression)
    member this.Csc() = SymbolicExpression(csc expression)
    member this.Sec() = SymbolicExpression(sec expression)
    member this.Cot() = SymbolicExpression(cot expression)

    member this.Sinh() = SymbolicExpression(sinh expression)
    member this.Cosh() = SymbolicExpression(cosh expression)
    member this.Tanh() = SymbolicExpression(tanh expression)
    member this.Csch() = SymbolicExpression(csch expression)
    member this.Sech() = SymbolicExpression(sech expression)
    member this.Coth() = SymbolicExpression(coth expression)

    member this.ArcSin() = SymbolicExpression(arcsin expression)
    member this.ArcCos() = SymbolicExpression(arccos expression)
    member this.ArcTan() = SymbolicExpression(arctan expression)
    member this.ArcCsc() = SymbolicExpression(arccsc expression)
    member this.ArcSec() = SymbolicExpression(arcsec expression)
    member this.ArcCot() = SymbolicExpression(arccot expression)

    member this.ArcSinh() = SymbolicExpression(arcsinh expression)
    member this.ArcCosh() = SymbolicExpression(arccosh expression)
    member this.ArcTanh() = SymbolicExpression(arctanh expression)
    member this.ArcCsch() = SymbolicExpression(arccsch expression)
    member this.ArcSech() = SymbolicExpression(arcsech expression)
    member this.ArcCoth() = SymbolicExpression(arccoth expression)

    member this.AiryAi() = SymbolicExpression(airyai expression)
    member this.AiryAiPrime() = SymbolicExpression(airyaiprime expression)
    member this.AiryBi() = SymbolicExpression(airybi expression)
    member this.AiryBiPrime() = SymbolicExpression(airybiprime expression)

    member this.BesselJ(n:SymbolicExpression) = SymbolicExpression(besselj n.Expression expression)
    member this.BesselY(n:SymbolicExpression) = SymbolicExpression(bessely n.Expression expression)
    member this.BesselI(n:SymbolicExpression) = SymbolicExpression(besseli n.Expression expression)
    member this.BesselK(n:SymbolicExpression) = SymbolicExpression(besselk n.Expression expression)
    member this.BesselIRatio(n:SymbolicExpression) = SymbolicExpression(besseliratio n.Expression expression)
    member this.BesselKRatio(n:SymbolicExpression) = SymbolicExpression(besselkratio n.Expression expression)
    member this.HankelH1(n:SymbolicExpression) = SymbolicExpression(hankelh1 n.Expression expression)
    member this.HankelH2(n:SymbolicExpression) = SymbolicExpression(hankelh2 n.Expression expression)
    member this.PointwiseMultiply(n:SymbolicExpression) = SymbolicExpression(PointwiseMul(expression, n.Expression))


    // STRUCTURE
    member this.NumberOfOperands = expression |> Structure.numberOfOperands
    member this.Operand(index:int) = SymbolicExpression(expression |> Structure.operand index)
    member this.Item
      with get(index) = this.Operand(index)
    member this.FreeOf(symbol:SymbolicExpression) = expression |> Structure.freeOf symbol.Expression
    member this.FreeOf(symbols:SymbolicExpression seq) = let s = System.Collections.Generic.HashSet<Expression>(symbols |> Seq.map unpack) in expression |> Structure.freeOfSet s
    member this.Substitute(x:SymbolicExpression, replacement:SymbolicExpression) = SymbolicExpression(expression |> Structure.substitute x.Expression replacement.Expression)
    member this.CollectVariables() = expression |> Structure.collectIdentifiers |> List.toSeq |> Seq.map pack
    member this.CollectRationalNumbers() = expression |> Structure.collectNumbers |> List.toSeq |> Seq.map pack
    member this.CollectRealNumbers() = expression |> Structure.collectDistinct (function | Approximation (Approximation.Real _) | Constant Pi | Constant E as e -> Some e |  _ -> None) |> Structure.sortList |> List.toSeq |> Seq.map pack
    member this.CollectComplexNumbers() = expression |> Structure.collectDistinct (function | Approximation (Approximation.Complex _) | Constant I as e -> Some e |  _ -> None) |> Structure.sortList |> List.toSeq |> Seq.map pack
    member this.CollectFunctions() = expression |> Structure.collectFunctions |> List.toSeq |> Seq.map pack
    member this.CollectSums() = expression |> Structure.collectSums |> List.toSeq |> Seq.map pack
    member this.CollectProducts() = expression |> Structure.collectProducts |> List.toSeq |> Seq.map pack
    member this.CollectPowers() = expression |> Structure.collectPowers |> List.toSeq |> Seq.map pack


    // ALGEBRAIC
    member this.Summands() = expression |> Algebraic.summands |> List.toSeq |> Seq.map pack
    member this.Factors() = expression |> Algebraic.factors |> List.toSeq |> Seq.map pack
    member this.Expand() = SymbolicExpression(Algebraic.expand expression)
    member this.ExpandMain() = SymbolicExpression(Algebraic.expandMain expression)


    // CALCULUS
    member this.Differentiate(variable:SymbolicExpression) = SymbolicExpression(expression |> Calculus.differentiate variable.Expression)
    member this.DifferentiateAt(variable:SymbolicExpression, value:SymbolicExpression) = SymbolicExpression(expression |> Calculus.differentiateAt variable.Expression value.Expression)
    member this.Taylor(k:int, variable:SymbolicExpression, value:SymbolicExpression) = SymbolicExpression(expression |> Calculus.taylor k variable.Expression value.Expression)
    member this.TangentLine(variable:SymbolicExpression, value:SymbolicExpression) = SymbolicExpression(expression |> Calculus.tangentLine variable.Expression value.Expression)
    member this.NormalLine(variable:SymbolicExpression, value:SymbolicExpression) = SymbolicExpression(expression |> Calculus.normalLine variable.Expression value.Expression)


    // GENERAL POLYNOMIAL
    member this.PolynomialVariables() = expression |> Polynomial.variables |> Seq.map pack
    member this.IsMonomial(variable:SymbolicExpression) = expression |> Polynomial.isMonomial variable.Expression
    member this.IsPolynomial(variable:SymbolicExpression) = expression |> Polynomial.isPolynomial variable.Expression
    member this.MonomialDegree(variable:SymbolicExpression) = SymbolicExpression(expression |> Polynomial.degreeMonomial variable.Expression)
    member this.PolynomialDegree(variable:SymbolicExpression) = SymbolicExpression(expression |> Polynomial.degree variable.Expression)
    member this.PolynomialTotalDegree() = SymbolicExpression(expression |> Polynomial.totalDegree)
    member this.PolynomialCommonFactors() = SymbolicExpression(expression |> Polynomial.commonFactors)
    member this.MonomialCoefficient(variable:SymbolicExpression) = SymbolicExpression(expression |> Polynomial.coefficientMonomial variable.Expression)
    member this.MonomialCoefficientDegree(variable:SymbolicExpression) = let coeff, degree = expression |> Polynomial.coefficientDegreeMonomial variable.Expression in SymbolicExpression(coeff), SymbolicExpression(degree)
    member this.Coefficient(variable:SymbolicExpression, k:int) = SymbolicExpression(expression |> Polynomial.coefficient variable.Expression k)
    member this.LeadingCoefficient(variable:SymbolicExpression) = SymbolicExpression(expression |> Polynomial.leadingCoefficient variable.Expression)
    member this.LeadingCoefficientDegree(variable:SymbolicExpression) = let coeff, degree = expression |> Polynomial.leadingCoefficientDegree variable.Expression in SymbolicExpression(coeff), SymbolicExpression(degree)
    member this.Coefficients(variable:SymbolicExpression) = expression |> Polynomial.coefficients variable.Expression |> Array.map pack
    member this.CollectPolynomialTerms(variable:SymbolicExpression) = SymbolicExpression(expression |> Polynomial.collectTerms variable.Expression)
    member this.PolynomialDivide(variable:SymbolicExpression, divisor:SymbolicExpression) = let quot, remainder = Polynomial.divide variable.Expression expression divisor.Expression in SymbolicExpression(quot), SymbolicExpression(remainder)
    member this.PolynomialQuotient(variable:SymbolicExpression, divisor:SymbolicExpression) = SymbolicExpression(Polynomial.quot variable.Expression expression divisor.Expression)
    member this.PolynomialRemainder(variable:SymbolicExpression, divisor:SymbolicExpression) = SymbolicExpression(Polynomial.remainder variable.Expression expression divisor.Expression)
    member this.PolynomialPseudoDivide(variable:SymbolicExpression, divisor:SymbolicExpression) = let pquot, premainder, b = Polynomial.pseudoDivide variable.Expression expression divisor.Expression in SymbolicExpression(pquot), SymbolicExpression(premainder), SymbolicExpression(b)
    member this.PolynomialPseudoQuotient(variable:SymbolicExpression, divisor:SymbolicExpression) = SymbolicExpression(Polynomial.pseudoQuot variable.Expression expression divisor.Expression)
    member this.PolynomialPseudoRemainder(variable:SymbolicExpression, divisor:SymbolicExpression) = SymbolicExpression(Polynomial.pseudoRemainder variable.Expression expression divisor.Expression)
    member this.PolynomialGcd(variable:SymbolicExpression, other:SymbolicExpression) = SymbolicExpression(Polynomial.gcd variable.Expression expression other.Expression)
    member this.IsSquareFree(variable:SymbolicExpression) = Polynomial.isSquareFree variable.Expression expression
    member this.FactorSquareFree(variable:SymbolicExpression) = SymbolicExpression(Polynomial.factorSquareFree variable.Expression expression)


    // MULTIVARIATE POLYNOMIAL
    member this.IsMultivariateMonomial([<System.ParamArray>] variables: SymbolicExpression array) = expression |> Polynomial.isMonomialMV (unpackArrayToSet variables)
    member this.IsMultivariatePolynomial([<System.ParamArray>] variables: SymbolicExpression array) = expression |> Polynomial.isPolynomialMV (unpackArrayToSet variables)
    member this.MultivariateMonomialDegree([<System.ParamArray>] variables: SymbolicExpression array) = SymbolicExpression(expression |> Polynomial.degreeMonomialMV (unpackArrayToSet variables))
    member this.MultivariatePolynomialDegree([<System.ParamArray>] variables: SymbolicExpression array) = SymbolicExpression(expression |> Polynomial.degreeMV (unpackArrayToSet variables))
    member this.MultivariateMonomialCoefficient([<System.ParamArray>] variables: SymbolicExpression array) = SymbolicExpression(expression |> Polynomial.coefficientMonomialMV (unpackArrayToSet variables))
    member this.CollectMultivariatePolynomialTerms([<System.ParamArray>] variables: SymbolicExpression array) = SymbolicExpression(expression |> Polynomial.collectTermsMV (unpackArrayToSet variables))


    // RATIONAL
    member this.Numerator() = SymbolicExpression(Rational.numerator expression)
    member this.Denominator() = SymbolicExpression(Rational.denominator expression)
    member this.Rationalize() = SymbolicExpression(Rational.rationalize expression)
    member this.RationalReduce() = SymbolicExpression(Rational.reduce expression)
    member this.RationalExpand() = SymbolicExpression(Rational.expand expression)
    member this.RationalSimplify(variable:SymbolicExpression) = SymbolicExpression(expression |> Rational.simplify variable.Expression)


    // EXPONENTIAL
    member this.ExponentialExpand() = SymbolicExpression(Exponential.expand expression)
    member this.ExponentialContract() = SymbolicExpression(Exponential.contract expression)
    member this.ExponentialSimplify() = SymbolicExpression(Exponential.simplify expression)


    // TRIGONOMETRIC
    member this.TrigonometricExpand() = SymbolicExpression(Trigonometric.expand expression)
    member this.TrigonometricContract() = SymbolicExpression(Trigonometric.contract expression)
    member this.TrigonometricSubstitute() = SymbolicExpression(Trigonometric.substitute expression)
    member this.TrigonometricSimplify() = SymbolicExpression(Trigonometric.simplify expression)


    // APPROXIMATE
    member this.Approximate() = SymbolicExpression(Approximate.approximate expression)
