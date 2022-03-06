namespace MathNet.Symbolics.Tests

open NUnit.Framework
open FsUnit

open MathNet.Numerics
open MathNet.Symbolics

open Operators
open VariableSets.Alphabet
open FsUnitTyped
open Definition

open System
open MathNet.Numerics.LinearAlgebra


module MatrixVector =

    type Expr = SymbolicExpression

    let KeyNotFoundException = throwWithMessage "The given key was not present in the dictionary."

    let keyNotFoundType = typeof<System.Collections.Generic.KeyNotFoundException>

    [<Test>]
    let ``Matrix Vector Expressions`` () =

        let V = FloatingPoint.RealVector <| vector[1.0;2.0;3.0]

        let M = FloatingPoint.RealMatrix <|
                matrix [[3.0; 0.0; 0.0]
                        [1.0; 2.0; 0.0]
                        [0.0; 1.0; 4.0]]

        let symbols2 = dict[ "a", V; "m", M ]

        Infix.parseOrThrow("mat_by_row(a, a)") ==> "mat_by_row(a,a)"
        Infix.parseOrThrow("mat_by_col(a, a)") ==> "mat_by_col(a,a)"
        Infix.parseOrThrow("mat_multiply(m, mat_by_col(a, vec(1.0,2.0,3.0), a), a)") ==> "mat_multiply(m,mat_by_col(a,vec(1.0,2.0,3.0),a),a)"


        Expr.Parse("mat_by_row(a, a)").ToString() |> shouldEqual """mat_by_row(a,a)"""
        Expr.Parse("mat_by_col(a, a)").ToString() |> shouldEqual """mat_by_col(a,a)"""
        Expr.Parse("mat_multiply(m, mat_by_col(a, vec(1.0,2.0,3.0), a), a)").ToString() |> shouldEqual """mat_multiply(m,mat_by_col(a,vec(1.0,2.0,3.0),a),a)"""


        let symV = Symbol "v"
        let symW = Symbol "w"
        let _ = define "test" ([symV; symW], (v + w)*2)
        Infix.parseOrThrow("test(a+1, a*2)") ==> "test(1 + a,2*a)"
        (fun () -> Infix.parseOrThrow("test1(a+1, a*2)") |> ignore)
            |> should KeyNotFoundException keyNotFoundType

        //(fun () -> Evaluate.evaluate symbols (f) |> ignore) |> should (throwWithMessage "Failed to find symbol f") typeof<System.Exception>
        //System.Collections.Generic.KeyNotFoundException : The given key was not present in the dictionary.
