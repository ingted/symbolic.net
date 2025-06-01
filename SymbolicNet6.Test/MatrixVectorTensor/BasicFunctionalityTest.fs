namespace MathNet.Symbolics.Tests
#if INTERACTIVE
#r "nuget: DiffSharp.Core, 1.0.7"
#r "nuget: DiffSharp-cpu, 1.0.7"
#r "nuget: DiffSharp.Backends.Reference, 1.0.7"
#r "nuget: DiffSharp.Backends.Torch, 1.0.7"
#endif

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
open DiffSharp
module MatrixVector =

    type Expr = SymbolicExpression

    let KeyNotFoundException : Type -> Constraints.EqualConstraint = throwWithMessage "The given key was not present in the dictionary."

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
        Infix.parseOrThrow("test(a+1, a + a) + test(a+1, a*2)") ==> "2*test(1 + a,2*a)"

        //(fun () -> Infix.parseOrThrow("test1(a+1, a*2)") |> ignore)
        //    |> should KeyNotFoundException keyNotFoundType

        //(fun () -> Evaluate.evaluate symbols (f) |> ignore) |> should (throwWithMessage "Failed to find symbol f") typeof<System.Exception>
        //System.Collections.Generic.KeyNotFoundException : The given key was not present in the dictionary.

        let expr001 = Expr.Parse("htensor(list_of(list_of(list_of(vec(1,2,3), vec(4,5,6)), list_of(vec(7,8,9), vec(10,11,12)))))")
        let expr002 = Expr.Parse("htensor(lo(lo(lo(vec(1,2,3), vec(4,5,6)), lo(vec(7,8,9), vec(10,11,12)))))")
        let s001 = expr001.ToString()
        printfn "s001: %s" s001
        expr001.Expression ==> "htensor(list_of(list_of(list_of(vec(1,2,3),vec(4,5,6)),list_of(vec(7,8,9),vec(10,11,12)))))"


        let eval001 = expr001.Evaluate(dict[])
        let eval002 = expr002.Evaluate(dict[])
        eval001 |> shouldEqual eval002


        dsharp.view (dsharp.tensor [1.0; 2.0; 3.0; 4.0; 5.0; 6.0; 7.0; 8.0; 9.0; 10.0; 11.0; 12.0], [1;2;2;3])
        |> shouldEqual eval001.DTensorValue

        ()
