namespace MathNet.Symbolics
open System
open System.Collections.Generic
open MathNet.Numerics
open MathNet.Numerics.LinearAlgebra
open DiffSharp

type TensorWrapper =
  | DSTensor of DiffSharp.Tensor
  | VecInTensor of MathNet.Numerics.LinearAlgebra.Vector<float>
  | ListOf of TensorWrapper list
and FloatingPoint =
  | Real of float
  | Complex of MathNet.Numerics.complex
  | RealVector of MathNet.Numerics.LinearAlgebra.Vector<float>
  | ComplexVector of MathNet.Numerics.LinearAlgebra.Vector<MathNet.Numerics.complex>
  | RealMatrix of MathNet.Numerics.LinearAlgebra.Matrix<float>
  | ComplexMatrix of MathNet.Numerics.LinearAlgebra.Matrix<MathNet.Numerics.complex>
  | Undef
  | PosInf
  | NegInf
  | ComplexInf
  | WTensor of TensorWrapper
  static member op_Implicit: x: DiffSharp.Tensor -> FloatingPoint
  static member op_Implicit: x: float32 -> FloatingPoint
  static member op_Implicit: x: complex -> FloatingPoint
  static member op_Implicit: x: complex32 -> FloatingPoint
  static member op_Implicit: x: Vector<float> -> FloatingPoint
  static member op_Implicit: x: Vector<complex> -> FloatingPoint
  static member op_Implicit: x: Matrix<float> -> FloatingPoint
  static member op_Implicit: x: Matrix<complex> -> FloatingPoint
  static member op_Implicit: x: Tensor -> FloatingPoint
  member ComplexMatrixValue: MathNet.Numerics.LinearAlgebra.Matrix<MathNet.Numerics.complex>
  member ComplexValue: System.Numerics.Complex
  member ComplexVectorValue: MathNet.Numerics.LinearAlgebra.Vector<MathNet.Numerics.complex>
  member DTensorValue: DiffSharp.Tensor
  member RealMatrixValue: MathNet.Numerics.LinearAlgebra.Matrix<float>
  member RealValue: float
  member RealVectorValue: MathNet.Numerics.LinearAlgebra.Vector<float>
module Evaluate =
    val listOf2Obj: wt0: TensorWrapper * shape: int list -> float[] * int list
    val listOf2DSTensor: wt0: TensorWrapper -> DiffSharp.Tensor
    val (|Infinity|_|) : _arg1: FloatingPoint -> unit option
    [<CompiledName("Real")>]
    val freal: x: float -> FloatingPoint
    [<CompiledName("Complex")>]
    val fcomplex: r: float -> i: float -> FloatingPoint
    val fnormalize: _arg1: FloatingPoint -> FloatingPoint
    val fadd: u: FloatingPoint -> v: FloatingPoint -> FloatingPoint
    val fmultiply: u: FloatingPoint -> v: FloatingPoint -> FloatingPoint
    val fpower: u: FloatingPoint -> v: FloatingPoint -> FloatingPoint
    val fapply:
      f: MathNet.Symbolics.Function -> u: FloatingPoint -> FloatingPoint
    val fapplyN:
      f: MathNet.Symbolics.FunctionN -> xs: FloatingPoint list -> FloatingPoint
    [<CompiledName("Evaluate")>]
    val evaluate:
      symbols: System.Collections.Generic.IDictionary<string,FloatingPoint>
      -> _arg1: MathNet.Symbolics.Expression -> FloatingPoint
