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

type EvaluateHelper = {
    trivial: bool
}
