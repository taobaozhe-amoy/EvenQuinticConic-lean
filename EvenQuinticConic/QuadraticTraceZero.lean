import Mathlib.Algebra.QuadraticAlgebra
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# The actual trace-zero module of a local quadratic algebra

These results concern the explicit algebra with t² = u. They do not assert
that an arbitrary finite étale double cover already has a chosen such chart.
-/
noncomputable section
open scoped TensorProduct
namespace EvenQuinticConic
variable {R : Type*} [CommRing R]

/-- The local quadratic algebra, with its actual mathlib algebra structure. -/
abbrev KummerAlgebra (u : R) := QuadraticAlgebra R u 0

/-- The basis element t of the actual quadratic algebra. -/
def kummerGenerator (u : R) : KummerAlgebra u := ⟨0, 1⟩

@[simp] theorem kummerGenerator_sq (u : R) :
    kummerGenerator u * kummerGenerator u = algebraMap R (KummerAlgebra u) u := by
  ext <;> simp [kummerGenerator, QuadraticAlgebra.algebraMap_eq]

/-- This is the trace of multiplication, not a newly defined trace function. -/
theorem kummer_trace (u : R) (x : KummerAlgebra u) :
    Algebra.trace R (KummerAlgebra u) x = 2 * x.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis u 0)]
  have h0 : (QuadraticAlgebra.basis u (0 : R)) 0 = ⟨1, 0⟩ := by
    apply (QuadraticAlgebra.basis u (0 : R)).repr.injective
    ext i
    fin_cases i <;> simp
  have h1 : (QuadraticAlgebra.basis u (0 : R)) 1 = ⟨0, 1⟩ := by
    apply (QuadraticAlgebra.basis u (0 : R)).repr.injective
    ext i
    fin_cases i <;> simp
  simp [Matrix.trace, Fin.sum_univ_two, Algebra.leftMulMatrix_eq_repr_mul,
    QuadraticAlgebra.basis_repr_apply, h0, h1]
  ring

/-- The genuine kernel of the algebra trace. -/
abbrev KummerTraceZero (u : R) := LinearMap.ker (Algebra.trace R (KummerAlgebra u))

variable [Invertible (2 : R)]

theorem kummer_trace_zero_iff (u : R) (x : KummerAlgebra u) :
    Algebra.trace R (KummerAlgebra u) x = 0 ↔ x.re = 0 := by
  rw [kummer_trace]
  exact (isUnit_of_invertible (2 : R)).mul_right_eq_zero

/-- The imaginary coefficient gives a basis of the actual trace kernel. -/
def kummerTraceZeroCoordinate (u : R) : KummerTraceZero u ≃ₗ[R] R where
  toFun x := x.val.im
  invFun r := ⟨⟨0, r⟩, by simp [LinearMap.mem_ker, kummer_trace]⟩
  left_inv x := by
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · exact ((kummer_trace_zero_iff u x.val).mp x.property).symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication of two trace-zero elements is a scalar, with coefficient uab. -/
theorem kummer_traceZero_mul (u : R) (x y : KummerTraceZero u) :
    x.val * y.val = algebraMap R (KummerAlgebra u)
      (u * (kummerTraceZeroCoordinate u x * kummerTraceZeroCoordinate u y)) := by
  have hx := (kummer_trace_zero_iff u x.val).mp x.property
  have hy := (kummer_trace_zero_iff u y.val).mp y.property
  ext <;> simp [QuadraticAlgebra.algebraMap_eq, hx, hy, kummerTraceZeroCoordinate]
  ring

/-- When u is a unit, multiplication is an actual tensor-square isomorphism. -/
def kummerTraceZeroTensorEquiv (u : Rˣ) :
    KummerTraceZero (u : R) ⊗[R] KummerTraceZero (u : R) ≃ₗ[R] R :=
  (TensorProduct.congr (kummerTraceZeroCoordinate (u : R))
    (kummerTraceZeroCoordinate (u : R))).trans
    ((TensorProduct.lid R R).trans (LinearEquiv.smulOfUnit (R := R) (M := R) u))

/-- The tensor isomorphism is induced by the actual algebra multiplication. -/
theorem kummerTraceZeroTensorEquiv_mul (u : Rˣ)
    (x y : KummerTraceZero (u : R)) :
    x.val * y.val = algebraMap R (KummerAlgebra (u : R))
      (kummerTraceZeroTensorEquiv u (x ⊗ₜ[R] y)) := by
  simpa [kummerTraceZeroTensorEquiv, LinearEquiv.smulOfUnit, Units.smul_def] using
    kummer_traceZero_mul (u : R) x y

end EvenQuinticConic
