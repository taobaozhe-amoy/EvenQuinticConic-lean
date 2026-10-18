import EvenQuinticConic.IncidenceGenericFiber
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# An actual hyperbolic decomposition of the incidence quadratic form

Starting with the distinguished isotropic coordinate and a nonzero polar
coefficient, we construct an invertible coordinate matrix. Its congruence
splits off the standard hyperbolic plane and leaves precisely the already
constructed incidence restriction matrix, rather than an unspecified
isometric ternary form. No Clifford or Brauer comparison is asserted here.
-/

noncomputable section
set_option maxRecDepth 4096

namespace EvenQuinticConic.Incidence

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

@[simp] private theorem finCasesOne {α : Type*} (a : α) (f : Fin (n + 1) → α) :
    Fin.cases a f (1 : Fin (n + 2)) = f 0 := rfl

/-- The standard hyperbolic plane, with quadratic expression `2*x₀*x₁`,
orthogonally adjoined to the displayed restriction matrix. -/
def incidenceHyperbolicSumMatrix (R : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) K :=
  fun i j => Fin.cases (Fin.cases 0 (Fin.cases 1 (fun _ => 0)) j)
    (Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i => Fin.cases 0 (Fin.cases 0 (fun j => R i j)) j)) i

/-- The literal quadratic expression consists of the hyperbolic term and
the original restricted quadratic expression on the retained coordinates. -/
theorem incidenceHyperbolicSumMatrix_quadratic
    (R : Matrix (Fin n) (Fin n) K) (x : Fin (n + 2) → K) :
    dotProduct x ((incidenceHyperbolicSumMatrix R).mulVec x) =
      2 * x 0 * x 1 +
        dotProduct (fun i => x i.succ.succ) (R.mulVec (fun i => x i.succ.succ)) := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, incidenceHyperbolicSumMatrix]
  ring

/-- The first two columns are the distinguished isotropic vector and an
explicit normalized isotropic partner. The remaining columns are the polar
elimination columns corrected in the distinguished coordinate so that they
are orthogonal to both members of the hyperbolic pair. -/
def incidenceHyperbolicBasisMatrix
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) K :=
  fun i j => Fin.cases
    (Fin.cases 1
      (Fin.cases (-(A 1 1 / (2 * (A 1 0)^2)))
        (fun j => A 1 1 * A j.succ.succ 0 / (A 1 0)^2 -
          A 1 j.succ.succ / A 1 0)) j)
    (Fin.cases
      (Fin.cases 0
        (Fin.cases ((A 1 0)⁻¹) (fun j => -(A j.succ.succ 0 / A 1 0))) j)
      (fun i => Fin.cases 0 (Fin.cases 0 (fun j => if i = j then 1 else 0)) j)) i

/-- The displayed change of basis is upper triangular. -/
theorem incidenceHyperbolicBasisMatrix_upperTriangular
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) :
    (incidenceHyperbolicBasisMatrix A).BlockTriangular id := by
  intro i j hij
  induction i using Fin.cases with
  | zero => simp at hij
  | succ i =>
    induction j using Fin.cases with
    | zero => induction i using Fin.cases <;> simp [incidenceHyperbolicBasisMatrix]
    | succ j =>
      induction i using Fin.cases with
      | zero => simp at hij
      | succ i =>
        induction j using Fin.cases with
        | zero => simp [incidenceHyperbolicBasisMatrix]
        | succ j =>
          have hne : i ≠ j := by intro h; subst j; simp at hij
          simp [incidenceHyperbolicBasisMatrix, hne]

/-- Its determinant is the inverse of the actual polar pivot. -/
theorem incidenceHyperbolicBasisMatrix_det
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) :
    (incidenceHyperbolicBasisMatrix A).det = (A 1 0)⁻¹ := by
  rw [Matrix.det_of_upperTriangular (incidenceHyperbolicBasisMatrix_upperTriangular A)]
  simp [Fin.prod_univ_succ, incidenceHyperbolicBasisMatrix]

/-- The coordinate change is invertible as soon as the chosen actual polar
coefficient is nonzero. -/
theorem incidenceHyperbolicBasisMatrix_det_ne_zero
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (hpivot : A 1 0 ≠ 0) :
    (incidenceHyperbolicBasisMatrix A).det ≠ 0 := by
  rw [incidenceHyperbolicBasisMatrix_det]
  exact inv_ne_zero hpivot

/-- Literal congruence to the standard hyperbolic plane and the exact matrix
from polar elimination. All basis coefficients are constructed above. -/
theorem incidenceHyperbolicBasisMatrix_congruence
    (h2 : (2 : K) ≠ 0)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0) (hpivot : A 1 0 ≠ 0) :
    (incidenceHyperbolicBasisMatrix A).transpose * A *
        incidenceHyperbolicBasisMatrix A =
      incidenceHyperbolicSumMatrix (incidenceRestrictedMatrix A) := by
  have h01 : A 0 1 = A 1 0 := hA.apply 1 0
  have h0i (i : Fin n) : A 0 i.succ.succ = A i.succ.succ 0 := hA.apply _ _
  have hi1 (i : Fin n) : A i.succ.succ 1 = A 1 i.succ.succ := hA.apply _ _
  ext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [incidenceHyperbolicBasisMatrix, incidenceHyperbolicSumMatrix,
        Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hbase]
    | succ j =>
      induction j using Fin.cases with
      | zero => simp [incidenceHyperbolicBasisMatrix, incidenceHyperbolicSumMatrix,
          Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hbase, h01, hpivot]
      | succ j =>
        simp [incidenceHyperbolicBasisMatrix, incidenceHyperbolicSumMatrix,
          Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hbase, h01, h0i]
        field_simp
        ring
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp [incidenceHyperbolicBasisMatrix, incidenceHyperbolicSumMatrix,
          Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hbase, hpivot]
      | succ j =>
        induction j using Fin.cases with
        | zero =>
          simp [incidenceHyperbolicBasisMatrix, incidenceHyperbolicSumMatrix,
            Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hbase, h01]
          field_simp
          ring
        | succ j =>
          simp [incidenceHyperbolicBasisMatrix, incidenceHyperbolicSumMatrix,
            Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hbase, h01, h0i]
          field_simp
          ring
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp [incidenceHyperbolicBasisMatrix, incidenceHyperbolicSumMatrix,
          Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hbase]
        field_simp
        ring
      | succ j =>
        induction j using Fin.cases with
        | zero =>
          simp [incidenceHyperbolicBasisMatrix, incidenceHyperbolicSumMatrix,
            Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hbase, h01, hi1]
          field_simp
          ring
        | succ j =>
          simp [incidenceHyperbolicBasisMatrix, incidenceHyperbolicSumMatrix,
            Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
            incidenceRestrictedMatrix_apply, hbase, h01, h0i, hi1]
          field_simp
          ring

/-- Move the constructed basis back through the actual chosen polar
permutation. This is a matrix in the original coordinates of `A`. -/
def incidencePivotHyperbolicBasisMatrix
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (r : Fin (n + 1)) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) K :=
  (incidenceHyperbolicBasisMatrix (incidencePivotMatrix A r)).submatrix
    (incidencePivotEquiv r).symm id

/-- The basis in the original coordinates is invertible at any nonzero
polar pivot. -/
theorem incidencePivotHyperbolicBasisMatrix_det_ne_zero
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (r : Fin (n + 1)) (hpivot : A r.succ 0 ≠ 0) :
    (incidencePivotHyperbolicBasisMatrix A r).det ≠ 0 := by
  rw [incidencePivotHyperbolicBasisMatrix, Matrix.det_permute]
  apply mul_ne_zero
  · exact isUnit_iff_ne_zero.mp
      ((Equiv.Perm.sign (incidencePivotEquiv r).symm).isUnit.map (Int.castRingHom K))
  · apply incidenceHyperbolicBasisMatrix_det_ne_zero
    simpa [incidencePivotMatrix] using hpivot

/-- The original matrix, without relabelling its coordinates in the
statement, splits as a standard hyperbolic plane and precisely the actual
restriction at the chosen pivot. -/
theorem incidencePivotHyperbolicBasisMatrix_congruence
    (h2 : (2 : K) ≠ 0)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0)
    (r : Fin (n + 1)) (hpivot : A r.succ 0 ≠ 0) :
    (incidencePivotHyperbolicBasisMatrix A r).transpose * A *
        incidencePivotHyperbolicBasisMatrix A r =
      incidenceHyperbolicSumMatrix (incidenceRestrictedMatrix (incidencePivotMatrix A r)) := by
  let e := incidencePivotEquiv r
  let B := incidenceHyperbolicBasisMatrix (incidencePivotMatrix A r)
  let P := incidencePivotHyperbolicBasisMatrix A r
  have he : P.submatrix e id = B := by
    ext i j
    simp [P, incidencePivotHyperbolicBasisMatrix, e, B]
  have het : P.transpose.submatrix id e = B.transpose := by
    ext i j
    exact congrArg (fun T => T j i) he
  have hcong : P.transpose * A * P = B.transpose * incidencePivotMatrix A r * B := by
    calc
      P.transpose * A * P = (P.transpose * A * P).submatrix id id := rfl
      _ = (P.transpose.submatrix id e * A.submatrix e e) * P.submatrix e id := by
        rw [Matrix.submatrix_mul _ _ id e id e.bijective,
          Matrix.submatrix_mul _ _ id e e e.bijective]
      _ = B.transpose * incidencePivotMatrix A r * B := by rw [he, het]; rfl
  change P.transpose * A * P = _
  rw [hcong]
  apply incidenceHyperbolicBasisMatrix_congruence h2 _
    (incidencePivotMatrix_isSymm A hA r)
  · simpa [incidencePivotMatrix] using hbase
  · simpa [incidencePivotMatrix] using hpivot

end EvenQuinticConic.Incidence
