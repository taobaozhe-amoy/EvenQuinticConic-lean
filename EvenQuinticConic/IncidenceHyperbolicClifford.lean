import EvenQuinticConic.IncidenceHyperbolicDecomposition
import EvenQuinticConic.MatrixQuadraticClifford
import EvenQuinticConic.IncidenceGenericConicGeometry

/-!
# Actual quadratic-space and even-Clifford hyperbolic comparisons

The constructed coordinate matrix compares the original quadratic space with
the hyperbolic plane and precisely the incidence polar restriction. The same
comparison induces an equivalence of actual even Clifford subalgebras, with
the coefficient field and vector-product generators retained. This is not
yet the separate matrix-algebra theorem `C₀(H ⊥ r) ≃ M₂(C₀(r))`.
-/

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace EvenQuinticConic.Incidence

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The displayed block matrix represents the standard hyperbolic plane
orthogonally summed with the original restriction quadratic form. -/
theorem matrixQuadraticForm_hyperbolicSum_apply
    (R : Matrix (Fin n) (Fin n) K) (x : Fin (n + 2) → K) :
    matrixQuadraticForm (incidenceHyperbolicSumMatrix R) x =
      2 * x 0 * x 1 + matrixQuadraticForm R (fun i => x i.succ.succ) := by
  change (incidenceHyperbolicSumMatrix R).toBilin' x x =
    2 * x 0 * x 1 + R.toBilin' (fun i => x i.succ.succ) (fun i => x i.succ.succ)
  simp only [Matrix.toBilin'_apply']
  exact incidenceHyperbolicSumMatrix_quadratic R x

/-- An actual isometry with the original quadratic form, for the chosen
polar pivot and the exact existing restriction matrix. -/
def incidencePivotQuadraticIsometry (h2 : (2 : K) ≠ 0)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0)
    (r : Fin (n + 1)) (hr : A r.succ 0 ≠ 0) :
    (matrixQuadraticForm (incidenceHyperbolicSumMatrix
      (incidenceRestrictedMatrix (incidencePivotMatrix A r)))).IsometryEquiv
        (matrixQuadraticForm A) :=
  matrixQuadraticIsometryOfCongruence A (incidencePivotHyperbolicBasisMatrix A r) _
    (isUnit_iff_ne_zero.mpr (incidencePivotHyperbolicBasisMatrix_det_ne_zero A r hr))
    (incidencePivotHyperbolicBasisMatrix_congruence h2 A hA hbase r hr)

/-- The isometry is the displayed coordinate matrix, not an unspecified
quadratic-space equivalence. -/
theorem incidencePivotQuadraticIsometry_apply (h2 : (2 : K) ≠ 0)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0)
    (r : Fin (n + 1)) (hr : A r.succ 0 ≠ 0) (x : Fin (n + 2) → K) :
    incidencePivotQuadraticIsometry h2 A hA hbase r hr x =
      incidencePivotHyperbolicBasisMatrix A r *ᵥ x := rfl

/-- The actual even Clifford algebras are compared over the original field. -/
def incidencePivotEvenCliffordEquiv (h2 : (2 : K) ≠ 0)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0)
    (r : Fin (n + 1)) (hr : A r.succ 0 ≠ 0) :
    CliffordAlgebra.even (matrixQuadraticForm (incidenceHyperbolicSumMatrix
      (incidenceRestrictedMatrix (incidencePivotMatrix A r)))) ≃ₐ[K]
        CliffordAlgebra.even (matrixQuadraticForm A) :=
  evenCliffordEquivOfIsometry (incidencePivotQuadraticIsometry h2 A hA hbase r hr)

/-- Every even vector-product generator is transported by the same actual
coordinate matrix as the quadratic-space isometry. -/
theorem incidencePivotEvenCliffordEquiv_ι (h2 : (2 : K) ≠ 0)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0)
    (r : Fin (n + 1)) (hr : A r.succ 0 ≠ 0) (x y : Fin (n + 2) → K) :
    incidencePivotEvenCliffordEquiv h2 A hA hbase r hr
      ((CliffordAlgebra.even.ι (matrixQuadraticForm (incidenceHyperbolicSumMatrix
        (incidenceRestrictedMatrix (incidencePivotMatrix A r))))).bilin x y) =
      (CliffordAlgebra.even.ι (matrixQuadraticForm A)).bilin
        (incidencePivotHyperbolicBasisMatrix A r *ᵥ x)
        (incidencePivotHyperbolicBasisMatrix A r *ᵥ y) :=
  evenCliffordEquivOfIsometry_ι _ x y

section Generic

variable (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (r : Fin 4) (hr : incidenceGenericMatrix M k p h r.succ 0 ≠ 0)

/-- The original actual generic matrix and the exact conic matrix, over the
actual Cramer parameter subfield, form the proved hyperbolic decomposition. -/
def incidenceGenericQuadraticIsometry :
    (matrixQuadraticForm (incidenceHyperbolicSumMatrix
      (incidenceGenericConicMatrix M k p h r))).IsometryEquiv
        (matrixQuadraticForm (incidenceGenericMatrix M k p h)) :=
  incidencePivotQuadraticIsometry
    (incidenceParameterSubfield_two_ne_zero h2 M k p h)
    (incidenceGenericMatrix M k p h)
    (incidenceGenericMatrix_isSymm M hM k p h)
    (incidenceGenericMatrix_zero_zero M hbase k p h) r hr

/-- Actual even Clifford transport keeps the same parameter field and the
same ternary matrix that defines the already constructed projective conic. -/
def incidenceGenericEvenCliffordEquiv :
    CliffordAlgebra.even (matrixQuadraticForm (incidenceHyperbolicSumMatrix
      (incidenceGenericConicMatrix M k p h r))) ≃ₐ[incidenceParameterSubfield M k p h]
        CliffordAlgebra.even (matrixQuadraticForm (incidenceGenericMatrix M k p h)) :=
  evenCliffordEquivOfIsometry (incidenceGenericQuadraticIsometry h2 M hM hbase k p h r hr)

end Generic

end EvenQuinticConic.Incidence
