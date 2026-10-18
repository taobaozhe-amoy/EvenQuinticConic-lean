import EvenQuinticConic.IncidenceHyperbolicClifford
import EvenQuinticConic.NetCoordinateChange

/-!
# Transport from the normalized net back to the original matrix net

The original net is evaluated at the same actual Cramer parameters used for
the normalized incidence construction. The original coordinate matrix is
extended to that same parameter field. Its congruence is proved to equal
the constructed normalized generic matrix, giving actual quadratic-space
and even-Clifford equivalences over the parameter field. In particular no
unexplained comparison with the original net is an input.
-/

noncomputable section
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000

namespace EvenQuinticConic.Incidence

open Matrix

attribute [local irreducible] incidenceParameterSubfield

variable {K : Type*} [Field K]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (B : Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow (matrixNetCongruence M B)) k p)
      (segreChartRow (netQuadraticRow (matrixNetCongruence M B)) k p)).z ≠ 0)

local notation "S" => incidenceParameterSubfield (matrixNetCongruence M B) k p h

-- Keep scalar inference on the actual parameter field from searching
-- through its presentation as an intermediate field of a rational field.
local instance : Module S (Fin 5 → S) := Pi.module (Fin 5) (fun _ => S) S
local instance : Module S (Fin 3 → S) := Pi.module (Fin 3) (fun _ => S) S

/-- The original matrix net, evaluated at the same normalized actual
Cramer parameter point, without changing the parameter-field embedding. -/
def incidenceOriginalGenericMatrix : Matrix (Fin 5) (Fin 5) S :=
  ∑ i, incidenceGenericParameter (matrixNetCongruence M B) k p h i •
    (M i).map (algebraMap K S)

/-- The entries retain the original matrix coefficients and the exact
parameter functions used by the normalized incidence construction. -/
theorem incidenceOriginalGenericMatrix_entry (u v : Fin 5) :
    incidenceOriginalGenericMatrix M B k p h u v =
      ∑ i, incidenceGenericParameter (matrixNetCongruence M B) k p h i *
        algebraMap K S (M i u v) := by
  simp [incidenceOriginalGenericMatrix, Matrix.sum_apply, Matrix.smul_apply]

/-- This is the literal evaluation of the original matrix net, after
extending its coefficients to the same parameter field. -/
theorem incidenceOriginalGenericMatrix_eq_evaluation :
    incidenceOriginalGenericMatrix M B k p h =
      (linearMatrixNet (fun i => (M i).map (algebraMap K S))).map
        (MvPolynomial.eval (incidenceGenericParameter (matrixNetCongruence M B) k p h)) := by
  ext u v
  simp [incidenceOriginalGenericMatrix_entry, linearMatrixNet, Matrix.map_apply, mul_comm]

/-- Extending the original coordinate matrix and evaluating the net commute
with the actual congruence, over the same parameter field. -/
theorem incidenceOriginalGenericMatrix_congruence :
    (B.map (algebraMap K S)).transpose * incidenceOriginalGenericMatrix M B k p h *
        B.map (algebraMap K S) =
      incidenceGenericMatrix (matrixNetCongruence M B) k p h := by
  have hn : incidenceGenericMatrix (matrixNetCongruence M B) k p h =
      ∑ i, incidenceGenericParameter (matrixNetCongruence M B) k p h i •
        (matrixNetCongruence M B i).map (algebraMap K S) := by
    ext u v
    simp only [incidenceGenericMatrix_entry, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul]
  rw [hn]
  simp only [incidenceOriginalGenericMatrix, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, matrixNetCongruence, Matrix.map_mul]
  rfl

/-- The coordinate matrix remains invertible in the actual parameter field. -/
theorem incidenceNormalizationMatrix_det_ne_zero (hB : B.det ≠ 0) :
    (B.map (algebraMap K S)).det ≠ 0 := by
  have hd : (B.map (algebraMap K S)).det = algebraMap K S B.det :=
    ((algebraMap K S).map_det B).symm
  rw [hd]
  exact (map_ne_zero (algebraMap K S)).mpr hB

/-- Actual quadratic-space transport back to the original matrix net at
the same parameters. -/
def incidenceNormalizationQuadraticIsometry (hB : B.det ≠ 0) :
    (matrixQuadraticForm
      (incidenceGenericMatrix (matrixNetCongruence M B) k p h)).IsometryEquiv
      (matrixQuadraticForm (incidenceOriginalGenericMatrix M B k p h)) :=
  matrixQuadraticIsometryOfCongruence _ (B.map (algebraMap K S)) _
    (isUnit_iff_ne_zero.mpr (incidenceNormalizationMatrix_det_ne_zero M B k p h hB))
    (incidenceOriginalGenericMatrix_congruence M B k p h)

@[simp] theorem incidenceNormalizationQuadraticIsometry_apply
    (hB : B.det ≠ 0) (x : Fin 5 → S) :
    incidenceNormalizationQuadraticIsometry M B k p h hB x =
      B.map (algebraMap K S) *ᵥ x := rfl

/-- The even Clifford comparison is over the actual parameter field,
rather than merely over the original ground field. -/
def incidenceNormalizationEvenCliffordEquiv (hB : B.det ≠ 0) :
    CliffordAlgebra.even (matrixQuadraticForm
      (incidenceGenericMatrix (matrixNetCongruence M B) k p h)) ≃ₐ[S]
      CliffordAlgebra.even (matrixQuadraticForm (incidenceOriginalGenericMatrix M B k p h)) :=
  evenCliffordEquivOfIsometry (incidenceNormalizationQuadraticIsometry M B k p h hB)

/-- The same exact ternary form from the normalized incidence conic gives
a hyperbolic decomposition of the original generic matrix at those parameters. -/
def incidenceOriginalGenericQuadraticIsometry
    (h2 : (2 : K) ≠ 0) (hM : ∀ i, (M i).IsSymm)
    (hB : B.det ≠ 0) (hbase : ∀ i, matrixNetCongruence M B i 0 0 = 0)
    (r : Fin 4) (hr : incidenceGenericMatrix (matrixNetCongruence M B) k p h r.succ 0 ≠ 0) :
    (matrixQuadraticForm (incidenceHyperbolicSumMatrix
      (incidenceGenericConicMatrix (matrixNetCongruence M B) k p h r))).IsometryEquiv
        (matrixQuadraticForm (incidenceOriginalGenericMatrix M B k p h)) :=
  (incidenceGenericQuadraticIsometry h2 (matrixNetCongruence M B)
    (matrixNetCongruence_isSymm M hM B) hbase k p h r hr).trans
      (incidenceNormalizationQuadraticIsometry M B k p h hB)

/-- The composed isometry retains both actual coordinate changes, in order. -/
theorem incidenceOriginalGenericQuadraticIsometry_apply
    (h2 : (2 : K) ≠ 0) (hM : ∀ i, (M i).IsSymm)
    (hB : B.det ≠ 0) (hbase : ∀ i, matrixNetCongruence M B i 0 0 = 0)
    (r : Fin 4) (hr : incidenceGenericMatrix (matrixNetCongruence M B) k p h r.succ 0 ≠ 0)
    (x : Fin 5 → S) :
    incidenceOriginalGenericQuadraticIsometry M B k p h h2 hM hB hbase r hr x =
      B.map (algebraMap K S) *ᵥ
        (incidencePivotHyperbolicBasisMatrix
          (incidenceGenericMatrix (matrixNetCongruence M B) k p h) r *ᵥ x) := rfl

/-- Full actual normalization and hyperbolic transport, retaining the same
parameter field and the original generic matrix coefficients. -/
def incidenceOriginalGenericEvenCliffordEquiv
    (h2 : (2 : K) ≠ 0) (hM : ∀ i, (M i).IsSymm)
    (hB : B.det ≠ 0) (hbase : ∀ i, matrixNetCongruence M B i 0 0 = 0)
    (r : Fin 4) (hr : incidenceGenericMatrix (matrixNetCongruence M B) k p h r.succ 0 ≠ 0) :
    CliffordAlgebra.even (matrixQuadraticForm (incidenceHyperbolicSumMatrix
      (incidenceGenericConicMatrix (matrixNetCongruence M B) k p h r))) ≃ₐ[S]
        CliffordAlgebra.even (matrixQuadraticForm (incidenceOriginalGenericMatrix M B k p h)) :=
  evenCliffordEquivOfIsometry
    (incidenceOriginalGenericQuadraticIsometry M B k p h h2 hM hB hbase r hr)

end EvenQuinticConic.Incidence
