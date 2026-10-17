import EvenQuinticConic.GeometricJacobianTransfer
import EvenQuinticConic.NetCoordinateChange

/-!
# Geometric Jacobian certificates under coordinate congruence

The determinant equation of an actual matrix net changes by the nonzero
constant square of the coordinate determinant. The Jacobian ideals are
therefore equal, so the certificate valid over all field extensions survives
normalization of a common point. No claim about geometric smoothness is
inferred from a condition only on base-field vectors.
-/

namespace EvenQuinticConic

open Matrix MvPolynomial

variable {K σ : Type*} [Field K]

/-- Scaling an equation by a constant can only shrink its Jacobian ideal. -/
theorem actualJacobianIdeal_C_mul_le (F : MvPolynomial σ K) (c : K) :
    actualJacobianIdeal (C c * F) ≤ actualJacobianIdeal F := by
  apply Ideal.span_le.mpr
  intro P hP
  rcases hP with hP | ⟨i, hi⟩
  · rw [hP]
    exact Ideal.mul_mem_left _ _ (self_mem_actualJacobianIdeal F)
  · rw [← hi]
    simpa only [pderiv_C_mul] using
      Ideal.mul_mem_left (actualJacobianIdeal F) (C c)
        (pderiv_mem_actualJacobianIdeal F i)

/-- A nonzero constant scaling leaves the actual Jacobian ideal unchanged. -/
theorem actualJacobianIdeal_C_mul (F : MvPolynomial σ K) (c : K) (hc : c ≠ 0) :
    actualJacobianIdeal (C c * F) = actualJacobianIdeal F := by
  apply le_antisymm (actualJacobianIdeal_C_mul_le F c)
  have hinv : C c⁻¹ * (C c * F) = F := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  calc
    actualJacobianIdeal F = actualJacobianIdeal (C c⁻¹ * (C c * F)) :=
      congrArg actualJacobianIdeal hinv.symm
    _ ≤ actualJacobianIdeal (C c * F) := actualJacobianIdeal_C_mul_le _ _

/-- The extension-independent Jacobian certificate is unchanged by a nonzero
constant scaling of the defining equation. -/
theorem projectiveJacobianCertificate_C_mul_iff
    (F : MvPolynomial σ K) (c : K) (hc : c ≠ 0) :
    ProjectiveJacobianCertificate (C c * F) ↔ ProjectiveJacobianCertificate F := by
  unfold ProjectiveJacobianCertificate
  rw [actualJacobianIdeal_C_mul F c hc]

/-- Nonzero constant scaling preserves the geometric Jacobian certificate. -/
theorem ProjectiveJacobianCertificate.C_mul
    {F : MvPolynomial σ K} (hCert : ProjectiveJacobianCertificate F)
    (c : K) (hc : c ≠ 0) : ProjectiveJacobianCertificate (C c * F) :=
  (projectiveJacobianCertificate_C_mul_iff F c hc).mpr hCert

variable {n : Type*} [Fintype n] [DecidableEq n] [Fintype σ]

/-- Congruence by an invertible coordinate matrix preserves the actual
radical-ideal Jacobian certificate for the determinant polynomial. -/
theorem linearMatrixNet_congruence_jacobianCertificate
    (M : σ → Matrix n n K) (B : Matrix n n K) (hB : B.det ≠ 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det) :
    ProjectiveJacobianCertificate (linearMatrixNet (matrixNetCongruence M B)).det := by
  rw [linearMatrixNet_congruence_det]
  exact hCert.C_mul (B.det * B.det) (mul_ne_zero hB hB)

/-- The geometric Jacobian certificates before and after coordinate change
are equivalent; the congruence loses no geometric smoothness information. -/
theorem linearMatrixNet_congruence_jacobianCertificate_iff
    (M : σ → Matrix n n K) (B : Matrix n n K) (hB : B.det ≠ 0) :
    ProjectiveJacobianCertificate (linearMatrixNet (matrixNetCongruence M B)).det ↔
      ProjectiveJacobianCertificate (linearMatrixNet M).det := by
  rw [linearMatrixNet_congruence_det]
  exact projectiveJacobianCertificate_C_mul_iff _ _ (mul_ne_zero hB hB)

omit [Fintype n] [DecidableEq n] in
/-- Normalize a common nonzero isotropic point while retaining the geometric
Jacobian certificate and proving independence of the remaining polar rows. -/
theorem exists_normalized_matrixNet_common_point_with_certificate
    [DecidableEq σ] {m : ℕ}
    (M : σ → Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : ∀ i, (M i).IsSymm) (P : Fin (m + 1) → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det) :
    ∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) K,
      B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      (∀ i, (matrixNetCongruence M B i).IsSymm) ∧
      (∀ i, matrixNetCongruence M B i 0 0 = 0) ∧
      ProjectiveJacobianCertificate (linearMatrixNet (matrixNetCongruence M B)).det ∧
      LinearIndependent K (fun i (j : Fin m) => matrixNetCongruence M B i j.succ 0) := by
  obtain ⟨B, hB, hcol, hsym, hbase, _, hind⟩ :=
    exists_normalized_matrixNet_common_point M hM P hP hisotropic hCert.rational_jacobian
  exact ⟨B, hB, hcol, hsym, hbase,
    linearMatrixNet_congruence_jacobianCertificate M B hB hCert, hind⟩

end EvenQuinticConic
