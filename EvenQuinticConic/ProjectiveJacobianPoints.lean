import EvenQuinticConic.PlaneQuintic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Nonzero vectors as actual projective points

The homogeneous prime attached to a nonzero vector is constructed as the
kernel of `X i ↦ v i * T`. This identifies homogeneous ideal membership with
ordinary evaluation at the vector and relates a gradient condition on all
points of `Proj` to the rational-point Jacobian condition.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial

variable {K : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous ideal of a line represented by a vector. -/
def vectorHomogeneousIdeal (v : Fin 3 → K) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 3) K) where
  toSubmodule := RingHom.ker (gradedRestriction v).toRingHom
  is_homogeneous' := by
    intro d P hP
    rw [← DirectSum.Decomposition.decompose'_eq,
      MvPolynomial.decomposition.decompose'_apply]
    change gradedRestriction v (homogeneousComponent d P) = 0
    exact gradedRestriction_homogeneousComponent_eq_zero v P hP d

/-- For homogeneous forms, membership in the vector ideal is ordinary
vanishing at that vector. -/
theorem mem_vectorHomogeneousIdeal_iff (v : Fin 3 → K)
    (P : PlanePolynomial K) (d : ℕ) (hP : P.IsHomogeneous d) :
    P ∈ (vectorHomogeneousIdeal v).toIdeal ↔ eval v P = 0 := by
  change gradedRestriction v P = 0 ↔ _
  rw [gradedRestriction_of_isHomogeneous v P d hP]
  simp [aeval_def]

/-- A nonzero vector gives an actual relevant homogeneous prime, hence an
actual point of the projective spectrum. -/
def vectorProjectivePoint (v : Fin 3 → K) (hv : v ≠ 0) :
    ProjectiveSpectrum (homogeneousSubmodule (Fin 3) K) where
  asHomogeneousIdeal := vectorHomogeneousIdeal v
  isPrime := RingHom.ker_isPrime (gradedRestriction v).toRingHom
  not_irrelevant_le := by
    intro hle
    apply hv
    funext i
    have hi : X i ∈ vectorHomogeneousIdeal v := hle (by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne (homogeneousSubmodule (Fin 3) K)
        (isHomogeneous_X K i) (by decide : (1 : ℕ) ≠ 0))
    have hi' := (mem_vectorHomogeneousIdeal_iff v (X i) 1
      (isHomogeneous_X K i)).mp hi
    simpa using hi'

/-- Homogeneous vanishing at the actual projective point agrees with
vanishing at its representing nonzero vector. -/
theorem mem_vectorProjectivePoint_iff (v : Fin 3 → K) (hv : v ≠ 0)
    (P : PlanePolynomial K) (d : ℕ) (hP : P.IsHomogeneous d) :
    P ∈ (vectorProjectivePoint v hv).asHomogeneousIdeal.toIdeal ↔ eval v P = 0 :=
  mem_vectorHomogeneousIdeal_iff v P d hP

/-- A gradient nonvanishing condition on the actual projective spectrum
implies the usual nonzero-vector Jacobian condition over the base field. -/
theorem rational_jacobian_of_projective_gradient
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hgrad : ∀ p : ProjectiveSpectrum (homogeneousSubmodule (Fin 3) K),
      F ∈ p.asHomogeneousIdeal.toIdeal →
        ∃ i : Fin 3, pderiv i F ∉ p.asHomogeneousIdeal.toIdeal) :
    ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0 := by
  intro v hv hzero
  obtain ⟨i, hi⟩ := hgrad (vectorProjectivePoint v hv)
    ((mem_vectorProjectivePoint_iff v hv F d hF).mpr hzero)
  refine ⟨i, ?_⟩
  intro hderiv
  exact hi ((mem_vectorProjectivePoint_iff v hv (pderiv i F) (d - 1)
    hF.pderiv).mpr hderiv)

end EvenQuinticConic
