import EvenQuinticConic.HomogeneousFactors
import EvenQuinticConic.ProjectiveJacobianPoints
import EvenQuinticConic.HomogeneousCommonZero
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# A nonsingular homogeneous plane equation is irreducible

The hypothesis concerns the given equation and its actual partial derivatives
at nonzero vectors over the algebraically closed field. It is stronger than
smoothness of its reduced zero locus: taking a power does not satisfy it.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

/-- Two factors vanishing at the same vector force every partial derivative
of their product to vanish at that vector. -/
theorem eval_pderiv_mul_eq_zero_of_common_zero (G H : PlanePolynomial K)
    (v : Fin 3 → K) (hG : eval v G = 0) (hH : eval v H = 0) (i : Fin 3) :
    eval v (pderiv i (G * H)) = 0 := by
  simp [hG, hH]

variable [IsAlgClosed K]

/-- The rational Jacobian criterion rules out a nontrivial factorization of a
positive-degree homogeneous plane equation over an algebraically closed field. -/
theorem plane_irreducible_of_jacobian (F : PlanePolynomial K) (d : ℕ)
    (hF : F.IsHomogeneous d) (hFdeg : 0 < F.totalDegree)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0) : Irreducible F := by
  have hF0 : F ≠ 0 := by intro hz; simp [hz] at hFdeg
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdeg := (isUnit_iff_totalDegree_of_isReduced.mp hunit).2
    omega
  · intro G H hfactor
    by_contra hunit
    push_neg at hunit
    obtain ⟨A, B, a, b, ha, hb, hA, hB, hAB⟩ :=
      homogeneous_positive_factorization_of_nontrivial F G H d hF hF0 hfactor
        hunit.1 hunit.2
    obtain ⟨v, hv, hvA, hvB⟩ := homogeneous_ternary_common_zero A B hA hB ha hb
    obtain ⟨i, hi⟩ := hJac v hv (by simp [hAB, hvA])
    exact hi (hAB ▸ eval_pderiv_mul_eq_zero_of_common_zero A B v hvA hvB i)

/-- The Jacobian hypothesis supplies primality of the actual homogeneous
principal ideal, without any independent primality assumption. -/
theorem plane_principal_isPrime_of_jacobian (F : PlanePolynomial K) (d : ℕ)
    (hF : F.IsHomogeneous d) (hFdeg : 0 < F.totalDegree)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0) : (Ideal.span {F}).IsPrime :=
  plane_principal_isPrime_of_irreducible F
    (plane_irreducible_of_jacobian F d hF hFdeg hJac)

/-- Nonsingularity of the equation on the actual projective spectrum implies
irreducibility of that equation. -/
theorem plane_irreducible_of_projective_gradient (F : PlanePolynomial K) (d : ℕ)
    (hF : F.IsHomogeneous d) (hFdeg : 0 < F.totalDegree)
    (hgrad : ∀ p : ProjectiveSpectrum (homogeneousSubmodule (Fin 3) K),
      F ∈ p.asHomogeneousIdeal.toIdeal →
        ∃ i : Fin 3, pderiv i F ∉ p.asHomogeneousIdeal.toIdeal) : Irreducible F :=
  plane_irreducible_of_jacobian F d hF hFdeg
    (rational_jacobian_of_projective_gradient F d hF hgrad)

/-- The projective gradient condition supplies the prime-ideal hypothesis
used in the actual scheme, section, and theta constructions. -/
theorem plane_principal_isPrime_of_projective_gradient (F : PlanePolynomial K) (d : ℕ)
    (hF : F.IsHomogeneous d) (hFdeg : 0 < F.totalDegree)
    (hgrad : ∀ p : ProjectiveSpectrum (homogeneousSubmodule (Fin 3) K),
      F ∈ p.asHomogeneousIdeal.toIdeal →
        ∃ i : Fin 3, pderiv i F ∉ p.asHomogeneousIdeal.toIdeal) : (Ideal.span {F}).IsPrime :=
  plane_principal_isPrime_of_irreducible F
    (plane_irreducible_of_projective_gradient F d hF hFdeg hgrad)

end EvenQuinticConic
