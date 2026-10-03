import Mathlib.RingTheory.MvPolynomial.Homogeneous
import EvenQuinticConic.ConicClassification

/-!
# Homogeneous linear factors of homogeneous conics

The preceding polynomial factorization only gives parameters of total degree
at most one.  This file proves that when the original conics are homogeneous
of degree two, the parameters are genuinely homogeneous linear polynomials:
their constant terms vanish.

All statements concern actual multivariate polynomials.  No construction of
sections of a theta characteristic, or identification of line bundles, is
asserted here.
-/

namespace EvenQuinticConic

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- A polynomial of degree at most one with zero constant term is homogeneous
of degree one.  This includes the zero polynomial. -/
theorem isHomogeneous_one_of_totalDegree_le_one_of_coeff_zero
    (a : MvPolynomial σ K) (hdeg : a.totalDegree ≤ 1)
    (hconst : a.coeff 0 = 0) : a.IsHomogeneous 1 := by
  intro d hd
  have hle : d.degree ≤ a.totalDegree := le_totalDegree (mem_support_iff.mpr hd)
  have hne : d.degree ≠ 0 := by
    intro hz
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hz
    apply hd
    simpa only [hd0] using hconst
  have hdegree : d.degree = 1 := by omega
  rw [Finsupp.degree_eq_weight_one] at hdegree
  exact hdegree

/-- If a nonzero scalar times the square of a polynomial of degree at most
one is a homogeneous conic, the polynomial is homogeneous linear. -/
theorem isHomogeneous_one_of_scalar_square_isHomogeneous_two
    (a : MvPolynomial σ K) (c : K) (hc : c ≠ 0)
    (hdeg : a.totalDegree ≤ 1) (hhom : (C c * a ^ 2).IsHomogeneous 2) :
    a.IsHomogeneous 1 := by
  have hcoeff : (C c * a ^ 2).coeff 0 = 0 :=
    hhom.coeff_eq_zero (by simp)
  have hprod : c * (constantCoeff a) ^ 2 = 0 := by
    change constantCoeff (C c * a ^ 2) = 0 at hcoeff
    simpa only [map_mul, map_pow, constantCoeff_C] using hcoeff
  have hzero : constantCoeff a = 0 :=
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod).resolve_left hc)
  exact isHomogeneous_one_of_totalDegree_le_one_of_coeff_zero a hdeg hzero

/-- The rank-one factorization of nonproportional homogeneous conics has
homogeneous linear factors, with a common nonzero field scalar. -/
theorem nonproportional_homogeneous_conics_factor_as_linear_squares
    (A B D : MvPolynomial σ K) (hA0 : A ≠ 0) (hD0 : D ≠ 0)
    (hA : A.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (hrel : A * D = B ^ 2) (hind : ¬ ∃ c : K, A = C c * D) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.IsHomogeneous 1 ∧ b.IsHomogeneous 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 := by
  obtain ⟨c, a, b, hc, hadeg, hbdeg, hAE, hBE, hDE⟩ :=
    nonproportional_conics_factor_as_linear_squares A B D hA0 hD0
      hA.totalDegree_le hD.totalDegree_le hrel hind
  have ha : a.IsHomogeneous 1 :=
    isHomogeneous_one_of_scalar_square_isHomogeneous_two a c hc hadeg
      (hAE ▸ hA)
  have hb : b.IsHomogeneous 1 :=
    isHomogeneous_one_of_scalar_square_isHomogeneous_two b c hc hbdeg
      (hDE ▸ hD)
  exact ⟨c, a, b, hc, ha, hb, hAE, hBE, hDE⟩

/-- Homogeneous conics satisfying the square-product relation modulo the
principal ideal of a quintic have homogeneous linear-square factors.

Membership in this ideal is an explicit algebraic hypothesis; it is not
being inferred here from a geometric restriction or vanishing condition.
-/
theorem nonproportional_homogeneous_conics_from_quintic_ideal
    (F A B D : MvPolynomial σ K)
    (hF : F.totalDegree = 5) (hA0 : A ≠ 0) (hD0 : D ≠ 0)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (hrel : A * D - B ^ 2 ∈ Ideal.span {F})
    (hind : ¬ ∃ c : K, A = C c * D) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.IsHomogeneous 1 ∧ b.IsHomogeneous 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 := by
  obtain ⟨c, a, b, hc, hadeg, hbdeg, hAE, hBE, hDE⟩ :=
    nonproportional_conics_from_quintic_ideal F A B D hF hA0 hD0
      hA.totalDegree_le hB.totalDegree_le hD.totalDegree_le hrel hind
  have ha : a.IsHomogeneous 1 :=
    isHomogeneous_one_of_scalar_square_isHomogeneous_two a c hc hadeg
      (hAE ▸ hA)
  have hb : b.IsHomogeneous 1 :=
    isHomogeneous_one_of_scalar_square_isHomogeneous_two b c hc hbdeg
      (hDE ▸ hD)
  exact ⟨c, a, b, hc, ha, hb, hAE, hBE, hDE⟩

end EvenQuinticConic
