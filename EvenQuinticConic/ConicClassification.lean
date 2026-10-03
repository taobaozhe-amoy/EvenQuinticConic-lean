import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import EvenQuinticConic.RankOneFactorization
import EvenQuinticConic.PolynomialDegree

/-!
# Degree consequences of a rank-one factorization of three conics

This file proves polynomial statements used in the proposed theta argument.
If `A = h * a^2` and `D = h * b^2` are nonzero polynomials of total degree at
most two, either they are scalar multiples or the common factor `h` is a
nonzero constant and `a,b` have total degree at most one.

These are statements about actual multivariate polynomials over a field. They
do not assert that any sections of a line bundle have been lifted to those
polynomials, or identify a theta characteristic with a hyperplane bundle.
Total degree at most one allows a constant term; homogeneity, where needed in
the geometric application, is an additional statement.
-/

namespace EvenQuinticConic

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- Exact degree of a nonzero common factor times a nonzero square. -/
theorem totalDegree_mul_sq_of_ne_zero (h a : MvPolynomial σ K)
    (hh : h ≠ 0) (ha : a ≠ 0) :
    (h * a ^ 2).totalDegree = h.totalDegree + 2 * a.totalDegree := by
  rw [pow_two, totalDegree_mul_of_isDomain hh (mul_ne_zero ha ha),
    totalDegree_mul_of_isDomain ha ha]
  omega

theorem rankOne_factor_degree_bounds (h a b : MvPolynomial σ K)
    (hh : h ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : (h * a ^ 2).totalDegree ≤ 2)
    (hD : (h * b ^ 2).totalDegree ≤ 2) :
    h.totalDegree + 2 * a.totalDegree ≤ 2 ∧
    h.totalDegree + 2 * b.totalDegree ≤ 2 ∧
    a.totalDegree ≤ 1 ∧ b.totalDegree ≤ 1 := by
  rw [totalDegree_mul_sq_of_ne_zero h a hh ha] at hA
  rw [totalDegree_mul_sq_of_ne_zero h b hh hb] at hD
  omega

/-- A nonconstant common factor forces both square roots to be constants. -/
theorem rankOne_factor_degree_dichotomy (h a b : MvPolynomial σ K)
    (hh : h ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : (h * a ^ 2).totalDegree ≤ 2)
    (hD : (h * b ^ 2).totalDegree ≤ 2) :
    h.totalDegree = 0 ∨ (a.totalDegree = 0 ∧ b.totalDegree = 0) := by
  have hbound := rankOne_factor_degree_bounds h a b hh ha hb hA hD
  omega

/-- Any two constant polynomials, with the second nonzero, are scalar multiples. -/
theorem exists_scalar_multiple_of_totalDegree_zero (a b : MvPolynomial σ K)
    (ha : a.totalDegree = 0) (hb : b.totalDegree = 0) (hb0 : b ≠ 0) :
    ∃ c : K, a = C c * b := by
  have haC := totalDegree_eq_zero_iff_eq_C.mp ha
  have hbC := totalDegree_eq_zero_iff_eq_C.mp hb
  have hbcoeff : b.coeff 0 ≠ 0 := by
    intro hz
    apply hb0
    rw [hbC, hz, map_zero]
  refine ⟨a.coeff 0 / b.coeff 0, ?_⟩
  rw [haC, hbC, ← map_mul]
  congr 1
  simpa using (div_mul_cancel₀ (a.coeff 0) hbcoeff).symm

/-- The full degree alternative for the two diagonal entries of a rank-one conic matrix. -/
theorem rankOne_conic_degree_classification (h a b : MvPolynomial σ K)
    (hh : h ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : (h * a ^ 2).totalDegree ≤ 2)
    (hD : (h * b ^ 2).totalDegree ≤ 2) :
    (∃ c : K, h * a ^ 2 = C c * (h * b ^ 2)) ∨
      (h.totalDegree = 0 ∧ a.totalDegree ≤ 1 ∧ b.totalDegree ≤ 1) := by
  obtain ⟨_, _, hadeg, hbdeg⟩ := rankOne_factor_degree_bounds h a b hh ha hb hA hD
  rcases rankOne_factor_degree_dichotomy h a b hh ha hb hA hD with hhdeg | ⟨ha0, hb0⟩
  · exact Or.inr ⟨hhdeg, hadeg, hbdeg⟩
  · obtain ⟨c, hc⟩ := exists_scalar_multiple_of_totalDegree_zero a b ha0 hb0 hb
    left
    refine ⟨c ^ 2, ?_⟩
    rw [hc, map_pow]
    ring

/-- Nonproportional conics have a constant common factor and linear square roots. -/
theorem rankOne_conic_constant_factor_of_not_scalar_multiple (h a b : MvPolynomial σ K)
    (hh : h ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : (h * a ^ 2).totalDegree ≤ 2)
    (hD : (h * b ^ 2).totalDegree ≤ 2)
    (hind : ¬ ∃ c : K, h * a ^ 2 = C c * (h * b ^ 2)) :
    ∃ c : K, c ≠ 0 ∧ h = C c ∧ a.totalDegree ≤ 1 ∧ b.totalDegree ≤ 1 := by
  have hdeg := (rankOne_conic_degree_classification h a b hh ha hb hA hD).resolve_left hind
  have hhC := totalDegree_eq_zero_iff_eq_C.mp hdeg.1
  refine ⟨h.coeff 0, ?_, hhC, hdeg.2⟩
  intro hc
  apply hh
  rw [hhC, hc, map_zero]

/-- An actual classification of nonproportional conics satisfying the square-product
relation: the common factor is a nonzero field scalar and the two parameters
have total degree at most one. -/
theorem nonproportional_conics_factor_as_linear_squares
    (A B D : MvPolynomial σ K) (hA0 : A ≠ 0) (hD0 : D ≠ 0)
    (hAdeg : A.totalDegree ≤ 2) (hDdeg : D.totalDegree ≤ 2)
    (hrel : A * D = B ^ 2) (hind : ¬ ∃ c : K, A = C c * D) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.totalDegree ≤ 1 ∧ b.totalDegree ≤ 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 := by
  letI := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial σ K)
  obtain ⟨h, a, b, hh, ha, _, hAE, hBE, hDE⟩ :=
    exists_reduced_rankOne_factorization_of_mul_eq_sq hA0 hrel
  have hb : b ≠ 0 := by
    intro hb0
    apply hD0
    simpa only [hb0, zero_pow (by decide : 2 ≠ 0), mul_zero] using hDE
  have hAd : (h * a ^ 2).totalDegree ≤ 2 := by
    simpa only [← hAE] using hAdeg
  have hDd : (h * b ^ 2).totalDegree ≤ 2 := by
    simpa only [← hDE] using hDdeg
  have hind' : ¬ ∃ c : K, h * a ^ 2 = C c * (h * b ^ 2) := by
    rintro ⟨c, hc⟩
    apply hind
    refine ⟨c, ?_⟩
    simpa only [hAE, hDE] using hc
  obtain ⟨c, hc, hhC, hadeg, hbdeg⟩ :=
    rankOne_conic_constant_factor_of_not_scalar_multiple h a b hh ha hb hAd hDd hind'
  rw [hhC] at hAE hBE hDE
  exact ⟨c, a, b, hc, hadeg, hbdeg, hAE, hBE, hDE⟩

/-- The combined polynomial step: a conic relation divisible by a quintic,
with nonproportional nonzero diagonal entries, has the explicit linear-square
form. This still does not supply any of the line-bundle interpretation. -/
theorem nonproportional_conics_from_quintic_relation
    (F A B D : MvPolynomial σ K)
    (hF : F.totalDegree = 5) (hA0 : A ≠ 0) (hD0 : D ≠ 0)
    (hAdeg : A.totalDegree ≤ 2) (hBdeg : B.totalDegree ≤ 2)
    (hDdeg : D.totalDegree ≤ 2)
    (hdiv : F ∣ A * D - B ^ 2) (hind : ¬ ∃ c : K, A = C c * D) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.totalDegree ≤ 1 ∧ b.totalDegree ≤ 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 := by
  apply nonproportional_conics_factor_as_linear_squares A B D hA0 hD0 hAdeg hDdeg
  · exact conic_relation_of_quintic_divisibility F A B D hF hAdeg hBdeg hDdeg hdiv
  · exact hind

/-- The same combined classification with the relation expressed as membership
in the actual principal ideal generated by the quintic. -/
theorem nonproportional_conics_from_quintic_ideal
    (F A B D : MvPolynomial σ K)
    (hF : F.totalDegree = 5) (hA0 : A ≠ 0) (hD0 : D ≠ 0)
    (hAdeg : A.totalDegree ≤ 2) (hBdeg : B.totalDegree ≤ 2)
    (hDdeg : D.totalDegree ≤ 2)
    (hrel : A * D - B ^ 2 ∈ Ideal.span ({F} : Set (MvPolynomial σ K)))
    (hind : ¬ ∃ c : K, A = C c * D) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.totalDegree ≤ 1 ∧ b.totalDegree ≤ 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 := by
  exact nonproportional_conics_from_quintic_relation F A B D hF hA0 hD0
    hAdeg hBdeg hDdeg (Ideal.mem_span_singleton.mp hrel) hind

end EvenQuinticConic
