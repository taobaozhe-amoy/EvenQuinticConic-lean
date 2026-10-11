import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.FinCases

/-!
# Actual differential identities on plane hypersurface charts

The chain rule is proved for an arbitrary derivation and then applied to
the genuine universal Kähler derivation. On a chart with one coordinate
equal to one, differentiating the equation gives the two remaining terms.
These identities concern the original polynomial and actual differentials;
they do not postulate an adjunction isomorphism.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial
open scoped BigOperators

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M]

/-- The multivariable chain rule for an actual derivation of an algebra. -/
theorem derivation_aeval_mvPolynomial {σ : Type*} [Fintype σ]
    (D : Derivation R S M) (v : σ → S) (F : MvPolynomial σ R) :
    D (aeval v F) = ∑ i, aeval v (pderiv i F) • D (v i) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have hpdi (a : σ) : aeval v (pderiv a (p * X j)) =
        aeval v (pderiv a p) * v j + if j = a then aeval v p else 0 := by
      rw [pderiv_mul, map_add, map_mul, map_mul, aeval_X]
      by_cases h : j = a
      · subst a; simp
      · simp [pderiv_X_of_ne h, h]
    rw [map_mul, aeval_X, D.leibniz, hp]
    simp only [hpdi, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [add_comm]
    congr 1
    simp only [Finset.smul_sum, smul_smul, mul_comm]

/-- Differentiating a polynomial relation gives its actual cotangent relation. -/
theorem kaehler_relation_of_aeval_eq_zero {σ : Type*} [Fintype σ]
    (F : MvPolynomial σ R) (v : σ → S) (hF : aeval v F = 0) :
    ∑ i, aeval v (pderiv i F) • KaehlerDifferential.D R S (v i) = 0 := by
  rw [← derivation_aeval_mvPolynomial, hF, map_zero]

/-- On a dehomogenized plane chart the derivative of the constant coordinate
vanishes, leaving the two actual nonconstant-coordinate terms. -/
theorem planeChart_kaehler_relation
    (F : MvPolynomial (Fin 3) R) (v : Fin 3 → S)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hvi : v i = 1) (hF : aeval v F = 0) :
    aeval v (pderiv j F) • KaehlerDifferential.D R S (v j) +
      aeval v (pderiv k F) • KaehlerDifferential.D R S (v k) = 0 := by
  have h := kaehler_relation_of_aeval_eq_zero F v hF
  have huniv : (Finset.univ : Finset (Fin 3)) = {i, j, k} := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    omega
  rw [huniv] at h
  simpa only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, hji, hki, hkj, Ne.symm hji, Ne.symm hki, Ne.symm hkj,
    not_false_eq_true, or_self, hvi, Derivation.map_one_eq_zero, smul_zero, zero_add] using h

/-- The actual chart kernel supplies both equations used by the cotangent
relation; they need not be independent assumptions. -/
theorem planeChart_kaehler_relation_of_kernel
    (F : MvPolynomial (Fin 3) R) (v : Fin 3 → S)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1}) :
    aeval v (pderiv j F) • KaehlerDifferential.D R S (v j) +
      aeval v (pderiv k F) • KaehlerDifferential.D R S (v k) = 0 := by
  apply planeChart_kaehler_relation F v i j k hji hki hkj
  · have h : X i - 1 ∈ RingHom.ker (aeval (R := R) v) := by
      rw [hker]
      exact Ideal.subset_span (by simp)
    simpa [RingHom.mem_ker, sub_eq_zero] using h
  · change F ∈ RingHom.ker (aeval (R := R) v)
    rw [hker]
    exact Ideal.subset_span (by simp)

/-- On the overlap where both nonradial derivatives are units, the two
signed residue forms agree inside the actual Kähler differential module. -/
theorem planeChart_kaehler_residue_swap
    (F : MvPolynomial (Fin 3) R) (v : Fin 3 → S)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hvi : v i = 1) (hF : aeval v F = 0)
    (uj uk : Sˣ) (huj : (uj : S) = aeval v (pderiv j F))
    (huk : (uk : S) = aeval v (pderiv k F)) :
    (↑uj⁻¹ : S) • KaehlerDifferential.D R S (v k) =
      -((↑uk⁻¹ : S) • KaehlerDifferential.D R S (v j)) := by
  have h := planeChart_kaehler_relation F v i j k hji hki hkj hvi hF
  rw [← huj, ← huk] at h
  apply ((uj * uk).isUnit.smul_left_cancel).mp
  change ((uj : S) * (uk : S)) • _ = ((uj : S) * (uk : S)) • _
  rw [smul_neg, smul_smul, smul_smul]
  have hj : ((uj : S) * (uk : S)) * (↑uj⁻¹ : S) = (uk : S) := by
    rw [mul_right_comm, Units.mul_inv, one_mul]
  have hk : ((uj : S) * (uk : S)) * (↑uk⁻¹ : S) = (uj : S) := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [hj, hk]
  exact eq_neg_of_add_eq_zero_right h

/-- Clearing the denominator in the quotient rule only uses a product
identity, so it is valid in rings with zero divisors. -/
theorem derivation_fraction_identity (D : Derivation R S M)
    (a b c : S) (h : c * b = a) :
    (b ^ 2) • D c = b • D a - a • D b := by
  rw [← h, D.leibniz, smul_add, smul_smul, smul_smul, pow_two]
  simp only [mul_comm b c, add_sub_cancel_left]

/-- The derivative of an inverse unit, without assuming the ambient ring is a field. -/
theorem derivation_unit_inverse (D : Derivation R S M) (u : Sˣ) :
    D (↑u⁻¹ : S) = -((↑u⁻¹ : S) ^ 2 • D (u : S)) := by
  have h := derivation_fraction_identity D 1 (u : S) (↑u⁻¹ : S) u.inv_mul
  simp only [Derivation.map_one_eq_zero, smul_zero, one_smul, zero_sub] at h
  have h' := congrArg (fun m : M => (↑u⁻¹ : S) ^ 2 • m) h
  simpa only [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul, smul_neg] using h'

end EvenQuinticConic
