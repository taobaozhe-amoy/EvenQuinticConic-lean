import EvenQuinticConic.PlaneResidueTransition

/-!
# Residue transition when the radial derivative changes

Euler's identity and the genuine cotangent relation give the remaining
cross-chart identity for quintic residue forms. All identities are valid
over arbitrary commutative rings, without dividing by the degree. They
concern actual Kähler differentials, not a postulated adjunction map.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial
open scoped BigOperators

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M]

/-- Euler's identity evaluated on a normalized plane hypersurface chart.
No characteristic restriction is required because the equation itself vanishes. -/
theorem planeChart_euler_relation
    (F : MvPolynomial (Fin 3) R) {d : ℕ} (hF : F.IsHomogeneous d)
    (v : Fin 3 → S) (i j k : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hvi : v i = 1) (hvF : aeval v F = 0) :
    aeval v (pderiv i F) + v j * aeval v (pderiv j F) +
      v k * aeval v (pderiv k F) = 0 := by
  have h := congrArg (aeval v) hF.sum_X_mul_pderiv
  simp only [map_sum, map_mul, aeval_X, map_nsmul, hvF, nsmul_zero] at h
  have huniv : (Finset.univ : Finset (Fin 3)) = {i, j, k} := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    omega
  rw [huniv] at h
  simpa only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, hji, hki, hkj, Ne.symm hji, Ne.symm hki, Ne.symm hkj,
    not_false_eq_true, or_self, hvi, one_mul, add_assoc] using h

/-- The module calculation for cross-chart residue forms, with every
cancellation justified by an actual unit. -/
theorem module_unit_residue_cross_transition
    (u p q : Sˣ) (a c : S) (m n z : M)
    (hd : (p : S) • m + c • n = 0)
    (he : (q : S) + (u : S) * (p : S) + a * c = 0)
    (hf : (u : S) ^ 2 • z = (u : S) • n - a • m) :
    -((↑(q * (u⁻¹) ^ 4)⁻¹ : S) • z) =
      (u : S) ^ 2 • ((↑p⁻¹ : S) • n) := by
  have hpm : (p : S) • m = -(c • n) := eq_neg_of_add_eq_zero_left hd
  have hc : (p : S) * (u : S) + a * c = -(q : S) := by
    rw [mul_comm]
    exact eq_neg_of_add_eq_zero_right (by simpa only [add_assoc] using he)
  have hrel : ((p : S) * (u : S) ^ 2) • z = -((q : S) • n) := by
    calc
      ((p : S) * (u : S) ^ 2) • z = (p : S) • ((u : S) ^ 2 • z) := by
        rw [smul_smul]
      _ = (p : S) • ((u : S) • n - a • m) := by rw [hf]
      _ = ((p : S) * (u : S)) • n - a • ((p : S) • m) := by
        rw [smul_sub, smul_smul, smul_smul, smul_smul, mul_comm (p : S) a]
      _ = ((p : S) * (u : S) + a * c) • n := by
        rw [hpm, smul_neg, sub_neg_eq_add, smul_smul, add_smul]
      _ = -((q : S) • n) := by rw [hc, neg_smul]
  have hpow : (u⁻¹) ^ 2 * u ^ 4 = u ^ 2 := by
    calc
      (u⁻¹) ^ 2 * u ^ 4 = ((u⁻¹) ^ 2 * u ^ 2) * u ^ 2 := by
        rw [mul_assoc, ← pow_add]
      _ = u ^ 2 := by rw [← mul_pow, inv_mul_cancel, one_pow, one_mul]
  have hl : (q * (u⁻¹) ^ 2 * p) * (q * (u⁻¹) ^ 4)⁻¹ = p * u ^ 2 := by
    calc
      (q * (u⁻¹) ^ 2 * p) * (q * (u⁻¹) ^ 4)⁻¹ =
          p * ((u⁻¹) ^ 2 * u ^ 4) := by
        simp [mul_inv_rev, inv_pow, mul_comm, mul_left_comm, mul_assoc]
      _ = p * u ^ 2 := by rw [hpow]
  have hr : (q * (u⁻¹) ^ 2 * p) * u ^ 2 * p⁻¹ = q := by
    calc
      (q * (u⁻¹) ^ 2 * p) * u ^ 2 * p⁻¹ =
          q * ((u⁻¹) ^ 2 * u ^ 2) := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      _ = q := by rw [← mul_pow, inv_mul_cancel, one_pow, mul_one]
  apply ((q * (u⁻¹) ^ 2 * p).isUnit.smul_left_cancel).mp
  rw [smul_neg, smul_smul, smul_smul, smul_smul]
  have hls := congrArg (fun t : Sˣ => (t : S)) hl
  have hrs := congrArg (fun t : Sˣ => (t : S)) hr
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hls hrs ⊢
  rw [hls, hrs, hrel, neg_neg]

/-- The inverse-coordinate quotient rule and the actual polynomial
relations identify the two residue forms when the derivative is radial
on the other chart. The first conjunct certifies the rescaled derivative. -/
theorem quintic_residue_transition_radial_derivatives
    (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 5)
    (v : Fin 3 → S) (i l k : Fin 3)
    (hli : l ≠ i) (hki : k ≠ i) (hkl : k ≠ l)
    (hvi : v i = 1) (hvF : aeval v F = 0)
    (u p q : Sˣ) (hu : (u : S) = v l)
    (hp : (p : S) = aeval v (pderiv l F))
    (hq : (q : S) = aeval v (pderiv i F)) :
    (↑(q * (u⁻¹) ^ 4) : S) =
        aeval (fun a => v a * (↑u⁻¹ : S)) (pderiv i F) ∧
      -((↑(q * (u⁻¹) ^ 4)⁻¹ : S) •
          KaehlerDifferential.D R S (v k * (↑u⁻¹ : S))) =
        (v l) ^ 2 • ((↑p⁻¹ : S) • KaehlerDifferential.D R S (v k)) := by
  refine ⟨quintic_scaled_derivative_unit F hF v i u q hq, ?_⟩
  have hd := planeChart_kaehler_relation F v i l k hli hki hkl hvi hvF
  have he := planeChart_euler_relation F hF v i l k hli hki hkl hvi hvF
  rw [← hp] at hd
  rw [← hq, ← hp, ← hu] at he
  have hf := derivation_fraction_identity (KaehlerDifferential.D R S)
    (v k) (u : S) (v k * (↑u⁻¹ : S)) (by
      rw [mul_assoc, Units.inv_mul, mul_one])
  have h := module_unit_residue_cross_transition u p q (v k)
    (aeval v (pderiv k F)) (KaehlerDifferential.D R S (v l))
    (KaehlerDifferential.D R S (v k))
    (KaehlerDifferential.D R S (v k * (↑u⁻¹ : S))) hd he (by simpa only [hu] using hf)
  simpa only [hu] using h

end EvenQuinticConic
