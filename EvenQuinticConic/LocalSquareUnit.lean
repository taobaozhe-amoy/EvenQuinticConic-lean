import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Roots of units in the fraction field of an integrally closed domain

If a positive power of a rational function is a unit in an integrally closed
domain, then the rational function itself comes from a unit in that domain.
For a normal local ring, this is the local algebra needed to extend a
rational section whose square is nowhere vanishing.  The statements here use
actual rings, fraction fields and units.  They do not construct a scheme,
line bundle, rational section or gluing datum.
-/

namespace EvenQuinticConic

variable {A L : Type*} [CommRing A] [IsIntegrallyClosed A]
  [Field L] [Algebra A L] [IsFractionRing A L]

/-- A positive-power root in the fraction field of a unit in an integrally
closed domain is already a unit of the domain, with the same power relation. -/
theorem exists_unit_of_fraction_pow_eq_unit (x : L) (u : Aˣ) {n : ℕ}
    (hn : 0 < n) (hx : x ^ n = algebraMap A L (u : A)) :
    ∃ v : Aˣ, algebraMap A L (v : A) = x ∧ v ^ n = u := by
  have hint : IsIntegral A (x ^ n) := by
    rw [hx]
    exact isIntegral_algebraMap
  obtain ⟨y, hy⟩ :=
    IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn hint
  have hyn : y ^ n = (u : A) := by
    apply IsFractionRing.injective A L
    simpa only [map_pow, hy] using hx
  have hyunit : IsUnit y :=
    (isUnit_pow_iff (Nat.ne_of_gt hn)).mp (hyn.symm ▸ u.isUnit)
  obtain ⟨v, hv⟩ := hyunit
  refine ⟨v, ?_, ?_⟩
  · simpa only [hv] using hy
  · apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hv] using hyn

/-- In particular, a square root of a unit in the fraction field extends to
a unit of the integrally closed domain. -/
theorem exists_unit_of_fraction_sq_eq_unit (x : L) (u : Aˣ)
    (hx : x ^ 2 = algebraMap A L (u : A)) :
    ∃ v : Aˣ, algebraMap A L (v : A) = x ∧ v ^ 2 = u :=
  exists_unit_of_fraction_pow_eq_unit x u (by decide) hx

/-- A unit coefficient can be absorbed into the unit on the other side.
This form allows a local trivialization of a tensor power to differ by a
unit from the chosen trivialization of its image. -/
theorem exists_unit_of_unit_mul_fraction_pow_eq_unit (x : L) (u v : Aˣ)
    {n : ℕ} (hn : 0 < n)
    (hx : algebraMap A L (u : A) * x ^ n = algebraMap A L (v : A)) :
    ∃ w : Aˣ, algebraMap A L (w : A) = x ∧ u * w ^ n = v := by
  have hpower : x ^ n = algebraMap A L ((u⁻¹ * v : Aˣ) : A) := by
    calc
      x ^ n = algebraMap A L ((u⁻¹ : Aˣ) : A) *
          (algebraMap A L (u : A) * x ^ n) := by
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      _ = algebraMap A L ((u⁻¹ : Aˣ) : A) * algebraMap A L (v : A) := by rw [hx]
      _ = algebraMap A L ((u⁻¹ * v : Aˣ) : A) := by
        rw [Units.val_mul, map_mul]
  obtain ⟨w, hw, hwpow⟩ := exists_unit_of_fraction_pow_eq_unit x (u⁻¹ * v) hn hpower
  refine ⟨w, hw, ?_⟩
  rw [hwpow, ← mul_assoc, mul_inv_cancel, one_mul]

/-- The square version of the preceding theorem: a rational local section
whose square differs from a unit by a unit coefficient extends to a unit. -/
theorem exists_unit_of_unit_mul_fraction_sq_eq_unit (x : L) (u v : Aˣ)
    (hx : algebraMap A L (u : A) * x ^ 2 = algebraMap A L (v : A)) :
    ∃ w : Aˣ, algebraMap A L (w : A) = x ∧ u * w ^ 2 = v :=
  exists_unit_of_unit_mul_fraction_pow_eq_unit x u v (by decide) hx

/-- A quotient of rational sections is a local unit when their squares
differ by units. The denominator need not itself be a local unit: this is
the cancellation needed at a common zero of the two regular sections. -/
theorem exists_unit_of_unit_mul_fraction_sq_eq_unit_mul_sq
    (x y : L) (hy : y ≠ 0) (u v : Aˣ)
    (hxy : algebraMap A L (u : A) * x ^ 2 =
      algebraMap A L (v : A) * y ^ 2) :
    ∃ w : Aˣ, algebraMap A L (w : A) = x / y ∧ u * w ^ 2 = v := by
  apply exists_unit_of_unit_mul_fraction_sq_eq_unit (x / y) u v
  rw [div_pow, ← mul_div_assoc, hxy]
  exact mul_div_cancel_right₀ (algebraMap A L (v : A)) (pow_ne_zero 2 hy)

end EvenQuinticConic
