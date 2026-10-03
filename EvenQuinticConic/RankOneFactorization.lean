import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Factorization of a symmetric matrix of rank at most one

The relation `A * D = B ^ 2`, with `A ≠ 0`, admits the parametrization
`A = h * a ^ 2`, `B = h * a * b`, `D = h * b ^ 2` in a gcd domain.
In fact only the multiplicative gcd-monoid structure is needed.

This is the algebraic factorization step in the proposed argument about
three quadratic polynomials.  It does not make a claim about sheaf sections,
their lifts to polynomials, or theta characteristics.
-/

namespace EvenQuinticConic

variable {R : Type*} [CancelCommMonoidWithZero R] [GCDMonoid R]

/-- The square-product relation gives a common factor and two relatively
prime parameters.  The assumption `B ≠ 0` is not necessary. -/
theorem exists_reduced_rankOne_factorization_of_mul_eq_sq
    {A B D : R} (hA : A ≠ 0) (hrel : A * D = B ^ 2) :
    ∃ h a b : R, h ≠ 0 ∧ a ≠ 0 ∧ IsRelPrime a b ∧
      A = h * a ^ 2 ∧ B = h * a * b ∧ D = h * b ^ 2 := by
  obtain ⟨a, b, hAa, hBb, habUnit⟩ := extract_gcd A B
  let g := gcd A B
  have hAa' : A = g * a := hAa
  have hBb' : B = g * b := hBb
  have hg : g ≠ 0 := by
    intro hg0
    apply hA
    simp [hAa', hg0]
  have ha : a ≠ 0 := by
    intro ha0
    apply hA
    simp [hAa', ha0]
  have hab : IsRelPrime a b := gcd_isUnit_iff_isRelPrime.mp habUnit
  have hred : a * D = g * b ^ 2 := by
    apply mul_left_cancel₀ hg
    calc
      g * (a * D) = A * D := by rw [hAa']; ac_rfl
      _ = B ^ 2 := hrel
      _ = g * (g * b ^ 2) := by rw [hBb']; simp [pow_two, mul_assoc, mul_left_comm]
  have hag : a ∣ g := by
    apply (hab.mul_right hab).dvd_of_dvd_mul_right
    rw [← pow_two, ← hred]
    exact dvd_mul_right a D
  obtain ⟨h, hgh⟩ := hag
  have hh : h ≠ 0 := by
    intro hh0
    apply hg
    simp [hgh, hh0]
  refine ⟨h, a, b, hh, ha, hab, ?_, ?_, ?_⟩
  · rw [hAa', hgh]
    simp [pow_two, mul_left_comm, mul_comm]
  · rw [hBb', hgh]
    simp [mul_left_comm, mul_comm]
  · apply mul_left_cancel₀ ha
    rw [hred, hgh]
    ac_rfl

/-- A symmetric `2 × 2` matrix with zero determinant and a nonzero first
entry has a common-factor rank-one parametrization. -/
theorem exists_rankOne_factorization_of_mul_eq_sq
    {A B D : R} (hA : A ≠ 0) (hrel : A * D = B ^ 2) :
    ∃ h a b : R, A = h * a ^ 2 ∧ B = h * a * b ∧ D = h * b ^ 2 := by
  obtain ⟨h, a, b, _, _, _, hA', hB', hD'⟩ :=
    exists_reduced_rankOne_factorization_of_mul_eq_sq hA hrel
  exact ⟨h, a, b, hA', hB', hD'⟩

/-- The same parametrization holds even when the first matrix entry is zero.
That case forces `B = 0` and is parametrized by `(h,a,b) = (D,0,1)`. -/
theorem exists_rankOne_factorization_of_mul_eq_sq_unrestricted
    {A B D : R} (hrel : A * D = B ^ 2) :
    ∃ h a b : R, A = h * a ^ 2 ∧ B = h * a * b ∧ D = h * b ^ 2 := by
  by_cases hA : A = 0
  · have hB : B = 0 := by simpa [hA] using hrel.symm
    subst A
    subst B
    exact ⟨D, 0, 1, by simp, by simp, by simp⟩
  · exact exists_rankOne_factorization_of_mul_eq_sq hA hrel

end EvenQuinticConic
