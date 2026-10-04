import Mathlib.RingTheory.Ideal.Height
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FinCases

/-!
# The height of the origin in affine three-space

The origin ideal has height at least three, witnessed by the prime chain
`(0) < (X₀) < (X₀,X₁) < (X₀,X₁,X₂)`.
The intermediate ideals are defined as kernels of actual substitutions.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial

/-- The maximal ideal of the origin of affine three-space has height at least three. -/
theorem planeOriginIdeal_height_ge_three (K : Type*) [Field K] :
    (3 : ℕ∞) ≤ (RingHom.ker (MvPolynomial.eval (0 : Fin 3 → K))).height := by
  let f₁ : (MvPolynomial (Fin 3) K) →+* (MvPolynomial (Fin 3) K) := eval₂Hom C (fun i => if i = 0 then 0 else X i)
  let f₂ : (MvPolynomial (Fin 3) K) →+* (MvPolynomial (Fin 3) K) := eval₂Hom C (fun i => if i = 2 then X i else 0)
  let e : (MvPolynomial (Fin 3) K) →+* K := eval (0 : Fin 3 → K)
  let p₁ := RingHom.ker f₁
  let p₂ := RingHom.ker f₂
  let m := RingHom.ker e
  haveI : (⊥ : Ideal (MvPolynomial (Fin 3) K)).IsPrime := Ideal.bot_prime
  haveI : p₁.IsPrime := RingHom.ker_isPrime f₁
  haveI : p₂.IsPrime := RingHom.ker_isPrime f₂
  haveI : m.IsPrime := RingHom.ker_isPrime e
  have h₁₂ : f₂.comp f₁ = f₂ := by
    ext i : 1
    · ext r
      simp [f₁, f₂]
    · fin_cases i <;> simp [f₁, f₂]
  have h₂e : e.comp f₂ = e := by
    ext i : 1
    · ext r
      simp [e, f₂]
    · fin_cases i <;> simp [e, f₂]
  have h₀₁ : (⊥ : Ideal (MvPolynomial (Fin 3) K)) < p₁ := by
    refine lt_of_le_of_ne bot_le ?_
    intro h
    have hx : (X (0 : Fin 3) : (MvPolynomial (Fin 3) K)) ∈ p₁ := by simp [p₁, f₁, RingHom.mem_ker]
    rw [← h, Ideal.mem_bot] at hx
    exact X_ne_zero (0 : Fin 3) hx
  have h₁₂' : p₁ < p₂ := by
    refine lt_of_le_of_ne ?_ ?_
    · intro p hp
      change f₂ p = 0
      change f₁ p = 0 at hp
      calc
        f₂ p = f₂ (f₁ p) := (RingHom.congr_fun h₁₂ p).symm
        _ = 0 := by rw [hp, map_zero]
    · intro h
      have hx : (X (1 : Fin 3) : (MvPolynomial (Fin 3) K)) ∈ p₂ := by simp [p₂, f₂, RingHom.mem_ker]
      rw [← h] at hx
      simp [p₁, f₁, RingHom.mem_ker] at hx
  have h₂m : p₂ < m := by
    refine lt_of_le_of_ne ?_ ?_
    · intro p hp
      change e p = 0
      change f₂ p = 0 at hp
      calc
        e p = e (f₂ p) := (RingHom.congr_fun h₂e p).symm
        _ = 0 := by rw [hp, map_zero]
    · intro h
      have hx : (X (2 : Fin 3) : (MvPolynomial (Fin 3) K)) ∈ m := by simp [m, e, RingHom.mem_ker]
      rw [← h] at hx
      simp [p₂, f₂, RingHom.mem_ker] at hx
  have h₁ := Ideal.primeHeight_add_one_le_of_lt h₀₁
  have h₂ := Ideal.primeHeight_add_one_le_of_lt h₁₂'
  have h₃ := Ideal.primeHeight_add_one_le_of_lt h₂m
  have hz : (⊥ : Ideal (MvPolynomial (Fin 3) K)).primeHeight = 0 := by
    rw [← Ideal.height_eq_primeHeight, Ideal.height_bot]
  rw [hz, zero_add] at h₁
  have h₂' : (2 : ℕ∞) ≤ p₂.primeHeight := by
    exact (add_le_add_right h₁ 1).trans h₂
  have h₃' : (3 : ℕ∞) ≤ m.primeHeight := by
    exact (add_le_add_right h₂' 1).trans h₃
  simpa only [Ideal.height_eq_primeHeight] using h₃'

end EvenQuinticConic
