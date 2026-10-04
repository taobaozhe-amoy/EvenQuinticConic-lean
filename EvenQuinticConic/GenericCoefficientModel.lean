import EvenQuinticConic.GradedRestriction
import EvenQuinticConic.SquareExtension
import EvenQuinticConic.WeightedRestriction
import EvenQuinticConic.FiniteDegreeRestriction

/-!
# Conic lifts from generic coefficients

The restriction homomorphism is constructed, not supplied as a free variable:
`X i ↦ C (f i) * X`. The quadratic identities are stated in the coefficient
field `L` with their common nonzero weight `u`. We prove that these data give
the homogeneous factorization and a rational ratio whose weighted square is
constant. Neither a square root of `u` nor a field extension is needed.

For geometric use, one must still obtain the coefficients from actual
sections, establish their independence and the restriction-kernel hypothesis,
and interpret the resulting ratio as a rational section of a line bundle.
-/

namespace EvenQuinticConic

open MvPolynomial

variable {σ K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]

/-- An actual graded restriction map and weighted generic product identities
suffice for the homogeneous linear-square factorization. -/
theorem generic_coefficient_conic_lifts_factor
    (f : σ → L) (F A B D : MvPolynomial σ K) (u α β : L)
    (hker : RingHom.ker (gradedRestriction f).toRingHom = Ideal.span {F})
    (hF : F.totalDegree = 5)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (hu : u ≠ 0) (hind : LinearIndependent K ![α, β])
    (hα : aeval f A = u * α ^ 2) (hαβ : aeval f B = u * α * β)
    (hβ : aeval f D = u * β ^ 2) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.IsHomogeneous 1 ∧ b.IsHomogeneous 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 := by
  have hind' : LinearIndependent K
      ![(Polynomial.C α * Polynomial.X : Polynomial L),
        Polynomial.C β * Polynomial.X] := by
    convert linearIndependent_C_mul_X K L ![α, β] hind using 1
    funext i
    fin_cases i <;> rfl
  apply weighted_homogeneous_conic_lifts_factor (gradedRestriction f) F A B D
    (Polynomial.C u) (Polynomial.C α * Polynomial.X) (Polynomial.C β * Polynomial.X)
    hker hF hA hB hD (by simpa using hu) hind'
  · rw [gradedRestriction_of_isHomogeneous f A 2 hA, hα]
    simp only [map_mul, map_pow]
    ring
  · rw [gradedRestriction_of_isHomogeneous f B 2 hB, hαβ]
    simp only [map_mul]
    ring
  · rw [gradedRestriction_of_isHomogeneous f D 2 hD, hβ]
    simp only [map_mul, map_pow]
    ring

/-- The factorization produces a nonzero rational ratio with constant
weighted square. This is the algebraic identity used in the local
nowhere-vanishing argument; no divisor or line bundle is defined here. -/
theorem generic_coefficient_factorization_with_ratio
    (f : σ → L) (F A B D : MvPolynomial σ K) (u α β : L)
    (hker : RingHom.ker (gradedRestriction f).toRingHom = Ideal.span {F})
    (hF : F.totalDegree = 5)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (hu : u ≠ 0) (hind : LinearIndependent K ![α, β])
    (hα : aeval f A = u * α ^ 2) (hαβ : aeval f B = u * α * β)
    (hβ : aeval f D = u * β ^ 2) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.IsHomogeneous 1 ∧ b.IsHomogeneous 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 ∧
      aeval f a ≠ 0 ∧ α / aeval f a ≠ 0 ∧
      u * (α / aeval f a) ^ 2 = algebraMap K L c := by
  obtain ⟨c, a, b, hc, ha, hb, hAE, hBE, hDE⟩ :=
    generic_coefficient_conic_lifts_factor f F A B D u α β hker hF
      hA hB hD hu hind hα hαβ hβ
  have hα0 : α ≠ 0 := by simpa using hind.ne_zero 0
  have heq : u * α ^ 2 = algebraMap K L c * (aeval f a) ^ 2 := by
    rw [← hα, hAE, map_mul, map_pow, aeval_C]
  have ha0 : aeval f a ≠ 0 := by
    intro hzero
    have : u * α ^ 2 = 0 := by simpa [hzero] using heq
    exact mul_ne_zero hu (pow_ne_zero 2 hα0) this
  refine ⟨c, a, b, hc, ha, hb, hAE, hBE, hDE, ha0, div_ne_zero hα0 ha0, ?_⟩
  rw [div_pow, ← mul_div_assoc, heq]
  exact mul_div_cancel_right₀ (algebraMap K L c) (pow_ne_zero 2 ha0)

/-- The same constant-ratio conclusion needs only injectivity on homogeneous
quartics, rather than the full principal-kernel description. -/
theorem generic_coefficient_ratio_of_quartic_injective
    (f : σ → L) (A B D : MvPolynomial σ K) (u α β : L)
    (h4 : ∀ P : MvPolynomial σ K, P.IsHomogeneous 4 → aeval f P = 0 → P = 0)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (hu : u ≠ 0) (hind : LinearIndependent K ![α, β])
    (hα : aeval f A = u * α ^ 2) (hαβ : aeval f B = u * α * β)
    (hβ : aeval f D = u * β ^ 2) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.IsHomogeneous 1 ∧ b.IsHomogeneous 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 ∧
      aeval f a ≠ 0 ∧ α / aeval f a ≠ 0 ∧
      u * (α / aeval f a) ^ 2 = algebraMap K L c := by
  obtain ⟨c, a, b, hc, ha, hb, hAE, hBE, hDE⟩ :=
    conic_lifts_factor_of_quartic_injective f A B D u α β h4
      hA hB hD hu hind hα hαβ hβ
  have hα0 : α ≠ 0 := by simpa using hind.ne_zero 0
  have heq : u * α ^ 2 = algebraMap K L c * (aeval f a) ^ 2 := by
    rw [← hα, hAE, map_mul, map_pow, aeval_C]
  have ha0 : aeval f a ≠ 0 := by
    intro hzero
    have : u * α ^ 2 = 0 := by simpa [hzero] using heq
    exact mul_ne_zero hu (pow_ne_zero 2 hα0) this
  refine ⟨c, a, b, hc, ha, hb, hAE, hBE, hDE, ha0, div_ne_zero hα0 ha0, ?_⟩
  rw [div_pow, ← mul_div_assoc, heq]
  exact mul_div_cancel_right₀ (algebraMap K L c) (pow_ne_zero 2 ha0)

end EvenQuinticConic
