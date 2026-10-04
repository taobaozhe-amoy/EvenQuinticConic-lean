import EvenQuinticConic.WeightedRestriction

/-!
# The conic argument needs only injectivity in degree four

The relation `A * D - B ^ 2` is a homogeneous quartic. Consequently the
classification of conic lifts does not require computing the whole kernel
of a restriction homomorphism: injectivity on homogeneous quartics suffices.

Here the restriction is the actual evaluation homomorphism at coefficients
`f : σ → L`. Evaluation is not asserted to be injective on all polynomials.
For geometric applications one must still construct the generic coefficients
and prove the stated injectivity on quartics from the curve.
-/

namespace EvenQuinticConic

open MvPolynomial

variable {σ K L : Type*} [Field K] [CommRing L] [IsDomain L] [Algebra K L]

omit [IsDomain L] in
/-- Injectivity only in homogeneous degree four upgrades the evaluated
weighted product relation to an equality of polynomials. -/
theorem conic_relation_of_quartic_injective
    (f : σ → L) (A B D : MvPolynomial σ K) (u α β : L)
    (h4 : ∀ P : MvPolynomial σ K, P.IsHomogeneous 4 → aeval f P = 0 → P = 0)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (hα : aeval f A = u * α ^ 2) (hαβ : aeval f B = u * α * β)
    (hβ : aeval f D = u * β ^ 2) :
    A * D = B ^ 2 := by
  apply sub_eq_zero.mp
  apply h4
  · exact (hA.mul hD).sub (hB.pow 2)
  · rw [map_sub, map_mul, map_pow, hα, hαβ, hβ]
    ring

/-- Homogeneous conic lifts of two independent coefficients factor as linear
squares using only injectivity of restriction on homogeneous quartics.
There is no hypothesis about a quintic equation or a full restriction kernel.
-/
theorem conic_lifts_factor_of_quartic_injective [IsAlgClosed K]
    (f : σ → L) (A B D : MvPolynomial σ K) (u α β : L)
    (h4 : ∀ P : MvPolynomial σ K, P.IsHomogeneous 4 → aeval f P = 0 → P = 0)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (hu : u ≠ 0) (hind : LinearIndependent K ![α, β])
    (hα : aeval f A = u * α ^ 2) (hαβ : aeval f B = u * α * β)
    (hβ : aeval f D = u * β ^ 2) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.IsHomogeneous 1 ∧ b.IsHomogeneous 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 := by
  obtain ⟨hA0, hD0⟩ := weighted_square_lifts_ne_zero_of_linearIndependent
    (aeval f) A D u α β hu hind hα hβ
  apply nonproportional_homogeneous_conics_factor_as_linear_squares A B D hA0 hD0 hA hD
  · exact conic_relation_of_quartic_injective f A B D u α β h4 hA hB hD hα hαβ hβ
  · exact weighted_square_lifts_not_scalar_proportional (aeval f) A D u α β hu hind hα hβ

end EvenQuinticConic
