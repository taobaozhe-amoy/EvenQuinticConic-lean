import EvenQuinticConic.HomogeneousLocalizationSections

/-!
# Homogeneous representatives after clearing a linear denominator

A nonzero homogeneous linear form is outside the defining principal ideal
of a plane hypersurface of degree greater than one. Once an actual identity
in the cone quotient clears a power of that linear form, homogeneous
projection extracts a representative of the desired degree.

The quotient identity is ordinary algebraic input, not a hypothesis about
surjectivity of a projective section map. No identification of the cone
function field with the projective curve function field is used.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

/-- Every nonzero homogeneous linear form avoids a principal ideal whose
generator has total degree greater than one. -/
theorem plane_linear_not_mem_principal (F L : PlanePolynomial K)
    (hFdeg : 1 < F.totalDegree) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) :
    L ∉ Ideal.span {F} := by
  intro hmem
  have hF0 : F ≠ 0 := by
    intro hzero
    simp [hzero] at hFdeg
  exact hL0 (eq_zero_of_dvd_of_totalDegree_lt F L hF0
    (Ideal.mem_span_singleton.mp hmem) (lt_of_le_of_lt hL.totalDegree_le hFdeg))

/-- The image of a nonzero homogeneous linear form remains nonzero in the
actual cone quotient. -/
theorem plane_cone_linear_ne_zero (F L : PlanePolynomial K)
    (hFdeg : 1 < F.totalDegree) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) :
    Ideal.Quotient.mk (Ideal.span {F}) L ≠ 0 := by
  intro hzero
  exact plane_linear_not_mem_principal F L hFdeg hL hL0
    ((Ideal.Quotient.eq_zero_iff_mem).mp hzero)

/-- Projection to the required homogeneous component gives a representative
after clearing a power of any nonzero linear form, not just a coordinate.
The prime ideal permits cancellation of the chosen denominator. -/
theorem plane_cone_linear_homogeneous_representative
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    [(Ideal.span {F}).IsPrime] (hFdeg : 1 < F.totalDegree)
    (L : PlanePolynomial K) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (m d : ℕ) (A : PlanePolynomial K) (hA : A.IsHomogeneous (m + d))
    (c : PlaneConeQuotient F)
    (h : (Ideal.Quotient.mk (Ideal.span {F}) L) ^ m * c =
      Ideal.Quotient.mk (Ideal.span {F}) A) :
    ∃ P : PlanePolynomial K, P.IsHomogeneous d ∧
      Ideal.Quotient.mk (Ideal.span {F}) P = c := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hi : L ^ m * g - A ∈ Ideal.span {F} := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simp only [map_sub, map_mul, map_pow, h, sub_self]
  have hic := (planeHomogeneousPrincipal F e hF).isHomogeneous (m + d) hi
  change GradedRing.proj (homogeneousSubmodule (Fin 3) K) (m + d)
    (L ^ m * g - A) ∈ Ideal.span {F} at hic
  have hmono : (L ^ m).IsHomogeneous m := by
    simpa using hL.pow m
  have hh : GradedRing.proj (homogeneousSubmodule (Fin 3) K) (m + d) (L ^ m * g) =
      L ^ m * GradedRing.proj (homogeneousSubmodule (Fin 3) K) d g :=
    DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (Fin 3) K) hmono
  have hAp : GradedRing.proj (homogeneousSubmodule (Fin 3) K) (m + d) A = A :=
    DirectSum.decompose_of_mem_same (homogeneousSubmodule (Fin 3) K) hA
  rw [map_sub, hh, hAp] at hic
  have hdiv : L ^ m * (g - GradedRing.proj (homogeneousSubmodule (Fin 3) K) d g) ∈
      Ideal.span {F} := by
    convert (Ideal.span {F}).sub_mem hi hic using 1
    ring
  have hLpow : L ^ m ∉ Ideal.span {F} := by
    intro hp
    exact plane_linear_not_mem_principal F L hFdeg hL hL0
      (Ideal.IsPrime.mem_of_pow_mem inferInstance m hp)
  have hdiff : g - GradedRing.proj (homogeneousSubmodule (Fin 3) K) d g ∈
      Ideal.span {F} :=
    ((inferInstance : (Ideal.span {F}).IsPrime).mem_or_mem hdiv).resolve_left hLpow
  refine ⟨GradedRing.proj (homogeneousSubmodule (Fin 3) K) d g,
    (DirectSum.decompose (homogeneousSubmodule (Fin 3) K) g d).property, ?_⟩
  apply (Ideal.Quotient.eq).mpr
  simpa only [neg_sub] using (Ideal.span {F}).neg_mem hdiff

/-- Degree-two specialization for an arbitrary nonzero linear denominator. -/
theorem plane_cone_linear_quadratic_representative
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    [(Ideal.span {F}).IsPrime] (hFdeg : 1 < F.totalDegree)
    (L : PlanePolynomial K) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (m : ℕ) (A : PlanePolynomial K) (hA : A.IsHomogeneous (m + 2))
    (c : PlaneConeQuotient F)
    (h : (Ideal.Quotient.mk (Ideal.span {F}) L) ^ m * c =
      Ideal.Quotient.mk (Ideal.span {F}) A) :
    ∃ P : PlanePolynomial K, P.IsHomogeneous 2 ∧
      Ideal.Quotient.mk (Ideal.span {F}) P = c :=
  plane_cone_linear_homogeneous_representative F e hF hFdeg L hL hL0 m 2 A hA c h

end EvenQuinticConic
