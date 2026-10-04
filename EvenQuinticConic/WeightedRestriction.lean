import EvenQuinticConic.RestrictionModel

/-!
# Restriction identities with a common nonzero weight

Trivializing the square of a line bundle introduces a common factor `u` in
the three quadratic identities.  One must not silently assume that factor
is a square in the function field.  This file keeps `u` explicit and proves
the conic factorization without adjoining a square root of `u`.

All homomorphisms and elements below are actual algebraic objects.  Their
construction from a curve and its line bundles is a separate obligation.
-/

namespace EvenQuinticConic

open MvPolynomial

variable {σ K R : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]

omit [IsDomain R] in
/-- A common weight in the three product identities preserves the rank-one
relation in the restriction kernel. -/
theorem conic_relation_mem_ideal_of_weighted_restriction
    (φ : MvPolynomial σ K →ₐ[K] R) (F A B D : MvPolynomial σ K) (u s t : R)
    (hker : RingHom.ker φ.toRingHom = Ideal.span {F})
    (hA : φ A = u * s ^ 2) (hB : φ B = u * s * t) (hD : φ D = u * t ^ 2) :
    A * D - B ^ 2 ∈ Ideal.span {F} := by
  rw [← hker, RingHom.mem_ker]
  change φ (A * D - B ^ 2) = 0
  rw [map_sub, map_mul, map_pow, hA, hB, hD]
  ring

/-- Nonzero weight and independent elements force nonzero square lifts. -/
theorem weighted_square_lifts_ne_zero_of_linearIndependent
    (φ : MvPolynomial σ K →ₐ[K] R) (A D : MvPolynomial σ K) (u s t : R)
    (hu : u ≠ 0) (hind : LinearIndependent K ![s, t])
    (hA : φ A = u * s ^ 2) (hD : φ D = u * t ^ 2) : A ≠ 0 ∧ D ≠ 0 := by
  have hs : s ≠ 0 := by simpa using hind.ne_zero 0
  have ht : t ≠ 0 := by simpa using hind.ne_zero 1
  constructor
  · intro hA0
    apply mul_ne_zero hu (pow_ne_zero 2 hs)
    rw [← hA, hA0, map_zero]
  · intro hD0
    apply mul_ne_zero hu (pow_ne_zero 2 ht)
    rw [← hD, hD0, map_zero]

/-- Cancellation of the common weight reduces proportional lifts to
proportional squares of the independent elements. -/
theorem weighted_square_lifts_not_scalar_proportional [IsAlgClosed K]
    (φ : MvPolynomial σ K →ₐ[K] R) (A D : MvPolynomial σ K) (u s t : R)
    (hu : u ≠ 0) (hind : LinearIndependent K ![s, t])
    (hA : φ A = u * s ^ 2) (hD : φ D = u * t ^ 2) :
    ¬ ∃ c : K, A = C c * D := by
  rintro ⟨c, hc⟩
  apply squares_not_scalar_proportional_of_linearIndependent s t hind
  refine ⟨c, ?_⟩
  apply mul_left_cancel₀ hu
  have himage := congrArg φ hc
  simp only [map_mul, algHom_C, hA, hD] at himage
  calc
    u * s ^ 2 = algebraMap K R c * (u * t ^ 2) := himage
    _ = u * (algebraMap K R c * t ^ 2) := by ring

/-- The homogeneous conic classification works with a common weight; it
does not require that weight to be a square in the restriction algebra. -/
theorem weighted_homogeneous_conic_lifts_factor [IsAlgClosed K]
    (φ : MvPolynomial σ K →ₐ[K] R) (F A B D : MvPolynomial σ K) (u s t : R)
    (hker : RingHom.ker φ.toRingHom = Ideal.span {F})
    (hF : F.totalDegree = 5)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (hu : u ≠ 0) (hind : LinearIndependent K ![s, t])
    (hφA : φ A = u * s ^ 2) (hφB : φ B = u * s * t) (hφD : φ D = u * t ^ 2) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.IsHomogeneous 1 ∧ b.IsHomogeneous 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 := by
  obtain ⟨hA0, hD0⟩ :=
    weighted_square_lifts_ne_zero_of_linearIndependent φ A D u s t hu hind hφA hφD
  exact nonproportional_homogeneous_conics_from_quintic_ideal F A B D hF hA0 hD0
    hA hB hD
    (conic_relation_mem_ideal_of_weighted_restriction φ F A B D u s t hker hφA hφB hφD)
    (weighted_square_lifts_not_scalar_proportional φ A D u s t hu hind hφA hφD)

end EvenQuinticConic
