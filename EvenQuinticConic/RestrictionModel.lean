import EvenQuinticConic.HomogeneousConics
import EvenQuinticConic.IndependentSquares

/-!
# A polynomial restriction model for the conic argument

This file uses an actual algebra homomorphism `φ : K[σ] →ₐ[K] R`, with an
explicitly specified kernel, and actual elements `s,t` of the domain `R`.
From `φ A = s²`, `φ B = s*t`, and `φ D = t²`, it derives the ideal relation
required by the polynomial classification.  Linear independence of `s,t`
supplies the nonzero and nonproportionality hypotheses.

No sheaf, line bundle, section ring, or generic trivialization is constructed
in this file.  Applying this theorem to geometric sections requires building
this algebra homomorphism and proving its kernel, image identities, and
linear independence, including all compatible choices of trivialization and
scalars.  The theorem below does not claim those geometric obligations have
been discharged.
-/

namespace EvenQuinticConic

open MvPolynomial

variable {σ K R : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]

omit [IsDomain R] in
/-- The three restriction identities imply that the conic relation lies in
the specified principal kernel. -/
theorem conic_relation_mem_ideal_of_restriction
    (φ : MvPolynomial σ K →ₐ[K] R) (F A B D : MvPolynomial σ K) (s t : R)
    (hker : RingHom.ker φ.toRingHom = Ideal.span {F})
    (hA : φ A = s ^ 2) (hB : φ B = s * t) (hD : φ D = t ^ 2) :
    A * D - B ^ 2 ∈ Ideal.span {F} := by
  rw [← hker, RingHom.mem_ker]
  change φ (A * D - B ^ 2) = 0
  rw [map_sub, map_mul, map_pow, hA, hB, hD]
  ring

/-- The square lifts of two independent elements cannot be zero. -/
theorem square_lifts_ne_zero_of_linearIndependent
    (φ : MvPolynomial σ K →ₐ[K] R) (A D : MvPolynomial σ K) (s t : R)
    (hind : LinearIndependent K ![s, t])
    (hA : φ A = s ^ 2) (hD : φ D = t ^ 2) : A ≠ 0 ∧ D ≠ 0 := by
  have hs : s ≠ 0 := by simpa using hind.ne_zero 0
  have ht : t ≠ 0 := by simpa using hind.ne_zero 1
  constructor
  · intro hA0
    apply pow_ne_zero 2 hs
    rw [← hA, hA0, map_zero]
  · intro hD0
    apply pow_ne_zero 2 ht
    rw [← hD, hD0, map_zero]

/-- Over an algebraically closed field, the two square lifts of independent
elements cannot be scalar multiples as polynomials. -/
theorem square_lifts_not_scalar_proportional_of_linearIndependent [IsAlgClosed K]
    (φ : MvPolynomial σ K →ₐ[K] R) (A D : MvPolynomial σ K) (s t : R)
    (hind : LinearIndependent K ![s, t])
    (hA : φ A = s ^ 2) (hD : φ D = t ^ 2) :
    ¬ ∃ c : K, A = C c * D := by
  rintro ⟨c, hc⟩
  apply squares_not_scalar_proportional_of_linearIndependent s t hind
  refine ⟨c, ?_⟩
  have himage := congrArg φ hc
  simpa only [map_mul, algHom_C, hA, hD] using himage

/-- A complete algebraic implication from an actual restriction map to the
homogeneous linear-square factorization of its conic lifts.

The inputs involving `φ`, its kernel, and the independent elements `s,t` are
explicit hypotheses, not assertions about any unconstructed geometric model.
-/
theorem homogeneous_conic_lifts_factor_of_principal_quintic_kernel [IsAlgClosed K]
    (φ : MvPolynomial σ K →ₐ[K] R) (F A B D : MvPolynomial σ K) (s t : R)
    (hker : RingHom.ker φ.toRingHom = Ideal.span {F})
    (hF : F.totalDegree = 5)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (hind : LinearIndependent K ![s, t])
    (hφA : φ A = s ^ 2) (hφB : φ B = s * t) (hφD : φ D = t ^ 2) :
    ∃ (c : K) (a b : MvPolynomial σ K),
      c ≠ 0 ∧ a.IsHomogeneous 1 ∧ b.IsHomogeneous 1 ∧
      A = C c * a ^ 2 ∧ B = C c * a * b ∧ D = C c * b ^ 2 := by
  obtain ⟨hA0, hD0⟩ := square_lifts_ne_zero_of_linearIndependent φ A D s t hind hφA hφD
  exact nonproportional_homogeneous_conics_from_quintic_ideal F A B D hF hA0 hD0
    hA hB hD (conic_relation_mem_ideal_of_restriction φ F A B D s t hker hφA hφB hφD)
    (square_lifts_not_scalar_proportional_of_linearIndependent φ A D s t hind hφA hφD)

end EvenQuinticConic
