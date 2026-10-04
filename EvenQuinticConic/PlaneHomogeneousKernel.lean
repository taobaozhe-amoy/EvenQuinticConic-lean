import EvenQuinticConic.ProjectiveQuarticRestriction
import EvenQuinticConic.ProjectiveBaseScalars

/-!
# The complete homogeneous kernel on an actual plane curve

Chart fractions are tested in the actual projective stalk at the image of
its generic point. This proves the full homogeneous vanishing ideal, not
only its low-degree part. Retaining homogeneous degree in a new variable
then embeds the affine-cone quotient into a polynomial ring over the actual
curve function field. The cone fraction field is not identified with that
function field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open HomogeneousLocalization
open scoped EvenQuinticConic.SchemeScalars

universe u

namespace EvenQuinticConic

section StalkCriterion

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- A homogeneous fraction is a unit precisely when its numerator avoids
its homogeneous prime. -/
theorem homogeneous_fraction_isUnit_iff_num_notMem
    (𝔭 : Ideal A) [𝔭.IsPrime]
    (z : NumDenSameDeg 𝒜 𝔭.primeCompl) :
    IsUnit (HomogeneousLocalization.mk z) ↔ z.num.1 ∉ 𝔭 := by
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val 𝒜 𝔭,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  exact IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime 𝔭) 𝔭
    z.num.1 ⟨z.den.1, z.den_mem⟩

/-- The actual stalk germ of a homogeneous chart fraction has the exact
unit criterion prescribed by its projective prime. -/
theorem projective_chart_fraction_germ_isUnit_iff
    (f : A) (x : Proj 𝒜) (hx : x ∈ Proj.basicOpen 𝒜 f)
    (z : NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    IsUnit ((Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) x hx
      (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z))) ↔
      z.num.1 ∉ x.asHomogeneousIdeal.toIdeal := by
  rw [← isUnit_map_iff (AlgebraicGeometry.Proj.stalkIso' 𝒜 x)]
  change IsUnit ((Proj.stalkIso' 𝒜 x)
    ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ
      (ProjectiveSpectrum.basicOpen 𝒜 f) x hx
      (ProjectiveSpectrum.Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z)))) ↔ _
  rw [AlgebraicGeometry.Proj.stalkIso'_germ]
  exact homogeneous_fraction_isUnit_iff_num_notMem 𝒜 x.asHomogeneousIdeal.toIdeal
    ⟨z.deg, z.num, z.den, (Submonoid.powers_le.mpr hx) z.den_mem⟩

/-- Vanishing in the actual source function field is exactly membership of
the numerator in the homogeneous prime at the actual generic image. -/
theorem projective_chart_fraction_pullback_eq_zero_iff
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Proj 𝒜) (f : A)
    [Nonempty (p ⁻¹ᵁ Proj.basicOpen 𝒜 f)]
    (z : NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    projectiveChartToFunctionField 𝒜 p f (HomogeneousLocalization.mk z) = 0 ↔
      z.num.1 ∈ (p.base (genericPoint X)).asHomogeneousIdeal.toIdeal := by
  have h := (generic_pullback_ne_zero_iff_germ_isUnit p (Proj.basicOpen 𝒜 f)
      (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z))).trans
    (projective_chart_fraction_germ_isUnit_iff 𝒜 f (p.base (genericPoint X))
      (genericPoint_image_mem_of_nonempty_preimage p _) z)
  exact not_iff_not.mp h

end StalkCriterion

section Plane

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Full homogeneous restriction kernel of an actual projective map whose
generic image is the defining homogeneous prime. -/
theorem projective_eval₂_eq_zero_iff_mem_principal
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Proj (homogeneousSubmodule (Fin 3) K))
    (F : PlanePolynomial K)
    (hη : (p.base (genericPoint X)).asHomogeneousIdeal.toIdeal = Ideal.span {F})
    (j : Fin 3) [Nonempty (p ⁻¹ᵁ Proj.basicOpen
      (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j))]
    (d : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous d) :
    eval₂
      ((projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p
        (MvPolynomial.X j)).comp (planeChartConstants j))
      (fun i ↦ projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p
        (MvPolynomial.X j) (planeChartRatio j i)) P = 0 ↔
      P ∈ Ideal.span {F} := by
  rw [planeChart_map_eval₂_homogeneous j d P hP]
  exact (projective_chart_fraction_pullback_eq_zero_iff
    (homogeneousSubmodule (Fin 3) K) p (MvPolynomial.X j)
    ⟨d • 1, ⟨P, by simpa using hP⟩,
      ⟨(MvPolynomial.X j) ^ d, SetLike.pow_mem_graded d (isHomogeneous_X K j)⟩,
      ⟨d, rfl⟩⟩).trans (by rw [hη])

/-- Constant chart fractions agree with the actual scalar map on the curve
function field. -/
theorem planeCurveGenericConstants_eq_algebraMap (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F j)] :
    planeCurveGenericConstants F j = algebraMap K (PlaneCurveScheme F).functionField := by
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j)) :=
    ‹Nonempty (planeCurveCoordinateOpen F j)›
  exact planeChartToFunctionField_constants_eq_algebraMap (planeCurveInclusion F) j

/-- A homogeneous form of any degree restricts to zero on the actual plane
curve if and only if it is divisible by the defining equation. -/
theorem planeCurve_homogeneous_aeval_eq_zero_iff
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (j : Fin 3) (d : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous d) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
    aeval (planeCurveGenericCoordinates F j) P = 0 ↔ P ∈ Ideal.span {F} := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j)) :=
    ‹Nonempty (planeCurveCoordinateOpen F j)›
  have hη : ((planeCurveInclusion F).base (genericPoint (PlaneCurveScheme F))).asHomogeneousIdeal.toIdeal =
      Ideal.span {F} := by
    rw [planeCurveInclusion_genericPoint F e hF hFdeg hprime]
    rfl
  have h := projective_eval₂_eq_zero_iff_mem_principal (planeCurveInclusion F)
    F hη j d P hP
  change eval₂ (planeCurveGenericConstants F j) (planeCurveGenericCoordinates F j) P = 0 ↔ _ at h
  rw [planeCurveGenericConstants_eq_algebraMap] at h
  exact h

/-- Retaining homogeneous degree computes the entire actual restriction
kernel, including nonhomogeneous polynomials. -/
theorem planeCurve_gradedRestriction_ker
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (j : Fin 3) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
    RingHom.ker (gradedRestriction (planeCurveGenericCoordinates F j)).toRingHom =
      Ideal.span {F} := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
  apply ker_gradedRestriction_eq_span_of_homogeneous_vanishing _ F e hF
  · exact (planeCurve_homogeneous_aeval_eq_zero_iff F e hF hFdeg hprime j e F hF).mpr
      (Ideal.subset_span (Set.mem_singleton F))
  · intro P d hP hzero
    exact (planeCurve_homogeneous_aeval_eq_zero_iff F e hF hFdeg hprime j d P hP).mp hzero

/-- The actual affine cone embeds in polynomials over the actual curve
function field, with the polynomial variable retaining homogeneous degree. -/
def planeConeToCurvePolynomial
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (j : Fin 3) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    PlaneConeQuotient F →ₐ[K] Polynomial (PlaneCurveScheme F).functionField := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
  exact Ideal.Quotient.liftₐ (Ideal.span {F})
    (gradedRestriction (planeCurveGenericCoordinates F j)) fun P hP ↦ by
      change P ∈ RingHom.ker (gradedRestriction (planeCurveGenericCoordinates F j)).toRingHom
      rw [planeCurve_gradedRestriction_ker F e hF hFdeg hprime j]
      exact hP

/-- On polynomial representatives the cone map is exactly graded evaluation
at the genuine generic chart coordinates. -/
@[simp]
theorem planeConeToCurvePolynomial_mk
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (j : Fin 3)
    (P : PlanePolynomial K) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
    planeConeToCurvePolynomial F e hF hFdeg hprime j
      (Ideal.Quotient.mk (Ideal.span {F}) P) =
      gradedRestriction (planeCurveGenericCoordinates F j) P := rfl

/-- This is an actual embedding, because its full kernel was computed from
the generic point of the actual projective curve. -/
theorem planeConeToCurvePolynomial_injective
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (j : Fin 3) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    Function.Injective (planeConeToCurvePolynomial F e hF hFdeg hprime j) := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
  exact Ideal.injective_lift_iff _ |>.mpr
    (planeCurve_gradedRestriction_ker F e hF hFdeg hprime j)

/-- The embedded value of a homogeneous form keeps precisely its degree. -/
theorem planeConeToCurvePolynomial_homogeneous
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (j : Fin 3)
    (P : PlanePolynomial K) (d : ℕ) (hP : P.IsHomogeneous d) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
    planeConeToCurvePolynomial F e hF hFdeg hprime j
      (Ideal.Quotient.mk (Ideal.span {F}) P) =
      Polynomial.C (aeval (planeCurveGenericCoordinates F j) P) * Polynomial.X ^ d := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
  rw [planeConeToCurvePolynomial_mk]
  exact gradedRestriction_of_isHomogeneous _ P d hP

end Plane

end EvenQuinticConic
