import EvenQuinticConic.PlaneChartPolynomialMap
import EvenQuinticConic.PlaneGradientCover
import EvenQuinticConic.PlaneJacobianPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Jacobian smoothness of the actual plane-curve structure morphism

The homogeneous projective gradient condition supplies an actual affine cover
by derivative principal opens. Their actual coordinate presentations and
localization maps prove smoothness of relative dimension one over the base field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial

namespace EvenQuinticConic

variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Polynomial evaluation of a partial derivative is the actual normalized
homogeneous derivative section. -/
theorem planeCurveChartPolynomialMap_pderiv
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j : Fin 3) :
    planeCurveChartPolynomialMap F i (pderiv j F) =
      planeCurveGradientSection F hF i j :=
  planeCurveChartPolynomialMap_homogeneous F i 4 (pderiv j F) hF.pderiv

/-- The actual derivative principal-open chart is standard smooth of relative
dimension one as a ring over the original field. -/
theorem planeCurveGradientBasicOpen_standardSmooth_constants
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j : Fin 3) (hji : j ≠ i) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      (((PlaneCurveScheme F).presheaf.map (homOfLE
          ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))).op).hom.comp
        (planeCurveChartConstants F i)) := by
  let A := Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i)
  let a := planeCurveGradientSection F hF i j
  let T := Γ(PlaneCurveScheme F, (PlaneCurveScheme F).basicOpen a)
  letI := planeCurveChartAlgebra F i
  letI : Algebra K T := ((algebraMap A T).comp (planeCurveChartConstants F i)).toAlgebra
  haveI : IsScalarTower K A T := IsScalarTower.of_algebraMap_eq' rfl
  have ha : (aeval (planeCurveChartCoordinates F i)) (pderiv j F) = a :=
    planeCurveChartPolynomialMap_pderiv F hF i j
  haveI : IsLocalization.Away ((aeval (planeCurveChartCoordinates F i)) (pderiv j F)) T := by
    rw [ha]
    exact (planeCurveCoordinateOpen_isAffine F i).isLocalization_basicOpen a
  have hv : Function.Surjective (aeval (planeCurveChartCoordinates F i)) :=
    planeCurveChartPolynomialMap_surjective F i
  have hk : RingHom.ker (aeval (planeCurveChartCoordinates F i)) =
      Ideal.span {F, X i - 1} := planeCurveChartPolynomialMap_ker F 5 hF hFdeg hprime i
  exact planeChart_derivative_localization_isStandardSmooth F i j hji
    (planeCurveChartCoordinates F i) hv hk T

/-- Each actual derivative principal open has a standard smooth structure map
on coordinate rings over the actual affine base scheme. -/
theorem planeCurveGradientBasicOpen_standardSmooth
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j : Fin 3) (hji : j ≠ i) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      ((planeCurveStructure F).appLE ⊤
        ((PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) le_top).hom := by
  letI := planeCurveScheme_isIntegral F 5 hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime i
  let a := planeCurveGradientSection F hF i j
  let res := (PlaneCurveScheme F).presheaf.map
    (homOfLE ((PlaneCurveScheme F).basicOpen_le a)).op
  let c := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have h := (planeCurveGradientBasicOpen_standardSmooth_constants F hF hFdeg hprime i j hji).comp
    (RingHom.IsStandardSmoothOfRelativeDimension.equiv c)
  have heq : (res.hom.comp (planeCurveChartConstants F i)).comp c.toRingHom =
      ((planeCurveStructure F).appLE ⊤ ((PlaneCurveScheme F).basicOpen a) le_top).hom := by
    rw [planeCurveChartConstants_eq_structure]
    change (res.hom.comp
      (((planeCurveStructure F).appLE ⊤ (planeCurveCoordinateOpen F i) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).comp
          (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom = _
    rw [RingHom.comp_assoc, RingHom.comp_assoc, ← CommRingCat.hom_comp,
      Iso.hom_inv_id, CommRingCat.hom_id, RingHom.comp_id]
    rw [← CommRingCat.hom_comp]
    congr 1
    exact (planeCurveStructure F).appLE_map le_top
      (homOfLE ((PlaneCurveScheme F).basicOpen_le a)).op
  change RingHom.IsStandardSmoothOfRelativeDimension (1 + 0)
    ((res.hom.comp (planeCurveChartConstants F i)).comp c.toRingHom) at h
  rwa [heq] at h

/-- The projective nonvanishing-gradient condition proves smoothness of
relative dimension one for the actual plane-curve structure morphism. -/
theorem planeCurveStructure_isSmoothOfRelativeDimension_of_gradient
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (hgrad : ∀ p : Proj (homogeneousSubmodule (Fin 3) K),
      F ∈ p.asHomogeneousIdeal.toIdeal →
        ∃ j : Fin 3, pderiv j F ∉ p.asHomogeneousIdeal.toIdeal) :
    IsSmoothOfRelativeDimension 1 (planeCurveStructure F) where
  exists_isStandardSmoothOfRelativeDimension x := by
    obtain ⟨i, j, hji, hx⟩ := exists_mem_planeCurveGradientBasicOpen F hF hgrad x
    exact ⟨⟨⊤, isAffineOpen_top _⟩,
      ⟨_, planeCurveGradientBasicOpen_isAffine F hF i j⟩, hx, le_top,
      planeCurveGradientBasicOpen_standardSmooth F hF hFdeg hprime i j hji⟩

end EvenQuinticConic
