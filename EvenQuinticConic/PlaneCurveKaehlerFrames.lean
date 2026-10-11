import EvenQuinticConic.PlaneKaehlerFrames
import EvenQuinticConic.PlaneJacobianSmooth
import EvenQuinticConic.SchemeKaehlerSheaf

/-!
# Coordinate differential frames in the actual curve differential presheaf

The coefficient action on each actual derivative principal open is the one
induced by `planeCurveStructure`, exactly as in `schemeKaehlerPresheaf`.
The affine Kähler basis therefore gives a basis of that presheaf's actual value.
No equality between its value and the sections of its sheafification is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial Module

namespace EvenQuinticConic

variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chart constant map equals the specified pullback of constants used
to define the actual differential presheaf. -/
theorem planeCurveChartConstants_eq_differentialConstants
    (F : PlanePolynomial K) [IsIntegral (PlaneCurveScheme F)]
    (i : Fin 3) [Nonempty (planeCurveCoordinateOpen F i)] :
    planeCurveChartConstants F i =
      ((schemeConstantsPresheafHom (planeCurveStructure F)).app
        (op (planeCurveCoordinateOpen F i))).hom := by
  rw [planeCurveChartConstants_eq_structure]
  rfl

/-- On the actual derivative open, the actual base-field scalar action is
compatible with restriction from the coordinate chart. -/
theorem planeCurveGradient_differential_scalarTower
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    [IsIntegral (PlaneCurveScheme F)]
    (i j : Fin 3) [Nonempty (planeCurveCoordinateOpen F i)] :
    letI := planeCurveChartAlgebra F i
    letI : Algebra K Γ(PlaneCurveScheme F,
        (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) :=
      ((schemeConstantsPresheafHom (planeCurveStructure F)).app
      (op ((PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)))).hom.toAlgebra
    IsScalarTower K Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i)
      Γ(PlaneCurveScheme F,
        (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) := by
  letI := planeCurveChartAlgebra F i
  letI : Algebra K Γ(PlaneCurveScheme F,
      (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) :=
    ((schemeConstantsPresheafHom (planeCurveStructure F)).app
    (op ((PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)))).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  change ((schemeConstantsPresheafHom (planeCurveStructure F)).app
      (op ((PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)))).hom =
    ((PlaneCurveScheme F).presheaf.map (homOfLE
      ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))).op).hom.comp
        (planeCurveChartConstants F i)
  rw [planeCurveChartConstants_eq_differentialConstants]
  have h := (schemeConstantsPresheafHom (planeCurveStructure F)).naturality
    (homOfLE ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))).op
  simpa only [Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp] using
    congrArg CommRingCat.Hom.hom h

/-- A basis of the actual differential-presheaf value on the actual derivative
principal open, with the scalar map supplied by the curve structure morphism. -/
def planeCurveGradientKaehlerBasis
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    Basis Unit Γ(PlaneCurveScheme F,
        (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
      ((schemeKaehlerPresheaf (planeCurveStructure F)).obj
        (op ((PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)))) := by
  letI := planeCurveScheme_isIntegral F 5 hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime i
  let A := Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i)
  let a := planeCurveGradientSection F hF i j
  let T := Γ(PlaneCurveScheme F, (PlaneCurveScheme F).basicOpen a)
  letI := planeCurveChartAlgebra F i
  letI : Algebra K T := ((schemeConstantsPresheafHom (planeCurveStructure F)).app
    (op ((PlaneCurveScheme F).basicOpen a))).hom.toAlgebra
  haveI : IsScalarTower K A T := planeCurveGradient_differential_scalarTower F hF i j
  have ha : (aeval (planeCurveChartCoordinates F i)) (pderiv j F) = a :=
    planeCurveChartPolynomialMap_pderiv F hF i j
  haveI : IsLocalization.Away ((aeval (planeCurveChartCoordinates F i)) (pderiv j F)) T := by
    rw [ha]
    exact (planeCurveCoordinateOpen_isAffine F i).isLocalization_basicOpen a
  have hv : Function.Surjective (aeval (planeCurveChartCoordinates F i)) :=
    planeCurveChartPolynomialMap_surjective F i
  have hk : RingHom.ker (aeval (planeCurveChartCoordinates F i)) =
      Ideal.span {F, X i - 1} := planeCurveChartPolynomialMap_ker F 5 hF hFdeg hprime i
  exact planeChartKaehlerBasis F i j k hji hki hkj (planeCurveChartCoordinates F i) hv hk T

/-- The actual basis vector is the differential of the restricted actual
coordinate ratio `X k / X i`. -/
theorem planeCurveGradientKaehlerBasis_apply
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    planeCurveGradientKaehlerBasis F hF hFdeg hprime i j k hji hki hkj () =
      CommRingCat.KaehlerDifferential.d
        ((PlaneCurveScheme F).presheaf.map (homOfLE
          ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))).op
            (planeCurveChartCoordinates F i k)) := by
  letI := planeCurveScheme_isIntegral F 5 hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime i
  let a := planeCurveGradientSection F hF i j
  let T := Γ(PlaneCurveScheme F, (PlaneCurveScheme F).basicOpen a)
  letI := planeCurveChartAlgebra F i
  letI : Algebra K T := ((schemeConstantsPresheafHom (planeCurveStructure F)).app
    (op ((PlaneCurveScheme F).basicOpen a))).hom.toAlgebra
  haveI : IsScalarTower K Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) T :=
    planeCurveGradient_differential_scalarTower F hF i j
  haveI : IsLocalization.Away ((aeval (planeCurveChartCoordinates F i)) (pderiv j F)) T := by
    rw [show (aeval (planeCurveChartCoordinates F i)) (pderiv j F) = a from
      planeCurveChartPolynomialMap_pderiv F hF i j]
    exact (planeCurveCoordinateOpen_isAffine F i).isLocalization_basicOpen a
  exact planeChartKaehlerBasis_apply F i j k hji hki hkj (planeCurveChartCoordinates F i)
    (planeCurveChartPolynomialMap_surjective F i)
    (planeCurveChartPolynomialMap_ker F 5 hF hFdeg hprime i) T

/-- Explicit affine coefficient trivialization of the actual differential
presheaf value on a derivative principal open. -/
def planeCurveGradientKaehlerTrivialization
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    Γ(PlaneCurveScheme F,
        (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) ≃ₗ[
      Γ(PlaneCurveScheme F,
        (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))]
      ((schemeKaehlerPresheaf (planeCurveStructure F)).obj
        (op ((PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)))) :=
  (LinearEquiv.funUnique Unit _ _).symm.trans
    (planeCurveGradientKaehlerBasis F hF hFdeg hprime i j k hji hki hkj).equivFun.symm

/-- The coefficient trivialization is multiplication by the actual
differential of the restricted coordinate ratio. -/
theorem planeCurveGradientKaehlerTrivialization_apply
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (t : Γ(PlaneCurveScheme F,
      (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))) :
    planeCurveGradientKaehlerTrivialization F hF hFdeg hprime i j k hji hki hkj t =
      t • CommRingCat.KaehlerDifferential.d
        ((PlaneCurveScheme F).presheaf.map (homOfLE
          ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))).op
            (planeCurveChartCoordinates F i k)) := by
  simp [planeCurveGradientKaehlerTrivialization, planeCurveGradientKaehlerBasis_apply]

end EvenQuinticConic
