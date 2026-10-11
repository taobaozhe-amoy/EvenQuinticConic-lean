import EvenQuinticConic.PlaneCurveDifferentialCover
import EvenQuinticConic.PlaneCurveResidueFrames
import EvenQuinticConic.PlaneCurveSignedResidueTransitions
import EvenQuinticConic.FrameTransitionComparison
import EvenQuinticConic.PlaneThetaIneffectivity

/-!
# Actual differential adjunction for a nonsingular plane quintic

The genuine differential sheaf is identified with the actual hyperplane
square sheaf. Its signed residue frames are built from actual Jacobian
bases, affine comparison and open restriction. Their complete transition
formula is proved on actual overlaps, then used to glue a sheaf isomorphism.
No adjunction or local differential trivialization is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial

namespace EvenQuinticConic
variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual signed residue frame on each derivative open. -/
def planeCurveSignedResidueCoverFrame
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (a : PlaneDifferentialChartIndex) :
    ModuleSheafFrame (schemeKaehlerSheaf (planeCurveStructure F))
      (planeCurveDifferentialOpen F hF a.1 a.2.1) :=
  planeCurveSignedResidueFrame F hF hFdeg hprime a.1 a.2.1
    (planeDifferentialThirdCoordinate a.1 a.2.1) a.2.2
    (planeDifferentialThirdCoordinate_ne a.1 a.2.1).1
    (planeDifferentialThirdCoordinate_ne a.1 a.2.1).2

/-- The hyperplane square frame restricted to the same derivative open. -/
def planeCurveQuadraticDifferentialFrame
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (a : PlaneDifferentialChartIndex) :
    ModuleSheafFrame (PlaneCurveQuadraticSheaf F)
      (planeCurveDifferentialOpen F hF a.1 a.2.1) :=
  (planeCurveQuadraticFrame F a.1).onSubopen
    ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF a.1 a.2.1))

/-- The actual quadratic frame coefficient is the squared coordinate unit. -/
theorem planeCurveQuadraticFrame_changeCoefficient
    (F : PlanePolynomial K) (i l : Fin 3) (W : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i) (hl : W ≤ planeCurveCoordinateOpen F l) :
    frameChangeCoefficient (planeCurveQuadraticFrame F i) (planeCurveQuadraticFrame F l)
      W hi hl = ((planeCurveHyperplaneTransition F).transition i l W hi hl :
        Γ(PlaneCurveScheme F, W)) ^ 2 := by
  let g := (planeCurveHyperplaneTransition F).mul (planeCurveHyperplaneTransition F)
  have h := g.frame_transition i l W hi hl (((g.frame l).coordinate W hl).symm 1)
  rw [LinearEquiv.apply_symm_apply, mul_one] at h
  exact h.trans (pow_two _).symm

/-- Signed differential residue frames and actual hyperplane-square frames
have identical transitions on every common subopen. -/
theorem planeCurveAdjunction_frame_coefficients
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (a b : PlaneDifferentialChartIndex) (W : (PlaneCurveScheme F).Opens)
    (ha : W ≤ planeCurveDifferentialOpen F hF a.1 a.2.1)
    (hb : W ≤ planeCurveDifferentialOpen F hF b.1 b.2.1) :
    frameChangeCoefficient (planeCurveSignedResidueCoverFrame F hF hFdeg hprime a)
        (planeCurveSignedResidueCoverFrame F hF hFdeg hprime b) W ha hb =
      frameChangeCoefficient (planeCurveQuadraticDifferentialFrame F hF a)
        (planeCurveQuadraticDifferentialFrame F hF b) W ha hb := by
  let hi := ha.trans ((PlaneCurveScheme F).basicOpen_le
    (planeCurveGradientSection F hF a.1 a.2.1))
  let hl := hb.trans ((PlaneCurveScheme F).basicOpen_le
    (planeCurveGradientSection F hF b.1 b.2.1))
  have hg : frameChangeCoefficient
      (planeCurveSignedResidueCoverFrame F hF hFdeg hprime a)
      (planeCurveSignedResidueCoverFrame F hF hFdeg hprime b) W ha hb =
        ((planeCurveHyperplaneTransition F).transition a.1 b.1 W hi hl :
          Γ(PlaneCurveScheme F, W)) ^ 2 := by
    apply frameChangeCoefficient_eq_of_generator_eq
    change ((planeCurveSignedResidueFrame F hF hFdeg hprime b.1 b.2.1
      (planeDifferentialThirdCoordinate b.1 b.2.1) b.2.2
      (planeDifferentialThirdCoordinate_ne b.1 b.2.1).1
      (planeDifferentialThirdCoordinate_ne b.1 b.2.1).2).coordinate W hb).symm 1 = _
    rw [planeCurveSignedResidueFrame_generator]
    change _ = _ • ((planeCurveSignedResidueFrame F hF hFdeg hprime a.1 a.2.1
      (planeDifferentialThirdCoordinate a.1 a.2.1) a.2.2
      (planeDifferentialThirdCoordinate_ne a.1 a.2.1).1
      (planeDifferentialThirdCoordinate_ne a.1 a.2.1).2).coordinate W ha).symm 1
    rw [planeCurveSignedResidueFrame_generator]
    exact planeCurveSignedResidue_transition_unit F hF hFdeg hprime
      a.1 a.2.1 (planeDifferentialThirdCoordinate a.1 a.2.1)
      b.1 b.2.1 (planeDifferentialThirdCoordinate b.1 b.2.1)
      a.2.2 (planeDifferentialThirdCoordinate_ne a.1 a.2.1).1
      (planeDifferentialThirdCoordinate_ne a.1 a.2.1).2
      b.2.2 (planeDifferentialThirdCoordinate_ne b.1 b.2.1).1
      (planeDifferentialThirdCoordinate_ne b.1 b.2.1).2 W ha hb
  rw [hg]
  exact (planeCurveQuadraticFrame_changeCoefficient F a.1 b.1 W hi hl).symm

/-- Actual differential adjunction from the projective gradient criterion. -/
def planeCurveAdjunctionIsoOfGradient
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (hgrad : ∀ p : Proj (homogeneousSubmodule (Fin 3) K),
      F ∈ p.asHomogeneousIdeal.toIdeal →
        ∃ j : Fin 3, pderiv j F ∉ p.asHomogeneousIdeal.toIdeal) :
    schemeKaehlerSheaf (planeCurveStructure F) ≅ PlaneCurveQuadraticSheaf F :=
  frameTransitionComparisonIso
    (fun a : PlaneDifferentialChartIndex ↦ planeCurveDifferentialOpen F hF a.1 a.2.1)
    (planeCurveGradientBasicOpen_cover F hF hgrad)
    (planeCurveSignedResidueCoverFrame F hF hFdeg hprime)
    (planeCurveQuadraticDifferentialFrame F hF)
    (planeCurveAdjunction_frame_coefficients F hF hFdeg hprime)

/-- The glued adjunction isomorphism preserves the actual residue and
quadratic coordinates on every derivative subopen. -/
theorem planeCurveAdjunctionIsoOfGradient_coordinate
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (hgrad : ∀ p : Proj (homogeneousSubmodule (Fin 3) K),
      F ∈ p.asHomogeneousIdeal.toIdeal →
        ∃ j : Fin 3, pderiv j F ∉ p.asHomogeneousIdeal.toIdeal)
    (a : PlaneDifferentialChartIndex) (W : (PlaneCurveScheme F).Opens)
    (ha : W ≤ planeCurveDifferentialOpen F hF a.1 a.2.1)
    (s : (schemeKaehlerSheaf (planeCurveStructure F)).val.obj (op W)) :
    (planeCurveQuadraticDifferentialFrame F hF a).coordinate W ha
        ((planeCurveAdjunctionIsoOfGradient F hF hFdeg hprime hgrad).hom.val.app
          (op W) s) =
      (planeCurveSignedResidueCoverFrame F hF hFdeg hprime a).coordinate W ha s :=
  frameTransitionComparisonIso_coordinate
    (fun a : PlaneDifferentialChartIndex ↦ planeCurveDifferentialOpen F hF a.1 a.2.1)
    (planeCurveGradientBasicOpen_cover F hF hgrad)
    (planeCurveSignedResidueCoverFrame F hF hFdeg hprime)
    (planeCurveQuadraticDifferentialFrame F hF)
    (planeCurveAdjunction_frame_coefficients F hF hFdeg hprime) a W ha s

/-- A nonsingular quintic equation supplies actual differential adjunction;
primality, all local frames, all transitions and gluing are proved internally. -/
def planeQuinticAdjunctionIsoOfJacobian [IsAlgClosed K]
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0) :
    schemeKaehlerSheaf (planeCurveStructure F) ≅ PlaneCurveQuadraticSheaf F :=
  planeCurveAdjunctionIsoOfGradient F hF (by omega)
    (plane_principal_isPrime_of_jacobian F 5 hF (by omega) hJac)
    (projective_gradient_of_rational_jacobian F hJac)

end EvenQuinticConic
