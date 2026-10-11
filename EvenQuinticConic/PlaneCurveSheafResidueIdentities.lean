import EvenQuinticConic.PlaneCurveResidueIdentities

/-!
# Actual sheaf-valued residue identities on curve overlaps

The proven identities in genuine overlap Kähler modules are sent through
the actual linear sheafification map. The resulting equalities concern
sections of `schemeKaehlerSheaf`, with the same actual derivative units
and degree-two coordinate factors. No local freeness or gluing conclusion
is assumed or asserted in this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial

namespace EvenQuinticConic

variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra planeCurveResidueSectionAlgebra

/-- The actual sheafification map on an overlap, expressed as a linear map
from its genuine ring Kähler module with the specified structure scalars. -/
def planeCurveResidueSheafificationLinearMap
    (F : PlanePolynomial K) (W : (PlaneCurveScheme F).Opens) :
    KaehlerDifferential K Γ(PlaneCurveScheme F, W) →ₗ[Γ(PlaneCurveScheme F, W)]
      (schemeKaehlerSheaf (planeCurveStructure F)).val.obj (op W) :=
  ((schemeKaehlerSheafificationMap (planeCurveStructure F)).app (op W)).hom

/-- The universal ring differential maps to the actual sheaf differential. -/
@[simp]
theorem planeCurveResidueSheafificationLinearMap_D
    (F : PlanePolynomial K) (W : (PlaneCurveScheme F).Opens)
    (s : Γ(PlaneCurveScheme F, W)) :
    planeCurveResidueSheafificationLinearMap F W
        (KaehlerDifferential.D K Γ(PlaneCurveScheme F, W) s) =
      (schemeKaehlerDerivation (planeCurveStructure F)).d s := rfl

/-- The actual sheaf section `d(X_k/X_i)/(∂_j F/X_i^4)` on a subopen
of the specified derivative principal open. Signs are stated in the
transition theorems rather than built into this expression. -/
def planeCurveSheafResidue
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j k : Fin 3)
    (W : (PlaneCurveScheme F).Opens)
    (hj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) :
    (schemeKaehlerSheaf (planeCurveStructure F)).val.obj (op W) :=
  (↑(planeCurveGradientUnitOn F hF i j W hj)⁻¹ : Γ(PlaneCurveScheme F, W)) •
    (schemeKaehlerDerivation (planeCurveStructure F)).d
      (planeCurveResidueCoordinates F i W
        (hj.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))) k)

/-- On an actual same-chart overlap, the two sheaf-valued residues differ
by precisely the sign proved in the ring differential module. -/
theorem planeCurveSheafResidue_sameChart
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (W : (PlaneCurveScheme F).Opens)
    (hj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hk : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i k)) :
    planeCurveSheafResidue F hF i j k W hj = -planeCurveSheafResidue F hF i k j W hk := by
  have h := congrArg (planeCurveResidueSheafificationLinearMap F W)
    (planeCurveResidue_sameChart F hF hFdeg hprime i j k hji hki hkj W hj hk)
  simpa only [map_smul, map_neg, planeCurveResidueSheafificationLinearMap_D,
    planeCurveSheafResidue] using h

/-- The common-derivative cross-chart formula holds inside the actual
differential sheaf, with the actual squared coordinate ratio. -/
theorem planeCurveSheafResidue_commonDerivative
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i l j : Fin 3) (W : (PlaneCurveScheme F).Opens)
    (hij : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hlj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l j)) :
    -planeCurveSheafResidue F hF l j i W hlj =
      (planeCurveResidueCoordinates F i W
        (hij.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))) l) ^ 2 •
      planeCurveSheafResidue F hF i j l W hij := by
  have h := congrArg (planeCurveResidueSheafificationLinearMap F W)
    (planeCurveResidue_commonDerivative F hF hFdeg hprime i l j W hij hlj)
  simpa only [map_smul, map_neg, planeCurveResidueSheafificationLinearMap_D,
    planeCurveSheafResidue] using h

/-- The radial-derivative cross-chart formula holds inside the actual
differential sheaf, with unchanged sign and degree-two transition factor. -/
theorem planeCurveSheafResidue_radialDerivatives
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i l k : Fin 3) (hli : l ≠ i) (hki : k ≠ i) (hkl : k ≠ l)
    (W : (PlaneCurveScheme F).Opens)
    (hil : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i l))
    (hli' : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l i)) :
    -planeCurveSheafResidue F hF l i k W hli' =
      (planeCurveResidueCoordinates F i W
        (hil.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i l))) l) ^ 2 •
      planeCurveSheafResidue F hF i l k W hil := by
  have h := congrArg (planeCurveResidueSheafificationLinearMap F W)
    (planeCurveResidue_radialDerivatives F hF hFdeg hprime i l k hli hki hkl W hil hli')
  simpa only [map_smul, map_neg, planeCurveResidueSheafificationLinearMap_D,
    planeCurveSheafResidue] using h

/-- The independently constructed derivative units commute with actual
restriction to smaller opens. -/
theorem planeCurveGradientUnitOn_restrict
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j : Fin 3)
    (W V : (PlaneCurveScheme F).Opens)
    (hj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hVW : V ≤ W) :
    Units.map (UnitTransition.res hVW).toMonoidHom (planeCurveGradientUnitOn F hF i j W hj) =
      planeCurveGradientUnitOn F hF i j V (hVW.trans hj) := by
  apply Units.ext
  change UnitTransition.res hVW
    (planeCurveGradientUnitOn F hF i j W hj : Γ(PlaneCurveScheme F, W)) = _
  rw [planeCurveGradientUnitOn_val, planeCurveGradientUnitOn_val, UnitTransition.res_res]

/-- Restricted chart coordinates commute with the actual structure-sheaf
restriction maps. -/
theorem planeCurveResidueCoordinates_restrict
    (F : PlanePolynomial K) (i : Fin 3) (W V : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i) (hVW : V ≤ W) (k : Fin 3) :
    UnitTransition.res hVW (planeCurveResidueCoordinates F i W hi k) =
      planeCurveResidueCoordinates F i V (hVW.trans hi) k :=
  UnitTransition.res_res hi hVW (planeCurveChartCoordinates F i k)

/-- Actual sheaf-valued residues are compatible with all smaller opens.
This uses the naturality of the genuine sheaf derivation and the proved
restriction formula for the genuine derivative units. -/
theorem planeCurveSheafResidue_restrict
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j k : Fin 3)
    (W V : (PlaneCurveScheme F).Opens)
    (hj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hVW : V ≤ W) :
    (schemeKaehlerSheaf (planeCurveStructure F)).val.map (homOfLE hVW).op
        (planeCurveSheafResidue F hF i j k W hj) =
      planeCurveSheafResidue F hF i j k V (hVW.trans hj) := by
  have hinv : UnitTransition.res hVW
      (↑(planeCurveGradientUnitOn F hF i j W hj)⁻¹ : Γ(PlaneCurveScheme F, W)) =
      (↑(planeCurveGradientUnitOn F hF i j V (hVW.trans hj))⁻¹ : Γ(PlaneCurveScheme F, V)) := by
    change (↑(Units.map (UnitTransition.res hVW).toMonoidHom
      (planeCurveGradientUnitOn F hF i j W hj)⁻¹) : Γ(PlaneCurveScheme F, V)) = _
    rw [map_inv, planeCurveGradientUnitOn_restrict]
  unfold planeCurveSheafResidue
  rw [PresheafOfModules.map_smul, ← schemeKaehlerDerivation_restrict]
  change UnitTransition.res hVW
      (↑(planeCurveGradientUnitOn F hF i j W hj)⁻¹ : Γ(PlaneCurveScheme F, W)) •
      (schemeKaehlerDerivation (planeCurveStructure F)).d
        (UnitTransition.res hVW (planeCurveResidueCoordinates F i W _ k)) = _
  rw [hinv, planeCurveResidueCoordinates_restrict]

end EvenQuinticConic
