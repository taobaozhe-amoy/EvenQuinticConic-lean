import EvenQuinticConic.PlaneCurveDifferentialSheafFrames
import EvenQuinticConic.PlaneCurveSignedResidueTransitions
import EvenQuinticConic.ModuleFrameRescaling

/-!
# Actual normalized residue frames on a plane curve

The actual coordinate-differential frames on derivative principal opens
are rescaled by the inverse of the actual derivative unit. Their generators
on every subordinate open are precisely the previously defined sheaf-valued
residues. No desired basis, local isomorphism, or transition identity is
assumed as an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial

namespace EvenQuinticConic

variable {K : Type} [Field K]

/-- Inverse derivative units restrict to the inverse of the actual derivative
unit independently constructed on the smaller open. -/
theorem planeCurveGradientUnitOn_inv_restrict
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j : Fin 3)
    (W V : (PlaneCurveScheme F).Opens)
    (hj : W ≤ planeCurveDifferentialOpen F hF i j) (hVW : V ≤ W) :
    UnitTransition.res hVW
        (↑(planeCurveGradientUnitOn F hF i j W hj)⁻¹ : Γ(PlaneCurveScheme F, W)) =
      (↑(planeCurveGradientUnitOn F hF i j V (hVW.trans hj))⁻¹ :
        Γ(PlaneCurveScheme F, V)) := by
  change (↑(Units.map (UnitTransition.res hVW).toMonoidHom
    (planeCurveGradientUnitOn F hF i j W hj)⁻¹) : Γ(PlaneCurveScheme F, V)) = _
  rw [map_inv, planeCurveGradientUnitOn_restrict]

/-- The coordinate defining the actual differential frame restricts to the
same normalized coordinate used in the actual residue section. -/
theorem planeCurveDifferentialCoordinate_restrict
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j k : Fin 3)
    (W : (PlaneCurveScheme F).Opens) (hW : W ≤ planeCurveDifferentialOpen F hF i j) :
    UnitTransition.res hW (planeCurveDifferentialCoordinate F hF i j k) =
      planeCurveResidueCoordinates F i W
        (hW.trans ((PlaneCurveScheme F).basicOpen_le
          (planeCurveGradientSection F hF i j))) k := by
  exact UnitTransition.res_res
    ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j)) hW
      (planeCurveChartCoordinates F i k)

/-- The actual differential frame normalized by the inverse actual derivative
unit. The coordinate differential basis and the affine sheaf comparison are
already proved inside `planeCurveDifferentialSheafFrame`. -/
def planeCurveResidueFrame
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    ModuleSheafFrame (schemeKaehlerSheaf (planeCurveStructure F))
      (planeCurveDifferentialOpen F hF i j) :=
  (planeCurveDifferentialSheafFrame F hF hFdeg hprime i j k hji hki hkj).rescale
    (planeCurveGradientUnitOn F hF i j (planeCurveDifferentialOpen F hF i j) le_rfl)⁻¹

/-- The normalized residue frame is an actual isomorphism to the structure
module on the original curve's site below the derivative principal open. -/
def planeCurveResidueLocalUnitIso
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    (schemeKaehlerSheaf (planeCurveStructure F)).over
      (planeCurveDifferentialOpen F hF i j) ≅
        SheafOfModules.unit ((PlaneCurveScheme F).ringCatSheaf.over
          (planeCurveDifferentialOpen F hF i j)) :=
  (planeCurveResidueFrame F hF hFdeg hprime i j k hji hki hkj).localUnitIso

/-- Orientation units are preserved by actual ring homomorphisms, in
particular by every structure-sheaf restriction map. -/
theorem planeResidueSignUnit_map {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (i j k : Fin 3) :
    Units.map f.toMonoidHom (planeResidueSignUnit (S := S) i j k) =
      planeResidueSignUnit (S := T) i j k := by
  apply Units.ext
  change f (planeResidueSignUnit (S := S) i j k : S) = _
  rw [planeResidueSignUnit_val, planeResidueSignUnit_val, map_intCast]

/-- The actual normalized frame with the orientation convention used by
`planeCurveSignedResidue`. Its transition coefficients have the degree-two
hyperplane convention. -/
def planeCurveSignedResidueFrame
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    ModuleSheafFrame (schemeKaehlerSheaf (planeCurveStructure F))
      (planeCurveDifferentialOpen F hF i j) :=
  (planeCurveResidueFrame F hF hFdeg hprime i j k hji hki hkj).rescale
    (planeResidueSignUnit
      (S := Γ(PlaneCurveScheme F, planeCurveDifferentialOpen F hF i j)) i j k)

/-- The signed residue frame supplies a genuine local isomorphism on the
original curve's restricted site. -/
def planeCurveSignedResidueLocalUnitIso
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    (schemeKaehlerSheaf (planeCurveStructure F)).over
      (planeCurveDifferentialOpen F hF i j) ≅
        SheafOfModules.unit ((PlaneCurveScheme F).ringCatSheaf.over
          (planeCurveDifferentialOpen F hF i j)) :=
  (planeCurveSignedResidueFrame F hF hFdeg hprime i j k hji hki hkj).localUnitIso

/-- The normalized frame's generator on every subordinate open is exactly
the genuine differential-sheaf residue, including the actual inverse
partial-derivative coefficient. -/
theorem planeCurveResidueFrame_generator
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (W : (PlaneCurveScheme F).Opens) (hW : W ≤ planeCurveDifferentialOpen F hF i j) :
    ((planeCurveResidueFrame F hF hFdeg hprime i j k hji hki hkj).coordinate
      W hW).symm 1 = planeCurveSheafResidue F hF i j k W hW := by
  rw [planeCurveResidueFrame, ModuleSheafFrame.rescale_generator,
    planeCurveDifferentialSheafFrame_generator F hF hFdeg hprime i j k hji hki hkj W hW]
  change UnitTransition.res hW
      (↑(planeCurveGradientUnitOn F hF i j
        (planeCurveDifferentialOpen F hF i j) le_rfl)⁻¹ :
          Γ(PlaneCurveScheme F, planeCurveDifferentialOpen F hF i j)) •
      (schemeKaehlerDerivation (planeCurveStructure F)).d
        (UnitTransition.res hW (planeCurveDifferentialCoordinate F hF i j k)) = _
  rw [planeCurveGradientUnitOn_inv_restrict, planeCurveDifferentialCoordinate_restrict]
  rfl

/-- The signed frame's actual generator on every subordinate open is exactly
the signed residue used in the proved degree-two transition formula. -/
theorem planeCurveSignedResidueFrame_generator
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (W : (PlaneCurveScheme F).Opens) (hW : W ≤ planeCurveDifferentialOpen F hF i j) :
    ((planeCurveSignedResidueFrame F hF hFdeg hprime i j k hji hki hkj).coordinate
      W hW).symm 1 = planeCurveSignedResidue F hF i j k W hW := by
  rw [planeCurveSignedResidueFrame, ModuleSheafFrame.rescale_generator,
    planeCurveResidueFrame_generator F hF hFdeg hprime i j k hji hki hkj W hW]
  have hsign := congrArg (fun w : Γ(PlaneCurveScheme F, W)ˣ => (w : Γ(PlaneCurveScheme F, W)))
    (planeResidueSignUnit_map (UnitTransition.res hW) i j k)
  change UnitTransition.res hW
      (planeResidueSignUnit
        (S := Γ(PlaneCurveScheme F, planeCurveDifferentialOpen F hF i j)) i j k :
          Γ(PlaneCurveScheme F, planeCurveDifferentialOpen F hF i j)) =
    (planeResidueSignUnit (S := Γ(PlaneCurveScheme F, W)) i j k : Γ(PlaneCurveScheme F, W)) at hsign
  change UnitTransition.res hW
      (planeResidueSignUnit
        (S := Γ(PlaneCurveScheme F, planeCurveDifferentialOpen F hF i j)) i j k :
          Γ(PlaneCurveScheme F, planeCurveDifferentialOpen F hF i j)) •
      planeCurveSheafResidue F hF i j k W hW = _
  rw [hsign, planeResidueSignUnit_smul]
  rfl

end EvenQuinticConic
