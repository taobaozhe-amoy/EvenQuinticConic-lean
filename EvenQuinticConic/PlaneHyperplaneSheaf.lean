import EvenQuinticConic.PlaneCurveScheme
import EvenQuinticConic.ProjectiveCoordinateSections
import EvenQuinticConic.PullbackTransition
import EvenQuinticConic.LineBundlePresheaf
import EvenQuinticConic.LineBundleSheaf
import EvenQuinticConic.LineBundleFrames
import EvenQuinticConic.ProjectiveQuarticRestriction
import EvenQuinticConic.ProjectiveBaseScalars
import EvenQuinticConic.SchemeScalarAction

/-!
# The actual coordinate sheaf and its coordinate sections on a plane curve

The transition units `Xⱼ/Xᵢ` of the actual projective plane are pulled back
along the actual closed immersion of the curve. The coordinate sections are
constructed from the pulled-back regular functions `Xₖ/Xᵢ`, and compatibility
is proved by the genuine transition cocycle, rather than assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic

variable {K : Type} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual hyperplane transition cocycle on the concrete curve scheme. -/
def planeCurveHyperplaneTransition (F : PlanePolynomial K) :
    UnitTransition (PlaneCurveScheme F) (planeCurveCoordinateOpen F) :=
  (planeCoordinateUnitTransition K).pullback (planeCurveInclusion F)

/-- The coordinate `Xₖ` in the chart frame `Xᵢ`, pulled back along the actual
curve inclusion as a regular function on the actual curve chart. -/
def planeCurveCoordinateFunction (F : PlanePolynomial K) (k i : Fin 3) :
    Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
  (planeCurveInclusion F).app (planeCoordinateOpen K i) (planeCoordinateRatio K i k)

/-- The pulled-back coordinate functions satisfy the actual curve cocycle on
every common subopen. -/
theorem planeCurveCoordinateFunction_compatible (F : PlanePolynomial K) (k i j : Fin 3)
    (W : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i) (hj : W ≤ planeCurveCoordinateOpen F j) :
    (PlaneCurveScheme F).presheaf.map (homOfLE hi).op (planeCurveCoordinateFunction F k i) =
      ((planeCurveHyperplaneTransition F).transition i j W hi hj : Γ(PlaneCurveScheme F, W)) *
        (PlaneCurveScheme F).presheaf.map (homOfLE hj).op (planeCurveCoordinateFunction F k j) := by
  exact pullback_compatible_coordinates (planeCurveInclusion F) (planeCoordinateUnitTransition K)
    (fun i ↦ planeCoordinateRatio K i k)
    (fun i j W hi hj ↦ (planeCoordinateRatioOn_cocycle K W i j k hi hj).symm)
    i j W hi hj

/-- The three actual global coordinate families in the descended presheaf,
constructed using restrictions of the pulled-back chart functions. -/
def planeCurveCoordinateSectionData (F : PlanePolynomial K) (k : Fin 3) :
    (planeCurveHyperplaneTransition F).Section ⊤ :=
  ⟨fun i W ↦ UnitTransition.res W.property.2 (planeCurveCoordinateFunction F k i), by
    constructor
    · intro i W Z hWtop hWi hZW
      exact UnitTransition.res_res hWi hZW (planeCurveCoordinateFunction F k i)
    · intro i j W hWtop hi hj
      exact planeCurveCoordinateFunction_compatible F k i j W hi hj⟩

/-- Evaluation of the constructed coordinate section uses precisely the
actual restriction of the actual pulled-back ratio. -/
theorem planeCurveCoordinateSectionData_eval (F : PlanePolynomial K) (k i : Fin 3)
    (W : (PlaneCurveScheme F).Opens) (hWtop : W ≤ ⊤)
    (hi : W ≤ planeCurveCoordinateOpen F i) :
    (planeCurveCoordinateSectionData F k).eval i W hWtop hi =
      UnitTransition.res hi (planeCurveCoordinateFunction F k i) := rfl

/-- An actual module sheaf on the actual curve scheme, constructed by descent
from the pulled-back hyperplane coordinate transitions. -/
def PlaneCurveHyperplaneSheaf (F : PlanePolynomial K) : (PlaneCurveScheme F).Modules :=
  (planeCurveHyperplaneTransition F).moduleSheaf

/-- The actual coherent chart frame of the constructed hyperplane sheaf. -/
def planeCurveHyperplaneFrame (F : PlanePolynomial K) (i : Fin 3) :
    ModuleSheafFrame (PlaneCurveHyperplaneSheaf F) (planeCurveCoordinateOpen F i) :=
  (planeCurveHyperplaneTransition F).frame i

/-- The actual global section corresponding to `Xₖ`. This is a constructed
element of the actual module sheaf's global sections, not an existence input. -/
def planeCurveCoordinateSection (F : PlanePolynomial K) (k : Fin 3) :
    (PlaneCurveHyperplaneSheaf F).val.obj (op ⊤) :=
  planeCurveCoordinateSectionData F k

/-- The generic germ of each actual pulled-back chart function is the
normalized coordinate used by the proved low-degree restriction theorem. -/
theorem planeCurveCoordinateFunction_generic (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i k : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] :
    (PlaneCurveScheme F).germToFunctionField (planeCurveCoordinateOpen F i)
      (planeCurveCoordinateFunction F k i) = planeCurveGenericCoordinates F i k := rfl

/-- The constructed global coordinate section has the prescribed local
coordinate in every subopen of every chart. -/
theorem planeCurveCoordinateSection_frame (F : PlanePolynomial K) (k i : Fin 3)
    (W : (PlaneCurveScheme F).Opens) (hi : W ≤ planeCurveCoordinateOpen F i) :
    (planeCurveHyperplaneFrame F i).coordinate W hi
      ((PlaneCurveHyperplaneSheaf F).val.map (homOfLE (show W ≤ ⊤ from le_top)).op
        (planeCurveCoordinateSection F k)) =
      (show (PlaneCurveScheme F).ringCatSheaf.val.obj (op W) from
        UnitTransition.res hi (planeCurveCoordinateFunction F k i)) := rfl

/-- The generic coefficient of the actual global coordinate section is
exactly the normalized coordinate in the curve's actual function field.
This joins the constructed hyperplane sheaf to low-degree restriction. -/
theorem planeCurveCoordinateSection_generic (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i k : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] :
    schemeGenericLinearMap (K := K) (PlaneCurveHyperplaneSheaf F)
      (planeCurveCoordinateOpen F i) (planeCurveHyperplaneFrame F i)
      (planeCurveCoordinateSection F k) = planeCurveGenericCoordinates F i k := by
  change (PlaneCurveScheme F).germToFunctionField (planeCurveCoordinateOpen F i)
      (UnitTransition.res le_rfl (planeCurveCoordinateFunction F k i)) = _
  rw [UnitTransition.res_refl]
  exact planeCurveCoordinateFunction_generic F i k

/-- Quartic injectivity in precisely the form used by the theta theorem,
now for the constructed hyperplane sheaf and its constructed three global
sections on the actual plane quintic. The canonical base-field action is
identified with pullback of constant chart functions. -/
theorem planeQuintic_hyperplane_quartic_injective
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : F.totalDegree = 5) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    letI := planeCurveScheme_isIntegral F 5 hF (by omega) hprime
    letI := planeCurveCoordinateOpen_nonempty F 5 hF (by omega) hprime i
    ∀ P : PlanePolynomial K, P.IsHomogeneous 4 →
      MvPolynomial.aeval (fun k ↦ schemeGenericLinearMap (K := K)
        (PlaneCurveHyperplaneSheaf F) (planeCurveCoordinateOpen F i)
        (planeCurveHyperplaneFrame F i) (planeCurveCoordinateSection F k)) P = 0 →
      P = 0 := by
  letI := planeCurveScheme_isIntegral F 5 hF (by omega) hprime
  letI := planeCurveCoordinateOpen_nonempty F 5 hF (by omega) hprime i
  intro P hP hzero
  apply planeQuintic_actual_chart_quartic_injective F hF hFdeg hprime i P hP
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin 3) K) (MvPolynomial.X i)) :=
    inferInstanceAs (Nonempty (planeCurveCoordinateOpen F i))
  have hc : planeCurveGenericConstants F i =
      algebraMap K (PlaneCurveScheme F).functionField :=
    planeChartToFunctionField_constants_eq_algebraMap (planeCurveInclusion F) i
  rw [hc]
  simpa only [planeCurveCoordinateSection_generic] using hzero

end EvenQuinticConic
