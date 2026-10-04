import EvenQuinticConic.PlaneHyperplaneSheaf

/-!
# Restricting actual frames to common trivializing opens

The coordinate of a global section at the generic point is unchanged when
its actual local frame is restricted to a smaller nonempty open. Consequently
the proved quartic restriction statement for the actual hyperplane sheaf
holds on any nonempty refinement of a standard coordinate chart. This permits
an independently given theta frame to be chosen on that refinement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped EvenQuinticConic.SchemeScalars

universe u

namespace EvenQuinticConic

namespace ModuleSheafFrame

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  {M : SheafOfModules.{u} R} {U V : Opens X}

/-- Restrict an actual coherent local frame to any smaller open. -/
def restrict (frame : ModuleSheafFrame M U) (hVU : V ≤ U) :
    ModuleSheafFrame M V where
  coordinate W hWV := frame.coordinate W (hWV.trans hVU)
  coordinate_restrict W Z hWV hZV hZW s :=
    frame.coordinate_restrict W Z (hWV.trans hVU) (hZV.trans hVU) hZW s

@[simp]
theorem restrict_coordinate (frame : ModuleSheafFrame M U) (hVU : V ≤ U)
    (W : Opens X) (hWV : W ≤ V) (s : M.val.obj (op W)) :
    (frame.restrict hVU).coordinate W hWV s =
      frame.coordinate W (hWV.trans hVU) s := rfl

end ModuleSheafFrame

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] (M : X.Modules)

/-- Taking the coefficient in the actual function field commutes with
restricting a coherent local frame to a nonempty subopen. -/
theorem schemeGenericLinearMap_restrict
    {U V : X.Opens} [Nonempty U] [Nonempty V]
    (frame : ModuleSheafFrame M U) (hVU : V ≤ U) :
    schemeGenericLinearMap (K := K) M V (frame.restrict hVU) =
      schemeGenericLinearMap (K := K) M U frame := by
  ext s
  change moduleGenericCoefficient M V (frame.restrict hVU)
      (moduleGlobalSectionFamily M s) =
    moduleGenericCoefficient M U frame (moduleGlobalSectionFamily M s)
  unfold moduleGenericCoefficient
  change X.germToFunctionField V
      (frame.coordinate V hVU ((moduleGlobalSectionFamily M s).eval (op V))) = _
  rw [frame.coordinate_section_restrict]
  exact generic_germ_restrict X (homOfLE hVU) _

section PlaneCurve

variable {K : Type} [Field K]

/-- On every nonempty refinement of a standard chart, the generic
coefficient of the constructed coordinate section remains the actual
normalized projective coordinate. -/
theorem planeCurveCoordinateSection_generic_on_subopen (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i k : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)]
    (V : (PlaneCurveScheme F).Opens) [Nonempty V]
    (hVi : V ≤ planeCurveCoordinateOpen F i) :
    schemeGenericLinearMap (K := K) (PlaneCurveHyperplaneSheaf F) V
      ((planeCurveHyperplaneFrame F i).restrict hVi)
      (planeCurveCoordinateSection F k) = planeCurveGenericCoordinates F i k := by
  rw [schemeGenericLinearMap_restrict]
  exact planeCurveCoordinateSection_generic F i k

/-- The actual coordinate sections of the constructed hyperplane sheaf
satisfy quartic injectivity on any nonempty subopen of any standard chart.
No trivialization of a separate theta sheaf on the whole chart is required. -/
theorem planeQuintic_hyperplane_quartic_injective_on_subopen
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : F.totalDegree = 5) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3)
    (V : (PlaneCurveScheme F).Opens) [Nonempty V]
    (hVi : V ≤ planeCurveCoordinateOpen F i) :
    letI := planeCurveScheme_isIntegral F 5 hF (by omega) hprime
    ∀ P : PlanePolynomial K, P.IsHomogeneous 4 →
      MvPolynomial.aeval (fun k ↦ schemeGenericLinearMap (K := K)
        (PlaneCurveHyperplaneSheaf F) V
        ((planeCurveHyperplaneFrame F i).restrict hVi)
        (planeCurveCoordinateSection F k)) P = 0 → P = 0 := by
  letI := planeCurveScheme_isIntegral F 5 hF (by omega) hprime
  letI := planeCurveCoordinateOpen_nonempty F 5 hF (by omega) hprime i
  intro P hP hzero
  apply planeQuintic_hyperplane_quartic_injective F hF hFdeg hprime i P hP
  simpa only [schemeGenericLinearMap_restrict] using hzero

end PlaneCurve

end EvenQuinticConic
