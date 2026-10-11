import EvenQuinticConic.PlaneCurveDifferentialSheafFrames

/-!
# A genuine rank-one differential-sheaf cover from the Jacobian condition

The six derivative opens, their coordinate choices, and their actual local
unit-sheaf isomorphisms are constructed internally. The closed endpoint
takes the original polynomial Jacobian criterion, not local freeness or
an isomorphism hypothesis.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial

namespace EvenQuinticConic
variable {K : Type} [Field K]

/-- The actual differential frame at each member of the six-open cover. -/
def planeCurveDifferentialCoverFrame
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (a : PlaneDifferentialChartIndex) :
    ModuleSheafFrame (schemeKaehlerSheaf (planeCurveStructure F))
      (planeCurveDifferentialOpen F hF a.1 a.2.1) :=
  planeCurveDifferentialSheafFrame F hF hFdeg hprime a.1 a.2.1
    (planeDifferentialThirdCoordinate a.1 a.2.1) a.2.2
    (planeDifferentialThirdCoordinate_ne a.1 a.2.1).1
    (planeDifferentialThirdCoordinate_ne a.1 a.2.1).2

/-- The original nonsingular equation alone supplies each actual differential
frame; primality is proved internally from its Jacobian condition. -/
def planeQuinticDifferentialFrameOfJacobian [IsAlgClosed K]
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0)
    (a : PlaneDifferentialChartIndex) :
    ModuleSheafFrame (schemeKaehlerSheaf (planeCurveStructure F))
      (planeCurveDifferentialOpen F hF a.1 a.2.1) :=
  planeCurveDifferentialCoverFrame F hF (by omega)
    (plane_principal_isPrime_of_jacobian F 5 hF (by omega) hJac) a

/-- A nonsingular quintic equation gives an actual local differential-sheaf
trivialization around every point of its actual curve. -/
theorem planeQuintic_differentialSheaf_locallyTrivial_of_jacobian [IsAlgClosed K]
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0)
    (x : PlaneCurveScheme F) :
    ∃ U : (PlaneCurveScheme F).Opens, x ∈ U ∧
      Nonempty ((schemeKaehlerSheaf (planeCurveStructure F)).over U ≅
        SheafOfModules.unit ((PlaneCurveScheme F).ringCatSheaf.over U)) := by
  have hx : x ∈ (⨆ a : PlaneDifferentialChartIndex,
      planeCurveDifferentialOpen F hF a.1 a.2.1) := by
    rw [planeCurveDifferentialOpen_cover_of_jacobian F hF hJac]
    trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
  exact ⟨_, ha, ⟨(planeQuinticDifferentialFrameOfJacobian F hF hFdeg hJac a).localUnitIso⟩⟩

end EvenQuinticConic
