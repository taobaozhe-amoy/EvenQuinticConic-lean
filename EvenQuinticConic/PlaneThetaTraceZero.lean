import EvenQuinticConic.KummerTraceZeroDescent

/-!
# Theta twists of the internally constructed global trace kernel

The input is an actual module sheaf with a coherent quadratic-algebra atlas.
The trace morphism, trace kernel, its line cocycle, square trivialization,
and theta twist are constructed internally. Extraction of this atlas from
the specified finite étale discriminant cover is still a separate gap.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars
namespace EvenQuinticConic
variable {K : Type} [Field K] [Invertible (2 : K)] (F : PlanePolynomial K)
    {M : (PlaneCurveScheme F).Modules} {ι : Type}
    (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (a : KummerModuleAtlas M U)

/-- Invertibility of two on section rings is derived from the base field. -/
local instance planeTraceSectionsTwo (V : (PlaneCurveScheme F).Opens) :
    Invertible (2 : Γ(PlaneCurveScheme F, V)) :=
  (show IsUnit (2 : Γ(PlaneCurveScheme F, V)) from by
    simpa only [map_ofNat] using
      (isUnit_of_invertible (2 : K)).map ((schemeConstantsPresheafHom (planeCurveStructure F)).app (op V)).hom).invertible

/-- The actual hyperplane twist of the internally constructed trace kernel. -/
def PlaneTraceZeroThetaSheaf : (PlaneCurveScheme F).Modules :=
  PlaneTorsionThetaSheaf F U hU (a.traceZeroTransition hU)

/-- The twist represents pairings on the actual categorical trace kernel,
not merely on an independently supplied line cocycle. -/
def planeTraceZeroThetaHomEquiv {P : (PlaneCurveScheme F).Modules} :
    (PlaneTraceZeroThetaSheaf F U hU a ⟶ P) ≃
      ModuleSheafPairing (a.traceZeroSheaf hU) (PlaneCurveHyperplaneSheaf F) P :=
  let r := planeTorsionTwistRefinement F U hU
  let g := a.traceZeroTransition hU
  (g.refine r.openSet r.leftIndex r.le_left).productHomEquivOfIso
    ((planeCurveHyperplaneTransition F).refine r.openSet r.rightIndex r.le_right)
    r.cover (a.traceZeroDescentIso hU ≪≫ (g.refineIso r.openSet r.leftIndex r.le_left r.cover).symm)
    ((planeCurveHyperplaneTransition F).refineIso r.openSet r.rightIndex r.le_right r.cover).symm

variable [IsAlgClosed K]

/-- The cotangent-square comparison is constructed from the actual atlas trace kernel. -/
def planeTraceZeroThetaCotangentSquareIso
    (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0) :
    ((planeTorsionTwistTransition F U hU (a.traceZeroTransition hU)).mul
      (planeTorsionTwistTransition F U hU (a.traceZeroTransition hU))).moduleSheaf ≅
        schemeKaehlerSheaf (planeCurveStructure F) :=
  planeTorsionThetaCotangentSquareIso F hF hFdeg hJac U hU (a.traceZeroTransition hU)
    (a.traceZeroSquareIso hU)

/-- Even-section vanishing for the twist of the actual internally constructed
trace kernel. No trace morphism, line cocycle, or square isomorphism is an input. -/
theorem planeQuintic_even_trace_kernel_twist_sections_eq_zero
    (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0)
    (heven : Even (Module.finrank K ((PlaneTraceZeroThetaSheaf F U hU a).val.obj (op ⊤))))
    (s : (PlaneTraceZeroThetaSheaf F U hU a).val.obj (op ⊤)) : s = 0 :=
  planeQuintic_even_twoTorsion_twist_sections_eq_zero F hF hFdeg hJac U hU
    (a.traceZeroTransition hU) (a.traceZeroSquareIso hU) heven s

end EvenQuinticConic
