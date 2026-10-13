import EvenQuinticConic.LineBundleTwoTorsion
import EvenQuinticConic.PlaneThetaAdjunction

/-!
# The actual theta twist of a square-trivial line sheaf on a plane quintic

Start with an actual unit cocycle on an arbitrary open cover and an actual
trivialization of its square. A common refinement with the hyperplane charts
constructs its tensor product with the hyperplane sheaf. The tensor universal
property identifies the factors with the original actual sheaves, and the
square isomorphism to the actual differential sheaf is constructed internally.

This does not construct a trace-zero line sheaf from a specified finite etale
double cover, nor prove its parity or any real-geometric conclusion.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars
namespace EvenQuinticConic
variable {K : Type} [Field K]

def planeTorsionTwistRefinement (F : PlanePolynomial K)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤) :
    AffineCommonRefinement U (planeCurveCoordinateOpen F) :=
  affineCommonRefinement U (planeCurveCoordinateOpen F) hU (planeCurveCoordinateOpen_cover F)

def planeTorsionTwistTransition (F : PlanePolynomial K)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (g : UnitTransition (PlaneCurveScheme F) U) :
    UnitTransition (PlaneCurveScheme F) (planeTorsionTwistRefinement F U hU).openSet :=
  let r := planeTorsionTwistRefinement F U hU
  (g.refine r.openSet r.leftIndex r.le_left).mul
    ((planeCurveHyperplaneTransition F).refine r.openSet r.rightIndex r.le_right)

def PlaneTorsionThetaSheaf (F : PlanePolynomial K)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (g : UnitTransition (PlaneCurveScheme F) U) : (PlaneCurveScheme F).Modules :=
  (planeTorsionTwistTransition F U hU g).moduleSheaf

/-- The twist represents pairings on the original, unrefined factors. -/
def planeTorsionThetaHomEquiv (F : PlanePolynomial K)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (g : UnitTransition (PlaneCurveScheme F) U) {P : (PlaneCurveScheme F).Modules} :
    (PlaneTorsionThetaSheaf F U hU g ⟶ P) ≃
      ModuleSheafPairing g.moduleSheaf (PlaneCurveHyperplaneSheaf F) P :=
  let r := planeTorsionTwistRefinement F U hU
  (g.refine r.openSet r.leftIndex r.le_left).productHomEquivOfIso
    ((planeCurveHyperplaneTransition F).refine r.openSet r.rightIndex r.le_right)
    r.cover (g.refineIso r.openSet r.leftIndex r.le_left r.cover).symm
    ((planeCurveHyperplaneTransition F).refineIso
      r.openSet r.rightIndex r.le_right r.cover).symm

def planeTorsionThetaSquareIso (F : PlanePolynomial K)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (g : UnitTransition (PlaneCurveScheme F) U)
    (e : (g.mul g).moduleSheaf ≅ SheafOfModules.unit (PlaneCurveScheme F).ringCatSheaf) :
    ((planeTorsionTwistTransition F U hU g).mul
      (planeTorsionTwistTransition F U hU g)).moduleSheaf ≅ PlaneCurveQuadraticSheaf F :=
  let r := planeTorsionTwistRefinement F U hU
  (g.refine r.openSet r.leftIndex r.le_left).twoTorsionTwistSquareIso
    ((planeCurveHyperplaneTransition F).refine r.openSet r.rightIndex r.le_right)
    r.cover (g.refineSquareTrivialization r.openSet r.leftIndex r.le_left r.cover e) ≪≫
  ((planeCurveHyperplaneTransition F).mul (planeCurveHyperplaneTransition F)).refineIso
    r.openSet r.rightIndex r.le_right r.cover

variable [IsAlgClosed K]

/-- Neither the theta object nor its cotangent square is an extra input. -/
def planeTorsionThetaCotangentSquareIso
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (g : UnitTransition (PlaneCurveScheme F) U)
    (e : (g.mul g).moduleSheaf ≅ SheafOfModules.unit (PlaneCurveScheme F).ringCatSheaf) :
    ((planeTorsionTwistTransition F U hU g).mul
      (planeTorsionTwistTransition F U hU g)).moduleSheaf ≅
        schemeKaehlerSheaf (planeCurveStructure F) :=
  planeTorsionThetaSquareIso F U hU g e ≪≫
    (planeQuinticAdjunctionIsoOfJacobian F hF hFdeg hJac).symm

/-- Conditional on parity, the actual constructed twist has no nonzero sections. -/
theorem planeQuintic_even_twoTorsion_twist_sections_eq_zero
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (g : UnitTransition (PlaneCurveScheme F) U)
    (e : (g.mul g).moduleSheaf ≅ SheafOfModules.unit (PlaneCurveScheme F).ringCatSheaf)
    (heven : Even (Module.finrank K ((PlaneTorsionThetaSheaf F U hU g).val.obj (op ⊤))))
    (s : (PlaneTorsionThetaSheaf F U hU g).val.obj (op ⊤)) : s = 0 := by
  let r := planeTorsionTwistRefinement F U hU
  let t := planeTorsionTwistTransition F U hU g
  apply planeQuintic_even_theta_sections_eq_zero_of_cotangent_square F hF hFdeg hJac
    t.moduleSheaf r.openSet r.cover (fun i ↦ (t.frame i).localUnitIso) _ heven s
  rw [UnitTransition.localTrivializationTransition_frame]
  exact planeTorsionThetaCotangentSquareIso F hF hFdeg hJac U hU g e

end EvenQuinticConic
