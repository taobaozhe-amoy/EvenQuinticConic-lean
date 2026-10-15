import EvenQuinticConic.PlaneCurveNoetherian
import EvenQuinticConic.PlaneThetaTraceZero
import EvenQuinticConic.SchemeFiniteEtaleData

/-!
# Theta twists constructed from a finite étale double cover

The input is an actual finite étale, flat morphism to the actual plane-curve
scheme, together with rank two on its canonical affine charts. The chart-ring
Noetherian and characteristic hypotheses follow from the base field. The
multiplicative charts, trace kernel, line cocycle, square trivialization, and
hyperplane twist are constructed internally.

The section-vanishing result remains conditional on parity. This file does
not identify a specified real discriminant cover, prove its parity, or prove
a conclusion about real connected components.
-/

noncomputable section
open scoped TensorProduct EvenQuinticConic.SchemeScalars
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
namespace EvenQuinticConic

variable {K : Type} [Field K]

/-- Rank two on the canonical affine charts of the actual plane-curve scheme. -/
def PlaneCoordinateRankTwo (F : PlanePolynomial K)
    {X : Scheme} (f : X ⟶ PlaneCurveScheme F) : Prop :=
  ∀ i : Fin 3,
    letI : Algebra Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i)
      Γ(X, f ⁻¹ᵁ planeCurveCoordinateOpen F i) :=
        (f.app (planeCurveCoordinateOpen F i)).hom.toAlgebra
    ∀ p : PrimeSpectrum Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i),
      Module.finrank (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal
          ⊗[Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i)]
            Γ(X, f ⁻¹ᵁ planeCurveCoordinateOpen F i)) = 2

variable [Invertible (2 : K)] (F : PlanePolynomial K)
    {X : Scheme} (f : X ⟶ PlaneCurveScheme F)
    [IsFinite f] [IsEtale f] [AlgebraicGeometry.Flat f]
    (hrank : PlaneCoordinateRankTwo F f)

/-- The actual categorical kernel of the uniquely characterized sheaf trace.
No additional Noetherian or section-ring unit hypotheses are supplied. -/
def PlaneFiniteEtaleTraceZeroSheaf : (PlaneCurveScheme F).Modules :=
  schemeFiniteEtaleTraceZeroSheaf f (planeCurveCoordinateOpen F)
    (planeCurveCoordinateOpen_cover F) (planeCurveCoordinateOpen_isAffine F) hrank

/-- The actual multiplicative cover is produced by the geometric hypotheses. -/
def planeFiniteEtaleKummerCover :=
  finiteEtaleKummerCover f (planeCurveCoordinateOpen F)
    (planeCurveCoordinateOpen_cover F) (planeCurveCoordinateOpen_isAffine F) hrank

/-- The line cocycle is extracted from the trace kernel of the given morphism. -/
def planeFiniteEtaleTraceZeroTransition :
    UnitTransition (PlaneCurveScheme F) (planeFiniteEtaleKummerCover F f hrank).openSet :=
  schemeFiniteEtaleTraceZeroTransition f (planeCurveCoordinateOpen F)
    (planeCurveCoordinateOpen_cover F) (planeCurveCoordinateOpen_isAffine F) hrank

/-- Descent identifies the cocycle sheaf with the actual categorical kernel. -/
def planeFiniteEtaleTraceZeroDescentIso :
    PlaneFiniteEtaleTraceZeroSheaf F f hrank ≅
      (planeFiniteEtaleTraceZeroTransition F f hrank).moduleSheaf :=
  schemeFiniteEtaleTraceZeroDescentIso f (planeCurveCoordinateOpen F)
    (planeCurveCoordinateOpen_cover F) (planeCurveCoordinateOpen_isAffine F) hrank

/-- The actual trace-zero line tensored with the hyperplane line. -/
def PlaneFiniteEtaleThetaSheaf : (PlaneCurveScheme F).Modules :=
  let d := planeFiniteEtaleKummerCover F f hrank
  PlaneTorsionThetaSheaf F d.openSet d.cover
    (planeFiniteEtaleTraceZeroTransition F f hrank)

/-- The constructed twist represents pairings on the actual trace kernel and
the actual hyperplane sheaf. -/
def planeFiniteEtaleThetaHomEquiv {P : (PlaneCurveScheme F).Modules} :
    (PlaneFiniteEtaleThetaSheaf F f hrank ⟶ P) ≃
      ModuleSheafPairing (PlaneFiniteEtaleTraceZeroSheaf F f hrank)
        (PlaneCurveHyperplaneSheaf F) P :=
  let d := planeFiniteEtaleKummerCover F f hrank
  let r := planeTorsionTwistRefinement F d.openSet d.cover
  let g := planeFiniteEtaleTraceZeroTransition F f hrank
  (g.refine r.openSet r.leftIndex r.le_left).productHomEquivOfIso
    ((planeCurveHyperplaneTransition F).refine r.openSet r.rightIndex r.le_right)
    r.cover
    (planeFiniteEtaleTraceZeroDescentIso F f hrank ≪≫
      (g.refineIso r.openSet r.leftIndex r.le_left r.cover).symm)
    ((planeCurveHyperplaneTransition F).refineIso
      r.openSet r.rightIndex r.le_right r.cover).symm

variable [IsAlgClosed K]

/-- On a smooth plane quintic the constructed twist squares to the actual
cotangent sheaf. The local charts and square isomorphism are not inputs. -/
def planeFiniteEtaleThetaCotangentSquareIso
    (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0) :
    let d := planeFiniteEtaleKummerCover F f hrank
    let t := planeTorsionTwistTransition F d.openSet d.cover
      (planeFiniteEtaleTraceZeroTransition F f hrank)
    (t.mul t).moduleSheaf ≅ schemeKaehlerSheaf (planeCurveStructure F) :=
  let d := planeFiniteEtaleKummerCover F f hrank
  planeTorsionThetaCotangentSquareIso F hF hFdeg hJac d.openSet d.cover
    (planeFiniteEtaleTraceZeroTransition F f hrank)
    (schemeFiniteEtaleTraceZeroSquareIso f (planeCurveCoordinateOpen F)
      (planeCurveCoordinateOpen_cover F) (planeCurveCoordinateOpen_isAffine F) hrank)

/-- Conditional on even parity, the geometrically constructed theta twist
has no nonzero global section. The given finite étale cover is the only
geometric input beyond its explicit flatness and rank-two hypotheses. -/
theorem planeQuintic_even_finiteEtale_theta_sections_eq_zero
    (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0)
    (heven : Even (Module.finrank K
      ((PlaneFiniteEtaleThetaSheaf F f hrank).val.obj (op ⊤))))
    (s : (PlaneFiniteEtaleThetaSheaf F f hrank).val.obj (op ⊤)) : s = 0 :=
  let d := planeFiniteEtaleKummerCover F f hrank
  planeQuintic_even_twoTorsion_twist_sections_eq_zero F hF hFdeg hJac
    d.openSet d.cover (planeFiniteEtaleTraceZeroTransition F f hrank)
    (schemeFiniteEtaleTraceZeroSquareIso f (planeCurveCoordinateOpen F)
      (planeCurveCoordinateOpen_cover F) (planeCurveCoordinateOpen_isAffine F) hrank)
    heven s

end EvenQuinticConic
