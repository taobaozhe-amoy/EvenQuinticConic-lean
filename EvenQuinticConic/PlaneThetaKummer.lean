import EvenQuinticConic.QuadraticTraceZeroTransition
import EvenQuinticConic.LineBundleSquareTrivialization
import EvenQuinticConic.PlaneThetaTwoTorsion

/-!
# Theta twists from actual local quadratic-algebra multiplication

The input still includes an actual line cocycle and local Kummer models with
compatible generator coordinates. Preservation of multiplication by their
actual overlap homomorphisms proves the square coefficient identities; descent
then constructs the global square trivialization and the theta twist.

This is not yet the extraction of such charts or their cocycle from an arbitrary
finite étale discriminant cover. That geometric step remains unproved here.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars
universe u
namespace EvenQuinticConic
namespace UnitTransition
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (g : UnitTransition X U)

/-- Actual algebra homomorphisms between the restricted local quadratic models. -/
def KummerOverlapMaps (u : ∀ i, Γ(X, U i)ˣ) :=
  ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
    KummerAlgebra (X.presheaf.map (homOfLE hj).op (u j : Γ(X, U j))) →ₐ[Γ(X, V)]
      KummerAlgebra (X.presheaf.map (homOfLE hi).op (u i : Γ(X, U i)))

/-- The given line coordinates agree with the actual algebra generators. -/
def KummerOverlapCoordinates (u : ∀ i, Γ(X, U i)ˣ) (f : KummerOverlapMaps u) : Prop :=
  ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
    f i j V hi hj (kummerGenerator _) =
      (g.transition i j V hi hj : Γ(X, V)) • kummerGenerator _

/-- Square compatibility is proved from actual overlap multiplication. -/
theorem squareCoefficientsCompatible_of_kummerMaps
    (u : ∀ i, Γ(X, U i)ˣ) (f : KummerOverlapMaps u)
    (hf : g.KummerOverlapCoordinates u f) : g.SquareCoefficientsCompatible u := by
  intro i j V hi hj
  exact kummer_parameter_change (f i j V hi hj) _ (hf i j V hi hj)

/-- No global square isomorphism is assumed: local algebra multiplication constructs it. -/
def squareIsoOfKummerMaps (hcover : iSup U = ⊤)
    (u : ∀ i, Γ(X, U i)ˣ) (f : KummerOverlapMaps u)
    (hf : g.KummerOverlapCoordinates u f) :
    (g.mul g).moduleSheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  g.squareIsoOfLocalUnits hcover u (g.squareCoefficientsCompatible_of_kummerMaps u f hf)

end UnitTransition

variable {K : Type} [Field K] [IsAlgClosed K]

/-- The theta square is constructed from local quadratic multiplication. -/
def planeKummerThetaCotangentSquareIso
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (g : UnitTransition (PlaneCurveScheme F) U)
    (u : ∀ i, Γ(PlaneCurveScheme F, U i)ˣ)
    (f : UnitTransition.KummerOverlapMaps u) (hf : g.KummerOverlapCoordinates u f) :
    ((planeTorsionTwistTransition F U hU g).mul
      (planeTorsionTwistTransition F U hU g)).moduleSheaf ≅
        schemeKaehlerSheaf (planeCurveStructure F) :=
  planeTorsionThetaCotangentSquareIso F hF hFdeg hJac U hU g
    (g.squareIsoOfKummerMaps hU u f hf)

/-- Conditional even-section vanishing with actual local algebra maps as input,
without a supplied global line-square or theta-square isomorphism. -/
theorem planeQuintic_even_kummer_twist_sections_eq_zero
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (g : UnitTransition (PlaneCurveScheme F) U)
    (u : ∀ i, Γ(PlaneCurveScheme F, U i)ˣ)
    (f : UnitTransition.KummerOverlapMaps u) (hf : g.KummerOverlapCoordinates u f)
    (heven : Even (Module.finrank K ((PlaneTorsionThetaSheaf F U hU g).val.obj (op ⊤))))
    (s : (PlaneTorsionThetaSheaf F U hU g).val.obj (op ⊤)) : s = 0 :=
  planeQuintic_even_twoTorsion_twist_sections_eq_zero F hF hFdeg hJac U hU g
    (g.squareIsoOfKummerMaps hU u f hf) heven s

end EvenQuinticConic
