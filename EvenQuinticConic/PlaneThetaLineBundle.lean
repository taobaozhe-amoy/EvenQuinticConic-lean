import EvenQuinticConic.PlaneThetaVanishing
import EvenQuinticConic.AffineCommonRefinement
import EvenQuinticConic.LineBundleSquareIso
import EvenQuinticConic.NormalSchemeSections
import EvenQuinticConic.FrameCocycleDescent

/-!
# Theta vanishing from line-sheaf square isomorphisms

The caller supplies a line sheaf by actual unit transition data and an
actual isomorphism from its square-cocycle sheaf. The affine common
refinement, theta frames, square pairing and local tensor-perfectness are
constructed internally. Normality is stated at the actual scheme stalks.

The original smoothness, adjunction and discriminant-cover bridges remain
separate obligations; this is not the original real conic-bundle theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic

variable {K : Type} [Field K] [IsAlgClosed K]

/-- Even theta sections vanish on the actual normal prime plane quintic.
All refined local data and tensor-perfectness are consequences of the
original cocycle and actual square-sheaf isomorphism. -/
theorem planeQuintic_even_theta_sections_eq_zero_of_square_iso
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : F.totalDegree = 5) (hprime : (Ideal.span {F}).IsPrime)
    (hnormal : ∀ x : PlaneCurveScheme F,
      IsIntegrallyClosed ((PlaneCurveScheme F).presheaf.stalk x))
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (g : UnitTransition (PlaneCurveScheme F) U)
    (squareIso : (g.mul g).moduleSheaf ≅ PlaneCurveQuadraticSheaf F)
    (heven : Even (Module.finrank K (g.moduleSheaf.val.obj (op ⊤))))
    (s : g.moduleSheaf.val.obj (op ⊤)) : s = 0 := by
  letI := planeCurveScheme_isIntegral F 5 hF (by omega) hprime
  let r := affineCommonRefinement U (planeCurveCoordinateOpen F)
    hU (planeCurveCoordinateOpen_cover F)
  letI (x : PlaneCurveScheme F) : IsIntegrallyClosed Γ(PlaneCurveScheme F, r.openSet x) :=
    isIntegrallyClosed_sections_of_stalks (PlaneCurveScheme F) hnormal
      (r.openSet x) (r.affine x)
  exact planeQuintic_even_theta_sections_eq_zero_of_normal_frames F hF hFdeg hprime
    g.moduleSheaf (g.squarePairingOfIso squareIso) r.openSet r.cover r.affine
    r.rightIndex r.le_right
    (fun x ↦ (g.frame (r.leftIndex x)).restrict (r.le_left x))
    (fun x ↦ g.squarePairingOfIso_tensor_bijective squareIso
      (r.leftIndex x) (r.openSet x) (r.le_left x)) heven s

/-- The same vanishing statement for an independently given actual line
sheaf. Only its original local unit-sheaf isomorphisms and a square
isomorphism for their descended square are supplied. The cocycle, its
identification with the original sheaf, and all refined data are constructed. -/
theorem planeQuintic_even_theta_sections_eq_zero_of_local_trivializations
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : F.totalDegree = 5) (hprime : (Ideal.span {F}).IsPrime)
    (hnormal : ∀ x : PlaneCurveScheme F,
      IsIntegrallyClosed ((PlaneCurveScheme F).presheaf.stalk x))
    (Θ : (PlaneCurveScheme F).Modules)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (triv : ∀ i, Θ.over (U i) ≅
      SheafOfModules.unit ((PlaneCurveScheme F).ringCatSheaf.over (U i)))
    (squareIso :
      ((localTrivializationTransition U triv).mul
        (localTrivializationTransition U triv)).moduleSheaf ≅ PlaneCurveQuadraticSheaf F)
    (heven : Even (Module.finrank K (Θ.val.obj (op ⊤))))
    (s : Θ.val.obj (op ⊤)) : s = 0 := by
  let e := localTrivializationDescentIso U hU triv
  have heven' : Even (Module.finrank K
      ((localTrivializationTransition U triv).moduleSheaf.val.obj (op ⊤))) := by
    rw [← schemeGlobalSections_finrank_eq (K := K) e]
    exact heven
  apply (schemeGlobalSectionLinearEquiv (K := K) e).injective
  rw [map_zero]
  exact planeQuintic_even_theta_sections_eq_zero_of_square_iso F hF hFdeg hprime
    hnormal U hU (localTrivializationTransition U triv) squareIso heven' _

end EvenQuinticConic
