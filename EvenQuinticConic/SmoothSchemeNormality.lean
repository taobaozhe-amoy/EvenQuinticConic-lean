import EvenQuinticConic.SmoothCurveNormality
import EvenQuinticConic.NormalSchemeSections
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Actual smooth integral curves have normal stalks

Over a perfect field, an integral scheme smooth of relative dimension one
has integrally closed structure-sheaf stalks. The proof uses the actual
standard smooth affine charts supplied by the scheme morphism predicate,
then localizes their integrally closed coordinate rings.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace EvenQuinticConic

/-- Smoothness of the actual structure morphism of an integral curve over
a perfect field implies integral closedness of its actual stalks. -/
theorem smoothCurve_stalks_isIntegrallyClosed
    (K : Type u) [Field K] [PerfectField K]
    (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsSmoothOfRelativeDimension 1 f]
    (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨⟨U, hU⟩, V, hx, e, hf⟩ :=
    IsSmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := f) x
  have htop : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f.base x := Subsingleton.elim _ _
    exact hy ▸ e hx
  subst U
  letI : Nonempty V.1 := ⟨⟨x, hx⟩⟩
  let c : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let g : K →+* Γ(X, V.1) := (f.appLE ⊤ V.1 e).hom.comp c.toRingHom
  letI : Algebra K Γ(X, V.1) := g.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(X, V.1) :=
    (hf.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv c)).toAlgebra
  letI : IsIntegrallyClosed Γ(X, V.1) :=
    standardSmoothCurve_isIntegrallyClosed K Γ(X, V.1)
  letI : Algebra Γ(X, V.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x)
      (V.2.primeIdealOf ⟨x, hx⟩).asIdeal := V.2.isLocalization_stalk ⟨x, hx⟩
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    (V.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (V.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl_le_nonZeroDivisors

/-- Every nonempty affine coordinate ring of an actual smooth integral
curve over a perfect field is integrally closed. -/
theorem smoothCurve_affineSections_isIntegrallyClosed
    (K : Type u) [Field K] [PerfectField K]
    (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsSmoothOfRelativeDimension 1 f]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(X, U) :=
  isIntegrallyClosed_sections_of_stalks X
    (smoothCurve_stalks_isIntegrallyClosed K X f) U hU

end EvenQuinticConic
