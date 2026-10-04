import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Normal stalks and affine section rings

For an integral scheme, integral closedness of its actual structure-sheaf
stalks implies integral closedness of every nonempty affine section ring.
The proof identifies the stalks at the points corresponding to maximal
ideals with localizations of the section ring.

Normality of the stalks remains a hypothesis here. In particular, this file
does not assert or assume that a smoothness predicate proves that hypothesis.
-/

noncomputable section

open AlgebraicGeometry

namespace EvenQuinticConic

/-- An integral scheme with integrally closed actual stalks has integrally
closed coordinate rings on its nonempty affine opens. -/
theorem isIntegrallyClosed_sections_of_stalks
    (X : Scheme) [IsIntegral X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let x : X := hU.fromSpec.base ⟨P, hP.isPrime⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf
      ⟨hU.fromSpec.base ⟨P, hP.isPrime⟩, (hU.isoSpec.inv.base _).2⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) P :=
    hU.isLocalization_stalk' ⟨P, hP.isPrime⟩ (hU.isoSpec.inv.base _).2
  exact (hnormal x).of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime P)).toRingEquiv

end EvenQuinticConic
