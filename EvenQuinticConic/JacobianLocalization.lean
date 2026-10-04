import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Smoothness after inverting a presentation Jacobian

A finite presentation with an injective choice of Jacobian columns becomes standard
smooth after its determinant is inverted. The proof uses the actual presentation
of the localization and the determinant formula for a composite presentation.
-/

namespace EvenQuinticConic

open Algebra

universe u v w w'

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} {σ : Type w'} [Finite ι] [Finite σ]

/-- The actual localization of a finite presentation at its Jacobian is standard
smooth, with the relative dimension of the original presentation. -/
theorem presentation_jacobian_localization_isStandardSmooth
    (P : PreSubmersivePresentation R S ι σ)
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away P.jacobian T] :
    IsStandardSmoothOfRelativeDimension P.dimension R T := by
  let Q := PreSubmersivePresentation.localizationAway T P.jacobian
  have hu : IsUnit (algebraMap S T P.jacobian) :=
    IsLocalization.map_units T (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
  let QP : SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    { toPreSubmersivePresentation := Q.comp P
      jacobian_isUnit := by
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
        change IsUnit (P.jacobian •
          (PreSubmersivePresentation.localizationAway T P.jacobian).jacobian)
        rw [PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
        exact hu.mul hu }
  apply QP.isStandardSmoothOfRelativeDimension
  change (Q.comp P).dimension = P.dimension
  rw [PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  change (Presentation.localizationAway T P.jacobian).dimension + P.dimension = P.dimension
  rw [Presentation.localizationAway_dimension_zero, zero_add]

end EvenQuinticConic
