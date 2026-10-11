import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Smoothness after inverting a presentation Jacobian

A finite presentation with an injective choice of Jacobian columns becomes standard
smooth after its determinant is inverted. We retain the actual submersive presentation,
so its complementary coordinate differentials can subsequently be identified explicitly.
-/

namespace EvenQuinticConic

open Algebra

universe u v w w'

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} {σ : Type w'} [Finite ι] [Finite σ]

/-- The explicit submersive presentation obtained by adjoining the inverse of the
original Jacobian. The new generator and relation occupy the left `Unit` summands. -/
noncomputable def presentationJacobianLocalization
    (P : PreSubmersivePresentation R S ι σ)
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away P.jacobian T] :
    SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ σ) :=
  { toPreSubmersivePresentation :=
      (PreSubmersivePresentation.localizationAway T P.jacobian).comp P
    jacobian_isUnit := by
      have hu : IsUnit (algebraMap S T P.jacobian) :=
        IsLocalization.map_units T
          (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
      rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
      change IsUnit (P.jacobian •
        (PreSubmersivePresentation.localizationAway T P.jacobian).jacobian)
      rw [PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
      exact hu.mul hu }

omit [Finite ι] in
/-- The original coordinates survive unchanged, through the actual localization map. -/
theorem presentationJacobianLocalization_val_inr
    (P : PreSubmersivePresentation R S ι σ)
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away P.jacobian T] (i : ι) :
    (presentationJacobianLocalization P T).val (.inr i) = algebraMap S T (P.val i) :=
  rfl

/-- The actual localization of a finite presentation at its Jacobian is standard
smooth, with the relative dimension of the original presentation. -/
theorem presentation_jacobian_localization_isStandardSmooth
    (P : PreSubmersivePresentation R S ι σ)
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away P.jacobian T] :
    IsStandardSmoothOfRelativeDimension P.dimension R T := by
  apply (presentationJacobianLocalization P T).isStandardSmoothOfRelativeDimension
  change ((PreSubmersivePresentation.localizationAway T P.jacobian).comp P).dimension =
    P.dimension
  rw [PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  change (Presentation.localizationAway T P.jacobian).dimension + P.dimension = P.dimension
  rw [Presentation.localizationAway_dimension_zero, zero_add]

end EvenQuinticConic
