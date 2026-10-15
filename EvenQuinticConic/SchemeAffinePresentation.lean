import EvenQuinticConic.AffinePushforwardKummerAtlas
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Affine presentations of actual scheme morphisms

For an affine morphism, restriction to an affine base open is identified
with the spectrum of the actual pullback on section rings. The ring
properties below are obtained from geometric hypotheses on this same
morphism. Flatness is explicit: no equivalence between the scheme and
algebra definitions of étaleness is assumed.
-/

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory
namespace EvenQuinticConic
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The canonical affine presentations intertwine the restricted morphism
and the spectrum of its actual map on sections. -/
theorem affinePreimage_isoSpec_inv_naturality [IsAffineHom f] (hU : IsAffineOpen U) :
    Spec.map (f.app U) ≫ hU.isoSpec.inv =
      (hU.preimage f).isoSpec.inv ≫ (f ∣_ U) := by
  apply (cancel_mono U.ι).mp
  simpa only [Category.assoc, IsAffineOpen.isoSpec_inv_ι, morphismRestrict_ι,
    ← Scheme.Hom.app_eq_appLE] using
    IsAffineOpen.Spec_map_appLE_fromSpec f hU (hU.preimage f) le_rfl

/-- The forward presentation square commutes as actual scheme morphisms. -/
theorem affinePreimage_isoSpec_hom_naturality [IsAffineHom f] (hU : IsAffineOpen U) :
    (hU.preimage f).isoSpec.hom ≫ Spec.map (f.app U) =
      (f ∣_ U) ≫ hU.isoSpec.hom := by
  apply (cancel_mono hU.isoSpec.inv).mp
  simp only [Category.assoc, affinePreimage_isoSpec_inv_naturality,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- An affine presentation of the restricted arrow, with the original
section-ring pullback rather than a newly chosen ring homomorphism. -/
def affinePreimageArrowIso [IsAffineHom f] (hU : IsAffineOpen U) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (Spec.map (f.app U)) :=
  Arrow.isoMk (hU.preimage f).isoSpec hU.isoSpec
    (affinePreimage_isoSpec_hom_naturality f U hU)

/-- The algebra structure used in the Kummer theorem induces exactly the
spectral morphism in the canonical affine presentation. -/
theorem affinePreimage_specMap_algebraMap :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) =
      Spec.map (f.app U) := rfl

/-- Finiteness of the geometric morphism gives finiteness for the actual
section-ring algebra on an affine base open. -/
theorem finitePreimage_moduleFinite [IsFinite f] (hU : IsAffineOpen U) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  IsFinite.finite_app (f := f) U hU

/-- Over a Noetherian affine base open the same finite section algebra is
finitely presented as a module. -/
theorem finitePreimage_moduleFinitePresentation [IsFinite f] (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(Y, U)] :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  haveI : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := finitePreimage_moduleFinite f U hU
  exact Module.finitePresentation_of_finite _ _

/-- Geometric flatness descends to the actual affine preimage algebra. -/
theorem affinePreimage_moduleFlat [IsAffineHom f] [AlgebraicGeometry.Flat f]
    (hU : IsAffineOpen U) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  have h := AlgebraicGeometry.Flat.flat_of_affine_subset (f := f)
    ⟨U, hU⟩ ⟨f ⁻¹ᵁ U, hU.preimage f⟩ le_rfl
  simpa only [← Scheme.Hom.app_eq_appLE] using h

/-- Geometric étaleness gives formal unramifiedness of the same actual
section algebra; no local Kummer chart is supplied as a hypothesis. -/
theorem affinePreimage_formallyUnramified [IsAffineHom f] [IsEtale f]
    (hU : IsAffineOpen U) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Algebra.FormallyUnramified Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  have h := AlgebraicGeometry.FormallyUnramified.formallyUnramified_of_affine_subset (f := f)
    ⟨U, hU⟩ ⟨f ⁻¹ᵁ U, hU.preimage f⟩ le_rfl
  simpa only [← Scheme.Hom.app_eq_appLE] using h

/-- The geometric hypotheses produce actual algebra isomorphisms on a
principal-open cover of the canonical affine presentation. These retain
the multiplication needed for subsequent transport to the original base. -/
theorem exists_affinePreimageKummerModels [IsFinite f] [IsEtale f]
    [AlgebraicGeometry.Flat f] (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(Y, U)] [Invertible (2 : Γ(Y, U))]
    (hrank : letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
      ∀ p : PrimeSpectrum Γ(Y, U), Module.finrank (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U)) = 2) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    ∃ g : PrimeSpectrum Γ(Y, U) → Γ(Y, U),
      (⨆ p, PrimeSpectrum.basicOpen (g p)) = ⊤ ∧
      ∀ p, ∃ v : (Localization.Away (g p))ˣ,
        Nonempty ((Localization.Away (g p) ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U))
          ≃ₐ[Localization.Away (g p)] KummerAlgebra (v : Localization.Away (g p))) := by
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  haveI : Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    finitePreimage_moduleFinitePresentation f U hU
  haveI : Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := affinePreimage_moduleFlat f U hU
  haveI : Algebra.FormallyUnramified Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    affinePreimage_formallyUnramified f U hU
  exact exists_principal_unit_kummer_cover hrank

/-- Geometric finiteness, flatness and étaleness produce the covering
Kummer atlas for the canonical affine presentation of the restricted
cover. Rank two and invertibility of two are explicit; transporting this
atlas from the spectrum back to the original base open is a further step. -/
theorem exists_affinePreimageKummerAtlas [IsFinite f] [IsEtale f]
    [AlgebraicGeometry.Flat f] (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(Y, U)] [Invertible (2 : Γ(Y, U))]
    (hrank : letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
      ∀ p : PrimeSpectrum Γ(Y, U), Module.finrank (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U)) = 2) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    ∃ g : PrimeSpectrum Γ(Y, U) → Γ(Y, U),
      (⨆ p, PrimeSpectrum.basicOpen (g p)) = ⊤ ∧
      Nonempty (KummerModuleAtlas
        (affinePushforwardModule (R := Γ(Y, U)) (A := Γ(X, f ⁻¹ᵁ U)))
        (fun p => PrimeSpectrum.basicOpen (g p))) := by
  classical
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  obtain ⟨g, hg, hmodels⟩ := exists_affinePreimageKummerModels f U hU hrank
  choose v e using hmodels
  exact ⟨g, hg, ⟨affinePushforwardKummerAtlas g v (fun p => Classical.choice (e p))⟩⟩

end EvenQuinticConic
