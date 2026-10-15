import EvenQuinticConic.SchemePushforwardRestriction
import EvenQuinticConic.KummerModuleTransport

/-!
# Transport of pushforward atlases from a base open

A coherent atlas for the actual restricted morphism transports to the actual
pushforward on the original base scheme. The resulting image opens cover
exactly the base open, and the chart parameters are unchanged.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  {ι : Type u} {V : ι → U.toScheme.Opens}

/-- Transport a restricted-morphism atlas to image opens of the original base,
using the canonical actual pushforward isomorphism. -/
def schemePushforwardAtlasOpenImage
    (a : KummerModuleAtlas
      ((schemeModulePushforward (f ∣_ U)).obj
        (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)) V) :
    KummerModuleAtlas
      ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
      (fun i ↦ U.ι ''ᵁ V i) :=
  (a.transport (schemePushforwardRestrictionIso f U).symm).openImage

/-- The genuine coefficient units are unchanged by transport to image opens. -/
theorem schemePushforwardAtlasOpenImage_parameter
    (a : KummerModuleAtlas
      ((schemeModulePushforward (f ∣_ U)).obj
        (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)) V) (i : ι) :
    (schemePushforwardAtlasOpenImage f U a).parameter i = a.parameter i := rfl

/-- A covering atlas of the restricted morphism covers exactly the chosen
base open after transportation to the original scheme. -/
theorem schemePushforwardAtlasOpenImage_cover (hcover : iSup V = ⊤) :
    (⨆ i, U.ι ''ᵁ V i) = U :=
  schemeOpen_image_cover U V hcover

/-- Existence of an atlas for the restricted morphism gives an actual atlas
on opens of the original base whose union is precisely `U`. -/
theorem exists_schemePushforwardAtlasOnOpen
    (h : ∃ V : ι → U.toScheme.Opens, iSup V = ⊤ ∧
      Nonempty (KummerModuleAtlas
        ((schemeModulePushforward (f ∣_ U)).obj
          (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)) V)) :
    ∃ W : ι → Y.Opens, iSup W = U ∧
      Nonempty (KummerModuleAtlas
        ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) W) := by
  obtain ⟨V, hcover, ⟨a⟩⟩ := h
  exact ⟨(fun i ↦ U.ι ''ᵁ V i), schemeOpen_image_cover U V hcover,
    ⟨schemePushforwardAtlasOpenImage f U a⟩⟩

end EvenQuinticConic
