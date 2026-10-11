import EvenQuinticConic.SchemeModuleRestriction
import EvenQuinticConic.LocalTrivializationFrames

/-!
# Frames on the original site from an actual open-subscheme trivialization

The module category on an actual open subscheme and the slice site `Over U`
are kept distinct. A genuine trivialization on the open subscheme is evaluated
on inverse-image opens, and the proved image-preimage equality transports its
coordinates back to every original subopen. Naturality supplies a coherent
frame and hence the actual local isomorphism on `Over U`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace EvenQuinticConic

universe u
variable {X : Scheme.{u}}

/-- An open already contained in `U` is recovered from its actual inverse image. -/
theorem schemeOpen_image_preimage_of_le (U V : X.Opens) (hV : V ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inter, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr hV]

/-- Evaluating a genuine open-subscheme trivialization gives coordinates on
its actual image open, with the original structure-ring action. -/
def schemeOpenModuleCoordinate (M : X.Modules) (U : X.Opens)
    (e : (schemeModuleRestrict U).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V : U.toScheme.Opens) :
    M.val.obj (op (U.ι ''ᵁ V)) ≃ₗ[Γ(X, U.ι ''ᵁ V)] Γ(X, U.ι ''ᵁ V) :=
  ((SheafOfModules.evaluation U.toScheme.ringCatSheaf (op V)).mapIso e).toLinearEquiv

/-- These coordinates commute with the original restriction maps on image opens. -/
theorem schemeOpenModuleCoordinate_restrict (M : X.Modules) (U : X.Opens)
    (e : (schemeModuleRestrict U).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V W : U.toScheme.Opens) (hWV : W ≤ V)
    (s : M.val.obj (op (U.ι ''ᵁ V))) :
    schemeOpenModuleCoordinate M U e W
      (M.val.map (U.ι.opensFunctor.map (homOfLE hWV)).op s) =
      X.presheaf.map (U.ι.opensFunctor.map (homOfLE hWV)).op
        (schemeOpenModuleCoordinate M U e V s) :=
  PresheafOfModules.naturality_apply e.hom.val (homOfLE hWV).op s

/-- Naturality of linear coordinates survives transport along actual equalities
of open sets. This lemma only transports equality; it adds no frame hypotheses. -/
theorem moduleCoordinates_transport_restrict (M : X.Modules)
    {V W V' W' : X.Opens} (hV : V' = V) (hW : W' = W)
    (hWV : W ≤ V) (hW'V' : W' ≤ V')
    (eV : M.val.obj (op V') ≃ₗ[Γ(X, V')] Γ(X, V'))
    (eW : M.val.obj (op W') ≃ₗ[Γ(X, W')] Γ(X, W'))
    (he : ∀ s, eW (M.val.map (homOfLE hW'V').op s) =
      X.presheaf.map (homOfLE hW'V').op (eV s))
    (s : M.val.obj (op V)) :
    (hW ▸ eW) (M.val.map (homOfLE hWV).op s) =
      X.presheaf.map (homOfLE hWV).op ((hV ▸ eV) s) := by
  subst V'
  subst W'
  exact he s

/-- An actual unit-sheaf trivialization on the open subscheme gives a coherent
frame on all original subopens of `U`, including the empty open. -/
def moduleSheafFrameOfSchemeOpenIso (M : X.Modules) (U : X.Opens)
    (e : (schemeModuleRestrict U).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ModuleSheafFrame M U where
  coordinate V hV := schemeOpen_image_preimage_of_le U V hV ▸
    schemeOpenModuleCoordinate M U e (U.ι ⁻¹ᵁ V)
  coordinate_restrict V W hV hW hWV s := by
    apply moduleCoordinates_transport_restrict M
      (schemeOpen_image_preimage_of_le U V hV)
      (schemeOpen_image_preimage_of_le U W hW) hWV
      (U.ι.image_le_image_of_le (show U.ι ⁻¹ᵁ W ≤ U.ι ⁻¹ᵁ V from fun _ hx => hWV hx))
    intro t
    exact schemeOpenModuleCoordinate_restrict M U e
      (U.ι ⁻¹ᵁ V) (U.ι ⁻¹ᵁ W) (show U.ι ⁻¹ᵁ W ≤ U.ι ⁻¹ᵁ V from fun _ hx => hWV hx) t

/-- Equality transport agrees with evaluation at equal opens. -/
theorem schemeOpenModuleCoordinate_transport (M : X.Modules) (U : X.Opens)
    (e : (schemeModuleRestrict U).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V W : U.toScheme.Opens) (h : V = W) (himage : U.ι ''ᵁ V = U.ι ''ᵁ W) :
    (himage ▸ schemeOpenModuleCoordinate M U e V) =
      schemeOpenModuleCoordinate M U e W := by
  subst W
  rfl

/-- On an actual image open, the transported frame recovers evaluation
of the original open-subscheme isomorphism without an extra transport. -/
theorem moduleSheafFrameOfSchemeOpenIso_coordinate_image (M : X.Modules) (U : X.Opens)
    (e : (schemeModuleRestrict U).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V : U.toScheme.Opens) (s : M.val.obj (op (U.ι ''ᵁ V))) :
    (moduleSheafFrameOfSchemeOpenIso M U e).coordinate
      (U.ι ''ᵁ V) (U.ι_image_le V) s = schemeOpenModuleCoordinate M U e V s := by
  exact congrArg (fun c => c s) (schemeOpenModuleCoordinate_transport M U e
    (U.ι ⁻¹ᵁ (U.ι ''ᵁ V)) V (U.ι.preimage_image_eq V)
    (schemeOpen_image_preimage_of_le U (U.ι ''ᵁ V) (U.ι_image_le V)))

/-- The inverse coordinates on an image open are precisely the original
inverse sheaf morphism. In particular, this identifies the actual generator. -/
theorem moduleSheafFrameOfSchemeOpenIso_inverse_coordinate_image
    (M : X.Modules) (U : X.Opens)
    (e : (schemeModuleRestrict U).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V : U.toScheme.Opens) (r : Γ(U.toScheme, V)) :
    ((moduleSheafFrameOfSchemeOpenIso M U e).coordinate
      (U.ι ''ᵁ V) (U.ι_image_le V)).symm r = e.inv.val.app (op V) r := by
  apply ((moduleSheafFrameOfSchemeOpenIso M U e).coordinate
    (U.ι ''ᵁ V) (U.ι_image_le V)).injective
  rw [LinearEquiv.apply_symm_apply, moduleSheafFrameOfSchemeOpenIso_coordinate_image]
  exact ((schemeOpenModuleCoordinate M U e V).apply_symm_apply r).symm

/-- The resulting local isomorphism lives on the original `Over U` site;
no identification of the two module categories is assumed. -/
def schemeOpenIsoToLocalUnitIso (M : X.Modules) (U : X.Opens)
    (e : (schemeModuleRestrict U).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (moduleSheafFrameOfSchemeOpenIso M U e).localUnitIso

end EvenQuinticConic
