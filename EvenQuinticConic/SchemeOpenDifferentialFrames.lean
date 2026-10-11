import EvenQuinticConic.SchemeOpenModuleFrames
import EvenQuinticConic.SchemeKaehlerRestriction

/-!
# Differential generators of frames from open-subscheme trivializations

The comparison with the original open site is proved using the actual
image-top equality and the actual restriction maps. A differential generator
on the top of an open subscheme therefore gives the same differential on all
original subopens.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace EvenQuinticConic

universe u

variable {K : Type u} [CommRing K] {X : Scheme.{u}}

/-- A frame's inverse unit coordinate is unchanged by an equality of opens. -/
theorem moduleSheafFrame_inverseUnit_transport (M : X.Modules) {U V W : X.Opens}
    (e : ModuleSheafFrame M U) (h : V = W) (hV : V ≤ U) (hW : W ≤ U) :
    (h ▸ (e.coordinate V hV).symm 1) = (e.coordinate W hW).symm 1 := by
  subst W
  rfl

/-- The actual differential commutes with transport through equal open sets. -/
theorem schemeKaehlerDerivation_transport
    (f : X ⟶ Spec (CommRingCat.of K)) {V W : X.Opens}
    (h : V = W) (s : Γ(X, W)) :
    (h ▸ (schemeKaehlerDerivation f).d
      (X.presheaf.map (eqToHom h).op s)) =
        (schemeKaehlerDerivation f).d s := by
  subst W
  simp

/-- A genuine top differential generator on an open subscheme gives the
same generator on the original open. -/
theorem moduleSheafFrameOfSchemeOpenIso_generator_derivation
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (e : (schemeModuleRestrict U).obj (schemeKaehlerSheaf f) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : Γ(X, U))
    (hs : e.inv.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤)) =
      (schemeKaehlerDerivation f).d
        (X := op (U.ι ''ᵁ ⊤)) (U.topIso.inv s)) :
    ((moduleSheafFrameOfSchemeOpenIso (schemeKaehlerSheaf f) U e).coordinate U le_rfl).symm 1 =
      (schemeKaehlerDerivation f).d s := by
  let E := moduleSheafFrameOfSchemeOpenIso (schemeKaehlerSheaf f) U e
  have h := (moduleSheafFrameOfSchemeOpenIso_inverse_coordinate_image
    (schemeKaehlerSheaf f) U e ⊤ (1 : Γ(U.toScheme, ⊤))).trans hs
  have ht := congrArg (fun t : (schemeKaehlerSheaf f).val.obj (op (U.ι ''ᵁ ⊤)) =>
    U.ι_image_top ▸ t) h
  exact (moduleSheafFrame_inverseUnit_transport (schemeKaehlerSheaf f) E
    U.ι_image_top (U.ι_image_le ⊤) le_rfl).symm.trans
      (ht.trans (schemeKaehlerDerivation_transport f U.ι_image_top s))

/-- The differential generator remains the differential of the restricted
function on every original subopen, including the empty open. -/
theorem moduleSheafFrameOfSchemeOpenIso_generator_derivation_subopen
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (e : (schemeModuleRestrict U).obj (schemeKaehlerSheaf f) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : Γ(X, U))
    (hs : e.inv.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤)) =
      (schemeKaehlerDerivation f).d
        (X := op (U.ι ''ᵁ ⊤)) (U.topIso.inv s))
    (W : X.Opens) (hW : W ≤ U) :
    ((moduleSheafFrameOfSchemeOpenIso (schemeKaehlerSheaf f) U e).coordinate W hW).symm 1 =
      (schemeKaehlerDerivation f).d (X.presheaf.map (homOfLE hW).op s) := by
  let E := moduleSheafFrameOfSchemeOpenIso (schemeKaehlerSheaf f) U e
  have htop := moduleSheafFrameOfSchemeOpenIso_generator_derivation f U e s hs
  apply (E.coordinate W hW).injective
  rw [LinearEquiv.apply_symm_apply, schemeKaehlerDerivation_restrict, ← htop]
  rw [E.coordinate_restrict U W le_rfl hW hW, LinearEquiv.apply_symm_apply]
  exact (X.presheaf.map (homOfLE hW).op).hom.map_one.symm

/-- A genuine trivialization of the differential sheaf on an open subscheme
provides a frame of the global differential sheaf on the original open site. -/
def schemeOpenDifferentialFrame
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (e : schemeKaehlerSheaf (U.ι ≫ f) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ModuleSheafFrame (schemeKaehlerSheaf f) U :=
  moduleSheafFrameOfSchemeOpenIso (schemeKaehlerSheaf f) U
    (schemeKaehlerRestrictIso f U ≪≫ e)

/-- The frame produced from an actual local differential trivialization has
its specified actual differential generator on the original open. -/
theorem schemeOpenDifferentialFrame_generator
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (e : schemeKaehlerSheaf (U.ι ≫ f) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : Γ(X, U))
    (hs : e.inv.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤)) =
      (schemeKaehlerDerivation (U.ι ≫ f)).d (U.topIso.inv s)) :
    ((schemeOpenDifferentialFrame f U e).coordinate U le_rfl).symm 1 =
      (schemeKaehlerDerivation f).d s := by
  apply moduleSheafFrameOfSchemeOpenIso_generator_derivation f U
    (schemeKaehlerRestrictIso f U ≪≫ e) s
  change (schemeKaehlerRestrictIso f U).inv.val.app (op ⊤)
    (e.inv.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤))) = _
  rw [hs]
  exact schemeKaehlerRestrictIso_inv_derivation f U (op ⊤) (U.topIso.inv s)

/-- On every original subopen the same frame generator is the actual
differential of the restricted regular function. -/
theorem schemeOpenDifferentialFrame_generator_subopen
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (e : schemeKaehlerSheaf (U.ι ≫ f) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : Γ(X, U))
    (hs : e.inv.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤)) =
      (schemeKaehlerDerivation (U.ι ≫ f)).d (U.topIso.inv s))
    (W : X.Opens) (hW : W ≤ U) :
    ((schemeOpenDifferentialFrame f U e).coordinate W hW).symm 1 =
      (schemeKaehlerDerivation f).d (X.presheaf.map (homOfLE hW).op s) := by
  apply moduleSheafFrameOfSchemeOpenIso_generator_derivation_subopen f U
    (schemeKaehlerRestrictIso f U ≪≫ e) s _ W hW
  change (schemeKaehlerRestrictIso f U).inv.val.app (op ⊤)
    (e.inv.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤))) = _
  rw [hs]
  exact schemeKaehlerRestrictIso_inv_derivation f U (op ⊤) (U.topIso.inv s)

end EvenQuinticConic
