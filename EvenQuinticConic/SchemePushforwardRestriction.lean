import EvenQuinticConic.AffinePushforwardModule
import EvenQuinticConic.SchemeModuleRestriction

/-!
# Restriction of the actual pushforward of the structure sheaf

For an arbitrary scheme morphism, restricting its pushed-forward structure
module to a base open is canonically isomorphic to pushing forward the
structure module along the restricted morphism. The comparison is the genuine
structure-sheaf map induced by the equality of the corresponding source opens.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The actual structure sections used by the two pushforwards agree via the
canonical equality of their source opens. -/
def schemePushforwardRestrictionRingEquiv (V : U.toScheme.Opens) :
    Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ V)) ≃+* Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V) :=
  (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U V)).op).commRingCatIsoToRingEquiv

/-- The section comparison is the actual structure-sheaf map. -/
theorem schemePushforwardRestrictionRingEquiv_apply (V : U.toScheme.Opens)
    (s : Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ V))) :
    schemePushforwardRestrictionRingEquiv f U V s =
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op s := rfl

/-- The restricted scheme morphism supplies precisely the transported scalar
coefficient map. -/
theorem schemePushforwardRestrictionRingEquiv_coefficient (V : U.toScheme.Opens)
    (r : Γ(U.toScheme, V)) :
    schemePushforwardRestrictionRingEquiv f U V (f.app (U.ι ''ᵁ V) r) =
      (f ∣_ U).app V r := by
  rw [schemePushforwardRestrictionRingEquiv_apply, morphismRestrict_app]
  rfl

/-- On each open the actual comparison is linear for the genuine pushforward
scalar actions. -/
def schemePushforwardRestrictionLinearMap (V : U.toScheme.Opens) :
    ((schemeModuleRestrict U).obj
      ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).val.obj (op V)
      →ₗ[Γ(U.toScheme, V)]
    ((schemeModulePushforward (f ∣_ U)).obj
      (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)).val.obj (op V) where
  toFun := schemePushforwardRestrictionRingEquiv f U V
  map_add' := map_add _
  map_smul' r s := by
    change schemePushforwardRestrictionRingEquiv f U V
        (f.app (U.ι ''ᵁ V) r * (show Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ V)) from s)) =
      (f ∣_ U).app V r * schemePushforwardRestrictionRingEquiv f U V s
    rw [map_mul, schemePushforwardRestrictionRingEquiv_coefficient]

/-- The sectionwise comparison respects the actual restriction maps. -/
theorem schemePushforwardRestrictionLinearMap_restrict
    (V W : U.toScheme.Opens) (hWV : W ≤ V)
    (s : ((schemeModuleRestrict U).obj
      ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).val.obj (op V)) :
    schemePushforwardRestrictionLinearMap f U W
      (moduleRestrict ((schemeModuleRestrict U).obj
        ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) hWV s) =
    moduleRestrict ((schemeModulePushforward (f ∣_ U)).obj
      (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)) hWV
      (schemePushforwardRestrictionLinearMap f U V s) := by
  change X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W)).op
      (X.presheaf.map ((Opens.map f.base).map (U.ι.opensFunctor.map (homOfLE hWV))).op s) =
    X.presheaf.map
      ((f ⁻¹ᵁ U).ι.opensFunctor.map ((Opens.map (f ∣_ U).base).map (homOfLE hWV))).op
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op s)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← X.presheaf.map_comp, ← X.presheaf.map_comp]
  congr 2

/-- The canonical morphism comparing restriction and actual pushforward of the
structure module. -/
def schemePushforwardRestrictionHom :
    (schemeModuleRestrict U).obj
      ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ⟶
    (schemeModulePushforward (f ∣_ U)).obj
      (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        (X := ((schemeModuleRestrict U).obj
          ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).val.obj V)
        (Y := ((schemeModulePushforward (f ∣_ U)).obj
          (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)).val.obj V)
        (schemePushforwardRestrictionLinearMap f U V.unop)
      naturality := by
        intro V W g
        ext s
        exact schemePushforwardRestrictionLinearMap_restrict f U V.unop W.unop g.unop.le s }

/-- Restriction of the genuine pushforward structure module is canonically the
genuine pushforward structure module of the restricted scheme morphism. -/
def schemePushforwardRestrictionIso :
    (schemeModuleRestrict U).obj
      ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
    (schemeModulePushforward (f ∣_ U)).obj
      (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) :=
  moduleSheafIsoOfBijective (schemePushforwardRestrictionHom f U)
    (fun V ↦ (schemePushforwardRestrictionRingEquiv f U V.unop).bijective)

/-- The isomorphism acts by the canonical actual structure-section comparison. -/
theorem schemePushforwardRestrictionIso_hom_app (V : U.toScheme.Opens)
    (s : ((schemeModuleRestrict U).obj
      ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).val.obj (op V)) :
    (schemePushforwardRestrictionIso f U).hom.val.app (op V) s =
      schemePushforwardRestrictionRingEquiv f U V s := rfl

end EvenQuinticConic
