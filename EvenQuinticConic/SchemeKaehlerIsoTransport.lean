import EvenQuinticConic.CommRingKaehlerIso
import EvenQuinticConic.SchemeKaehlerSheaf
import EvenQuinticConic.TopologyOpenRestriction
import EvenQuinticConic.ModuleSheafificationRestriction
import Mathlib.AlgebraicGeometry.OpenImmersion

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite TopologicalSpace

set_option maxHeartbeats 300000

universe u

namespace EvenQuinticConic

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i]

/-- The actual ring isomorphisms on the image opens of an open immersion. -/
noncomputable def schemeOpenImageRingHom : X.presheaf ⟶ i.opensFunctor.op ⋙ Y.presheaf where
  app U := (i.appIso U.unop).inv
  naturality _ _ j := i.appIso_inv_naturality j

/-- Restriction of actual module presheaves along the image opens of an open immersion. -/
noncomputable def schemeModuleOpenImagePresheaf : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.pushforward
    (whiskerRight (schemeOpenImageRingHom i) (forget₂ CommRingCat RingCat))

/-- The corresponding morphism of actual structure sheaves. -/
noncomputable def schemeOpenImageRingSheafHom :
    X.ringCatSheaf ⟶
      (letI := i.isOpenEmbedding.functor_isContinuous
       i.opensFunctor.sheafPushforwardContinuous RingCat
         (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj
      Y.ringCatSheaf :=
  ⟨whiskerRight (schemeOpenImageRingHom i) (forget₂ CommRingCat RingCat)⟩

/-- Transport of actual module sheaves along an open immersion, using its
actual isomorphisms on sections over image opens. -/
noncomputable def schemeModuleOpenImage : Y.Modules ⥤ X.Modules :=
  letI := i.isOpenEmbedding.functor_isContinuous
  SheafOfModules.pushforward (schemeOpenImageRingSheafHom i)

/-- The structure module is carried to the structure module under actual
transport, with coefficient map the inverse section-ring isomorphism. -/
noncomputable def schemeModuleOpenImageUnitMap :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (schemeModuleOpenImage i).obj (SheafOfModules.unit Y.ringCatSheaf) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (SheafOfModules.unit X.ringCatSheaf).val.obj U)
        (Y := ((schemeModuleOpenImage i).obj
          (SheafOfModules.unit Y.ringCatSheaf)).val.obj U)
        { toFun := (i.appIso U.unop).inv
          map_add' := map_add _
          map_smul' := fun a b ↦ (i.appIso U.unop).inv.hom.map_mul a b }
      naturality := fun {U V} j ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact ConcreteCategory.congr_hom (i.appIso_inv_naturality j) s }

/-- The actual structure-module comparison is an isomorphism. -/
noncomputable def schemeModuleOpenImageUnitIso :
    SheafOfModules.unit X.ringCatSheaf ≅
      (schemeModuleOpenImage i).obj (SheafOfModules.unit Y.ringCatSheaf) := by
  let c := schemeModuleOpenImageUnitMap i
  haveI (U : X.Opensᵒᵖ) : IsIso (c.val.app U) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact (ConcreteCategory.bijective_of_isIso (i.appIso U.unop).inv)
  exact (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ asIso (c.val.app U)) (fun {_ _} j ↦ c.val.naturality j))

@[simp]
theorem schemeModuleOpenImageUnitIso_hom_apply (U : X.Opens) (s : Γ(X, U)) :
    (schemeModuleOpenImageUnitIso i).hom.val.app (op U) s =
      (i.appIso U).inv s := rfl

variable {K : Type u} [CommRing K] (g : Y ⟶ Spec (CommRingCat.of K))

/-- Base constants agree under the actual section isomorphisms. -/
theorem schemeOpenImage_constants (U : X.Opens) :
    (schemeConstantsPresheafHom (i ≫ g)).app (op U) ≫ (i.appIso U).inv =
      (schemeConstantsPresheafHom g).app (op (i ''ᵁ U)) := by
  unfold schemeConstantsPresheafHom
  dsimp only
  rw [Scheme.comp_appTop]
  simp only [Category.assoc]
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop ≫
    i.appLE ⊤ U (by simp) ≫ (i.appIso U).inv = _
  rw [Scheme.Hom.appLE_appIso_inv]

/-- The sectionwise comparison is induced by the genuine ring isomorphism. -/
noncomputable def schemeKaehlerOpenImageMapApp (U : X.Opens) :
    (schemeKaehlerPresheaf (i ≫ g)).obj (op U) ⟶
      ((schemeModuleOpenImagePresheaf i).obj (schemeKaehlerPresheaf g)).obj (op U) := by
  change CommRingCat.KaehlerDifferential ((schemeConstantsPresheafHom (i ≫ g)).app (op U)) ⟶
    (ModuleCat.restrictScalars (i.appIso U).inv.hom).obj
      (CommRingCat.KaehlerDifferential ((schemeConstantsPresheafHom g).app (op (i ''ᵁ U))))
  exact CommRingCat.KaehlerDifferential.map
    (g := 𝟙 (CommRingCat.of K)) (g' := (i.appIso U).inv)
    (by simpa using (schemeOpenImage_constants i g U).symm)

@[simp]
theorem schemeKaehlerOpenImageMapApp_d (U : X.Opens) (s : Γ(X, U)) :
    schemeKaehlerOpenImageMapApp i g U (CommRingCat.KaehlerDifferential.d s) =
      CommRingCat.KaehlerDifferential.d ((i.appIso U).inv s) := by
  exact CommRingCat.KaehlerDifferential.map_d
    (g := 𝟙 (CommRingCat.of K)) (g' := (i.appIso U).inv)
    (by simpa using (schemeOpenImage_constants i g U).symm) s

/-- The genuine map on ring differentials induced by the section isomorphisms. -/
noncomputable def schemeKaehlerOpenImagePresheafMap :
    schemeKaehlerPresheaf (i ≫ g) ⟶
      (schemeModuleOpenImagePresheaf i).obj (schemeKaehlerPresheaf g) where
  app U := schemeKaehlerOpenImageMapApp i g U.unop
  naturality {U V} j := by
    apply CommRingCat.KaehlerDifferential.ext
      (f := (schemeConstantsPresheafHom (i ≫ g)).app U)
    intro s
    simp only [ModuleCat.comp_apply]
    erw [schemeKaehlerOpenImageMapApp_d i g U.unop s]
    have h1 := PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d
      (schemeConstantsPresheafHom (i ≫ g)) j s
    have h2 := PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d
      (schemeConstantsPresheafHom g) (i.opensFunctor.op.map j) ((i.appIso U.unop).inv s)
    erw [h1]
    erw [schemeKaehlerOpenImageMapApp_d i g V.unop (X.presheaf.map j s)]
    change CommRingCat.KaehlerDifferential.d _ = _
    erw [h2]
    exact congrArg CommRingCat.KaehlerDifferential.d
      (ConcreteCategory.congr_hom (i.appIso_inv_naturality j) s)

/-- The raw comparison preserves the actual universal differential. -/
@[simp]
theorem schemeKaehlerOpenImagePresheafMap_d (U : X.Opens) (s : Γ(X, U)) :
    (schemeKaehlerOpenImagePresheafMap i g).app (op U)
      (CommRingCat.KaehlerDifferential.d s) =
        CommRingCat.KaehlerDifferential.d ((i.appIso U).inv s) :=
  schemeKaehlerOpenImageMapApp_d i g U s

/-- Actual ring isomorphisms induce an isomorphism of differential presheaves. -/
noncomputable def schemeKaehlerOpenImagePresheafIso :
    schemeKaehlerPresheaf (i ≫ g) ≅
      (schemeModuleOpenImagePresheaf i).obj (schemeKaehlerPresheaf g) := by
  haveI (U : X.Opensᵒᵖ) : IsIso (schemeKaehlerOpenImageMapApp i g U.unop) := by
    exact commRingKaehlerMap_isIso (i.appIso U.unop).symm
      (by simpa using (schemeOpenImage_constants i g U.unop).symm)
  exact PresheafOfModules.isoMk
    (fun U ↦ asIso (schemeKaehlerOpenImageMapApp i g U.unop))
    (fun {_ _} j ↦ (schemeKaehlerOpenImagePresheafMap i g).naturality j)

/-- Relative differential sheaves commute with actual transport along an
open immersion. This is obtained from ring-differential isomorphisms and
the sheafification units, rather than an assertion about arbitrary sections. -/
noncomputable def schemeKaehlerOpenImageIso :
    schemeKaehlerSheaf (i ≫ g) ≅
      (schemeModuleOpenImage i).obj (schemeKaehlerSheaf g) := by
  letI := i.isOpenEmbedding.functor_isContinuous
  letI := openImageFunctor_isCocontinuous i.isOpenEmbedding.isOpenMap
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).mapIso
      (schemeKaehlerOpenImagePresheafIso i g) ≪≫
    moduleSheafificationPushforwardIso
      (F := i.opensFunctor) (S := X.ringCatSheaf) (R := Y.ringCatSheaf)
      (schemeOpenImageRingSheafHom i) (schemeKaehlerPresheaf g)

/-- The sheaf comparison is compatible with the genuine sheafification units. -/
theorem schemeKaehlerOpenImageIso_unit :
    schemeKaehlerSheafificationMap (i ≫ g) ≫ (schemeKaehlerOpenImageIso i g).hom.val =
      schemeKaehlerOpenImagePresheafMap i g ≫
        (schemeModuleOpenImagePresheaf i).map (schemeKaehlerSheafificationMap g) := by
  letI := i.isOpenEmbedding.functor_isContinuous
  letI := openImageFunctor_isCocontinuous i.isOpenEmbedding.isOpenMap
  let α := schemeKaehlerOpenImagePresheafMap i g
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)
  have hnat := adj.unit.naturality α
  change α ≫ adj.unit.app _ = adj.unit.app _ ≫
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map α).val at hnat
  change adj.unit.app _ ≫
    (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map α).val ≫
      (moduleSheafificationPushforwardComparison
        (F := i.opensFunctor) (S := X.ringCatSheaf) (R := Y.ringCatSheaf)
        (schemeOpenImageRingSheafHom i) (schemeKaehlerPresheaf g)).val) = _
  rw [← Category.assoc, ← hnat, Category.assoc]
  exact congrArg (fun β ↦ α ≫ β)
    (moduleSheafificationPushforwardComparison_unit
      (F := i.opensFunctor) (S := X.ringCatSheaf) (R := Y.ringCatSheaf)
      (schemeOpenImageRingSheafHom i) (schemeKaehlerPresheaf g))

/-- Transport preserves the actual differential on every open. -/
theorem schemeKaehlerOpenImageIso_hom_derivation (U : X.Opens) (s : Γ(X, U)) :
    (schemeKaehlerOpenImageIso i g).hom.val.app (op U)
      ((schemeKaehlerDerivation (i ≫ g)).d s) =
        (schemeKaehlerDerivation g).d ((i.appIso U).inv s) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun α ↦ α.app (op U)) (schemeKaehlerOpenImageIso_unit i g))
    (CommRingCat.KaehlerDifferential.d s)
  change (schemeKaehlerOpenImageIso i g).hom.val.app (op U)
      ((schemeKaehlerDerivation (i ≫ g)).d s) =
    (schemeKaehlerSheafificationMap g).app (op (i ''ᵁ U))
      ((schemeKaehlerOpenImagePresheafMap i g).app (op U)
        (CommRingCat.KaehlerDifferential.d s)) at h
  erw [schemeKaehlerOpenImagePresheafMap_d i g U s] at h
  exact h

/-- The inverse transport sends the differential of an image-open function
to the differential of its actual pullback. -/
theorem schemeKaehlerOpenImageIso_inv_derivation (U : X.Opens)
    (s : Γ(Y, i ''ᵁ U)) :
    (schemeKaehlerOpenImageIso i g).inv.val.app (op U)
      ((schemeKaehlerDerivation g).d s) =
        (schemeKaehlerDerivation (i ≫ g)).d ((i.appIso U).hom s) := by
  let E := (SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso
    (schemeKaehlerOpenImageIso i g)
  apply (ConcreteCategory.bijective_of_isIso E.hom).injective
  change E.hom (E.inv _) = _
  rw [← ModuleCat.comp_apply, E.inv_hom_id, ModuleCat.id_apply]
  erw [schemeKaehlerOpenImageIso_hom_derivation i g U ((i.appIso U).hom s)]
  congr 1
  exact (ConcreteCategory.congr_hom (i.appIso U).hom_inv_id s).symm

end EvenQuinticConic
