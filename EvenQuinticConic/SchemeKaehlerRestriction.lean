import EvenQuinticConic.SchemeModuleRestriction
import EvenQuinticConic.SchemeKaehlerSheaf
import EvenQuinticConic.ModuleSheafificationRestriction
import EvenQuinticConic.TopologyOpenRestriction
import EvenQuinticConic.CommRingKaehlerIso

/-!
# Restriction of the actual differential sheaf

The square of actual base constants induces the genuine ring differential
maps on every open of an open subscheme. Their naturality gives a raw
presheaf isomorphism. Cocontinuity of the open-image functor then identifies
the two actual sheafifications, compatibly with their universal differentials.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite TopologicalSpace

universe u


namespace EvenQuinticConic

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {K : Type u} [CommRing K] {X : Scheme.{u}}

/-- Actual pullback of constants commutes with passage to an open subscheme. -/
theorem schemeConstantsPresheafHom_restrict
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) :
    schemeConstantsPresheafHom (U.ι ≫ f) =
      whiskerLeft U.ι.opensFunctor.op (schemeConstantsPresheafHom f) := by
  ext1
  funext V
  dsimp only [schemeConstantsPresheafHom, whiskerLeft_app]
  rw [Scheme.comp_appTop, Category.assoc, Scheme.Opens.ι_appTop]
  rw [Scheme.Opens.toScheme_presheaf_map, ← Functor.map_comp]
  rfl

/-- The square of actual constants for the identity map of an open section ring. -/
theorem schemeConstantsRestrictionSquare
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (V : U.toScheme.Opensᵒᵖ) :
    (𝟙 (CommRingCat.of K)) ≫ (schemeConstantsPresheafHom (U.ι ≫ f)).app V =
      (schemeConstantsPresheafHom f).app (U.ι.opensFunctor.op.obj V) ≫
        (Iso.refl (U.toScheme.presheaf.obj V)).hom := by
  simpa only [Category.id_comp, Iso.refl_hom, Category.comp_id, whiskerLeft_app]
    using congrArg (fun g => g.app V) (schemeConstantsPresheafHom_restrict f U)

/-- On actual open subschemes, the raw differential presheaves are canonically isomorphic. -/
noncomputable def schemeKaehlerPresheafRestrictIso
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) :
    (schemeModulePresheafRestrict U).obj (schemeKaehlerPresheaf f) ≅
      schemeKaehlerPresheaf (U.ι ≫ f) :=
  PresheafOfModules.isoMk (fun V =>
    commRingKaehlerIso (Iso.refl (U.toScheme.presheaf.obj V))
      (schemeConstantsRestrictionSquare f U V)) (by
    intro V W i
    apply CommRingCat.KaehlerDifferential.ext
    intro s
    simp only [ModuleCat.comp_apply]
    change CommRingCat.KaehlerDifferential.map (schemeConstantsRestrictionSquare f U W)
        ((schemeKaehlerPresheaf f).map (U.ι.opensFunctor.op.map i)
          (CommRingCat.KaehlerDifferential.d
            (f := (schemeConstantsPresheafHom f).app (U.ι.opensFunctor.op.obj V)) s)) =
      (schemeKaehlerPresheaf (U.ι ≫ f)).map i
        (CommRingCat.KaehlerDifferential.map (schemeConstantsRestrictionSquare f U V)
          (CommRingCat.KaehlerDifferential.d s))
    change CommRingCat.KaehlerDifferential.map (schemeConstantsRestrictionSquare f U W)
        (CommRingCat.KaehlerDifferential.map
          ((schemeConstantsPresheafHom f).naturality (U.ι.opensFunctor.op.map i))
          (CommRingCat.KaehlerDifferential.d s)) =
      CommRingCat.KaehlerDifferential.map
        ((schemeConstantsPresheafHom (U.ι ≫ f)).naturality i)
        (CommRingCat.KaehlerDifferential.map (schemeConstantsRestrictionSquare f U V)
          (CommRingCat.KaehlerDifferential.d s))
    rw [CommRingCat.KaehlerDifferential.map_d, CommRingCat.KaehlerDifferential.map_d,
      CommRingCat.KaehlerDifferential.map_d, CommRingCat.KaehlerDifferential.map_d]
    rfl)

@[simp]
theorem schemeKaehlerPresheafRestrictIso_hom_d
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (V : U.toScheme.Opensᵒᵖ) (s : U.toScheme.presheaf.obj V) :
    (schemeKaehlerPresheafRestrictIso f U).hom.app V
      (CommRingCat.KaehlerDifferential.d
        (f := (schemeConstantsPresheafHom f).app (U.ι.opensFunctor.op.obj V)) s) =
      CommRingCat.KaehlerDifferential.d
        (f := (schemeConstantsPresheafHom (U.ι ≫ f)).app V) s :=
  CommRingCat.KaehlerDifferential.map_d (schemeConstantsRestrictionSquare f U V) s

@[simp]
theorem schemeKaehlerPresheafRestrictIso_inv_d
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (V : U.toScheme.Opensᵒᵖ) (s : U.toScheme.presheaf.obj V) :
    (schemeKaehlerPresheafRestrictIso f U).inv.app V
      (CommRingCat.KaehlerDifferential.d
        (f := (schemeConstantsPresheafHom (U.ι ≫ f)).app V) s) =
      CommRingCat.KaehlerDifferential.d
        (f := (schemeConstantsPresheafHom f).app (U.ι.opensFunctor.op.obj V)) s :=
  commRingKaehlerIso_inv_d (Iso.refl (U.toScheme.presheaf.obj V))
    (schemeConstantsRestrictionSquare f U V) s

/-- The actual differential sheaf commutes with restriction to an actual open subscheme. -/
noncomputable def schemeKaehlerRestrictIso
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) :
    (schemeModuleRestrict U).obj (schemeKaehlerSheaf f) ≅
      schemeKaehlerSheaf (U.ι ≫ f) := by
  letI := U.ι.isOpenEmbedding.functor_isContinuous
  letI := openImageFunctor_isCocontinuous U.ι.isOpenEmbedding.isOpenMap
  dsimp only [schemeModuleRestrict, schemeKaehlerSheaf]
  exact (moduleSheafificationPushforwardIso (F := U.ι.opensFunctor)
    (R := X.ringCatSheaf) (S := U.toScheme.ringCatSheaf)
    (𝟙 U.toScheme.ringCatSheaf) (schemeKaehlerPresheaf f)).symm ≪≫
      (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.val)).mapIso
        (schemeKaehlerPresheafRestrictIso f U)

/-- The inverse restriction comparison is compatible with both actual sheafification units. -/
theorem schemeKaehlerRestrictIso_inv_unit
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) :
    schemeKaehlerSheafificationMap (U.ι ≫ f) ≫
        (schemeKaehlerRestrictIso f U).inv.val =
      (schemeKaehlerPresheafRestrictIso f U).inv ≫
        (schemeModulePresheafRestrict U).map (schemeKaehlerSheafificationMap f) := by
  letI := U.ι.isOpenEmbedding.functor_isContinuous
  letI := openImageFunctor_isCocontinuous U.ι.isOpenEmbedding.isOpenMap
  let e := schemeKaehlerPresheafRestrictIso f U
  let c := moduleSheafificationPushforwardComparison (F := U.ι.opensFunctor)
    (R := X.ringCatSheaf) (S := U.toScheme.ringCatSheaf)
    (𝟙 U.toScheme.ringCatSheaf) (schemeKaehlerPresheaf f)
  change schemeKaehlerSheafificationMap (U.ι ≫ f) ≫
      ((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.val)).map e.inv).val ≫
        c.val = _
  rw [← Category.assoc]
  have hn := (PresheafOfModules.sheafificationAdjunction
    (𝟙 U.toScheme.ringCatSheaf.val)).unit.naturality e.inv
  change e.inv ≫ (PresheafOfModules.sheafificationAdjunction
    (𝟙 U.toScheme.ringCatSheaf.val)).unit.app _ =
      schemeKaehlerSheafificationMap (U.ι ≫ f) ≫
        ((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.val)).map e.inv).val at hn
  rw [← hn, Category.assoc]
  exact congrArg (fun g => e.inv ≫ g)
    (moduleSheafificationPushforwardComparison_unit (F := U.ι.opensFunctor)
      (R := X.ringCatSheaf) (S := U.toScheme.ringCatSheaf)
      (𝟙 U.toScheme.ringCatSheaf) (schemeKaehlerPresheaf f))

/-- The inverse restriction isomorphism preserves the differential of every regular section. -/
theorem schemeKaehlerRestrictIso_inv_derivation
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (V : U.toScheme.Opensᵒᵖ) (s : U.toScheme.presheaf.obj V) :
    (schemeKaehlerRestrictIso f U).inv.val.app V
      ((schemeKaehlerDerivation (U.ι ≫ f)).d s) =
        (schemeKaehlerDerivation f).d
          (X := U.ι.opensFunctor.op.obj V) s := by
  have h := congrArg (fun g => g.app V
    (CommRingCat.KaehlerDifferential.d
      (f := (schemeConstantsPresheafHom (U.ι ≫ f)).app V) s))
        (schemeKaehlerRestrictIso_inv_unit f U)
  change (schemeKaehlerRestrictIso f U).inv.val.app V
      ((schemeKaehlerDerivation (U.ι ≫ f)).d s) =
    (schemeKaehlerSheafificationMap f).app (U.ι.opensFunctor.op.obj V)
      ((schemeKaehlerPresheafRestrictIso f U).inv.app V
        (CommRingCat.KaehlerDifferential.d
          (f := (schemeConstantsPresheafHom (U.ι ≫ f)).app V) s)) at h
  rw [schemeKaehlerPresheafRestrictIso_inv_d] at h
  exact h

/-- The restriction isomorphism preserves the differential of every regular section. -/
theorem schemeKaehlerRestrictIso_hom_derivation
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (V : U.toScheme.Opensᵒᵖ) (s : U.toScheme.presheaf.obj V) :
    (schemeKaehlerRestrictIso f U).hom.val.app V
      ((schemeKaehlerDerivation f).d (X := U.ι.opensFunctor.op.obj V) s) =
        (schemeKaehlerDerivation (U.ι ≫ f)).d s := by
  rw [← schemeKaehlerRestrictIso_inv_derivation f U V s]
  have h := congrArg (fun g => g.val.app V
    ((schemeKaehlerDerivation (U.ι ≫ f)).d s))
      (schemeKaehlerRestrictIso f U).inv_hom_id
  exact h

end EvenQuinticConic
