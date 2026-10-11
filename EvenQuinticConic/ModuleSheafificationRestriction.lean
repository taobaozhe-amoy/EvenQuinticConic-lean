import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Sheafification and restriction of module presheaves

Precomposition along a continuous and cocontinuous functor commutes with
module sheafification. The comparison is characterized by the genuine
sheafification units, including after restriction of scalars.
-/

noncomputable section

open CategoryTheory

namespace EvenQuinticConic

attribute [local instance] Types.instFunLike Types.instConcreteCategory

universe v v₁ v₂ u₁ u₂ u

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous.{u} F J K] [Functor.IsContinuous.{v} F J K]
  [F.IsCocontinuous J K]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (P : PresheafOfModules.{v} R.val)

/-- The canonical comparison from sheafifying the restricted module presheaf
into the restriction of its associated sheaf. -/
def moduleSheafificationPushforwardComparison :
    (PresheafOfModules.sheafification (𝟙 S.val)).obj
        ((PresheafOfModules.pushforward φ.val).obj P) ⟶
      (SheafOfModules.pushforward φ).obj
        ((PresheafOfModules.sheafification (𝟙 R.val)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 S.val)).symm
    ((PresheafOfModules.pushforward φ.val).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.val)).unit.app P))

omit [F.IsCocontinuous J K] [J.HasSheafCompose (forget AddCommGrpCat.{v})] in
/-- The canonical comparison intertwines the actual sheafification units. -/
theorem moduleSheafificationPushforwardComparison_unit :
    (PresheafOfModules.sheafificationAdjunction (𝟙 S.val)).unit.app
        ((PresheafOfModules.pushforward φ.val).obj P) ≫
      (moduleSheafificationPushforwardComparison φ P).val =
    (PresheafOfModules.pushforward φ.val).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.val)).unit.app P) := by
  change (PresheafOfModules.sheafificationAdjunction (𝟙 S.val)).homEquiv _ _
    (moduleSheafificationPushforwardComparison φ P) = _
  exact (PresheafOfModules.sheafificationHomEquiv (𝟙 S.val)).apply_symm_apply _

/-- Restriction along a cocontinuous functor preserves the local bijectivity
of the sheafification unit, so the canonical comparison is an isomorphism. -/
theorem moduleSheafificationPushforwardComparison_isIso :
    IsIso (moduleSheafificationPushforwardComparison φ P) := by
  let Q := (PresheafOfModules.pushforward φ.val).obj P
  let c := moduleSheafificationPushforwardComparison φ P
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 S.val)).unit.app Q
  let η' := (PresheafOfModules.toPresheaf S.val).map η
  let c' := (PresheafOfModules.toPresheaf S.val).map c.val
  have hcomp : η' ≫ c' = Functor.whiskerLeft F.op
      (CategoryTheory.toSheafify K P.presheaf) := by
    change (PresheafOfModules.toPresheaf S.val).map η ≫
      (PresheafOfModules.toPresheaf S.val).map c.val = _
    rw [← Functor.map_comp]
    rw [moduleSheafificationPushforwardComparison_unit]
    rfl
  haveI : Presheaf.IsLocallyInjective J η' := by
    change Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J Q.presheaf)
    infer_instance
  haveI : Presheaf.IsLocallySurjective J η' := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J Q.presheaf)
    infer_instance
  haveI : Presheaf.IsLocallyInjective J (η' ≫ c') := by
    rw [hcomp]
    exact Presheaf.isLocallyInjective_whisker J K F _
  haveI : Presheaf.IsLocallySurjective J (η' ≫ c') := by
    rw [hcomp]
    exact Presheaf.isLocallySurjective_whisker J K F _
  haveI : Presheaf.IsLocallyInjective J c' :=
    (Presheaf.comp_isLocallyInjective_iff J η' c').mp inferInstance
  haveI : Presheaf.IsLocallySurjective J c' :=
    (Presheaf.comp_isLocallySurjective_iff J η' c').mp inferInstance
  haveI : IsIso ((SheafOfModules.toSheaf _).map c) := by
    apply (Sheaf.isLocallyBijective_iff_isIso
      ((SheafOfModules.toSheaf _).map c)).mp
    constructor
    · change Presheaf.IsLocallyInjective J c'
      infer_instance
    · change Presheaf.IsLocallySurjective J c'
      infer_instance
  exact isIso_of_reflects_iso c (SheafOfModules.toSheaf _)

/-- Module sheafification commutes with restriction and scalar restriction. -/
def moduleSheafificationPushforwardIso :
    (PresheafOfModules.sheafification (𝟙 S.val)).obj
        ((PresheafOfModules.pushforward φ.val).obj P) ≅
      (SheafOfModules.pushforward φ).obj
        ((PresheafOfModules.sheafification (𝟙 R.val)).obj P) := by
  letI := moduleSheafificationPushforwardComparison_isIso φ P
  exact asIso (moduleSheafificationPushforwardComparison φ P)

/-- The isomorphism uses the canonical comparison, preserving its unit formula. -/
@[simp]
theorem moduleSheafificationPushforwardIso_hom :
    (moduleSheafificationPushforwardIso φ P).hom =
      moduleSheafificationPushforwardComparison φ P := rfl

end EvenQuinticConic
