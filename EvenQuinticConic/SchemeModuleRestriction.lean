import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Module sheaves on actual open subschemes

Restriction uses the open-image functor and the actual restricted structure
sheaf. Its target is `U.toScheme.Modules`; no identification with the slice
site used by `SheafOfModules.over` is assumed.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X : Scheme.{u}}

/-- Restriction of an actual structure-module presheaf to an open subscheme. -/
noncomputable def schemeModulePresheafRestrict (U : X.Opens) :
    X.PresheafOfModules ⥤ U.toScheme.PresheafOfModules :=
  PresheafOfModules.pushforward (F := U.ι.opensFunctor)
    (𝟙 U.toScheme.ringCatSheaf.val)

/-- Restriction of an actual module sheaf to the actual open subscheme. -/
noncomputable def schemeModuleRestrict (U : X.Opens) :
    X.Modules ⥤ U.toScheme.Modules :=
  letI := U.ι.isOpenEmbedding.functor_isContinuous
  SheafOfModules.pushforward (F := U.ι.opensFunctor)
    (𝟙 U.toScheme.ringCatSheaf)

@[simp]
theorem schemeModuleRestrict_obj_val (U : X.Opens) (M : X.Modules) :
    ((schemeModuleRestrict U).obj M).val =
      (schemeModulePresheafRestrict U).obj M.val := rfl

@[simp]
theorem schemeModulePresheafRestrict_obj_obj (U : X.Opens)
    (P : X.PresheafOfModules) (V : U.toScheme.Opensᵒᵖ) :
    ((schemeModulePresheafRestrict U).obj P).obj V =
      P.obj (U.ι.opensFunctor.op.obj V) := rfl

@[simp]
theorem schemeModuleRestrict_map_val (U : X.Opens)
    {M N : X.Modules} (g : M ⟶ N) :
    ((schemeModuleRestrict U).map g).val =
      (schemeModulePresheafRestrict U).map g.val := rfl

end EvenQuinticConic
