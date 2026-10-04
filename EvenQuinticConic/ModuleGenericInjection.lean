import EvenQuinticConic.LocalFrames
import EvenQuinticConic.GenericPointInjection
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Generic coefficients of sections of actual locally framed module sheaves

A coherent local frame on any nonempty open of an integral scheme gives a
coefficient in the scheme's actual function field for every global section.
If the module sheaf has coherent rank-one frames on an open cover, this
coefficient determines the global section uniquely.  No injectivity of a
section-to-generic-fiber map is assumed: it follows from integrality,
compatibility of the frames with restriction, and the actual sheaf condition.

The statements concern an actual `Scheme.Modules` object. They do not construct
a theta characteristic or its local frames for a particular plane curve.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X : Scheme.{u}} [IsIntegral X] (M : X.Modules)

/-- The rational coefficient of a global section in a chosen coherent local
frame. The target is the actual generic stalk of the integral scheme. -/
noncomputable def moduleGenericCoefficient
    (V : X.Opens) [Nonempty V] (frame : ModuleSheafFrame M V)
    (s : M.sections) : X.functionField :=
  X.germToFunctionField V (frame.coordinate V le_rfl (s.eval (op V)))

/-- Equality of generic coefficients in one nonempty framed open gives equality
of the restrictions of the sections to that open. -/
theorem module_eq_on_frame_of_generic_eq
    (V : X.Opens) [Nonempty V] (frame : ModuleSheafFrame M V)
    (s t : M.sections)
    (h : moduleGenericCoefficient M V frame s =
      moduleGenericCoefficient M V frame t) :
    s.eval (op V) = t.eval (op V) := by
  apply (frame.coordinate V le_rfl).injective
  exact X.germToFunctionField_injective V h

/-- On an integral scheme, equality on one nonempty open propagates to a
second nonempty framed open. The overlap contains the actual generic point. -/
theorem module_eq_on_frame_of_eq_on_nonempty
    (U V : X.Opens) [Nonempty U] [Nonempty V]
    (frame : ModuleSheafFrame M U) (s t : M.sections)
    (h : s.eval (op V) = t.eval (op V)) :
    s.eval (op U) = t.eval (op U) := by
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      simpa using (inferInstance : Nonempty U))
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by
      simpa using (inferInstance : Nonempty V))
  letI : Nonempty (U ⊓ V : X.Opens) := ⟨⟨genericPoint X, hηU, hηV⟩⟩
  have hW : s.eval (op (U ⊓ V)) = t.eval (op (U ⊓ V)) := by
    have hs : M.val.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op (s.eval (op V)) =
        s.eval (op (U ⊓ V)) :=
      PresheafOfModules.sections_property s (homOfLE inf_le_right : U ⊓ V ⟶ V).op
    have ht : M.val.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op (t.eval (op V)) =
        t.eval (op (U ⊓ V)) :=
      PresheafOfModules.sections_property t (homOfLE inf_le_right : U ⊓ V ⟶ V).op
    rw [← hs, ← ht, h]
  apply (frame.coordinate U le_rfl).injective
  apply map_injective_of_isIntegral X (homOfLE inf_le_left : U ⊓ V ⟶ U)
  change X.ringCatSheaf.val.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op
      (frame.coordinate U le_rfl (s.eval (op U))) =
    X.ringCatSheaf.val.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op
      (frame.coordinate U le_rfl (t.eval (op U)))
  rw [← frame.coordinate_section_restrict s (U ⊓ V) inf_le_left,
    ← frame.coordinate_section_restrict t (U ⊓ V) inf_le_left, hW]

omit [IsIntegral X] in
/-- Compatible global section families agreeing on an actual open cover agree
everywhere, by uniqueness in the actual sheaf condition. -/
theorem module_sections_eq_of_cover
    {ι : Type*} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (s t : M.sections) (h : ∀ i, s.eval (op (U i)) = t.eval (op (U i))) :
    s = t := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.val.presheaf, M.isSheaf⟩
  have htop : s.eval (op ⊤) = t.eval (op ⊤) := by
    apply F.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) (by rw [hcover])
    intro i
    change M.val.map (homOfLE (show U i ≤ ⊤ from le_top)).op (s.eval (op ⊤)) =
      M.val.map (homOfLE (show U i ≤ ⊤ from le_top)).op (t.eval (op ⊤))
    simpa only [PresheafOfModules.sections_property] using h i
  apply PresheafOfModules.sections_ext
  intro W
  have hs := PresheafOfModules.sections_property s
    (homOfLE (show W.unop ≤ ⊤ from le_top)).op
  have ht := PresheafOfModules.sections_property t
    (homOfLE (show W.unop ≤ ⊤ from le_top)).op
  exact hs.symm.trans ((congrArg (M.val.map
    (homOfLE (show W.unop ≤ ⊤ from le_top)).op) htop).trans ht)

/-- A global section of an actual module sheaf with a cover by coherent
rank-one frames is determined by its coefficient at the generic point in any
chosen nonempty framed open. -/
theorem moduleGenericCoefficient_injective
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (frames : ∀ i, ModuleSheafFrame M (U i))
    (V : X.Opens) [Nonempty V] (frame : ModuleSheafFrame M V) :
    Function.Injective (moduleGenericCoefficient M V frame) := by
  intro s t h
  have hV := module_eq_on_frame_of_generic_eq M V frame s t h
  apply module_sections_eq_of_cover M U hcover s t
  intro i
  exact module_eq_on_frame_of_eq_on_nonempty M (U i) V (frames i) s t hV

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

/-- The generic coefficient as a linear map on the actual module of global
sections. Scalars act through the canonical map from global functions to the
actual function field. -/
noncomputable def moduleGlobalGenericLinearMap
    (V : X.Opens) [Nonempty V] (frame : ModuleSheafFrame M V) :
    M.val.obj (op ⊤) →ₗ[Γ(X, ⊤)] X.functionField where
  toFun s := moduleGenericCoefficient M V frame (moduleGlobalSectionFamily M s)
  map_add' s t := by
    dsimp [moduleGenericCoefficient, moduleGlobalSectionFamily]
    rw [map_add, map_add, map_add]
  map_smul' r s := by
    dsimp [moduleGenericCoefficient, moduleGlobalSectionFamily]
    have hmap : M.val.map (homOfLE (show V ≤ ⊤ from le_top)).op (r • s) =
        X.ringCatSheaf.val.map (homOfLE (show V ≤ ⊤ from le_top)).op r •
          M.val.map (homOfLE (show V ≤ ⊤ from le_top)).op s :=
      M.val.map_smul _ r s
    have hmap' := congrArg (fun a ↦ X.germToFunctionField V
      (frame.coordinate V le_rfl a)) hmap
    apply hmap'.trans
    have hframe := (frame.coordinate V le_rfl).map_smul
      (X.ringCatSheaf.val.map (homOfLE (show V ≤ ⊤ from le_top)).op r)
      (M.val.map (homOfLE (show V ≤ ⊤ from le_top)).op s)
    apply (congrArg (X.germToFunctionField V) hframe).trans
    change X.germToFunctionField V
        (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op r *
          (show Γ(X, V) from frame.coordinate V le_rfl
            (M.val.map (homOfLE (show V ≤ ⊤ from le_top)).op s))) =
      X.germToFunctionField ⊤ r * _
    rw [map_mul, generic_germ_restrict]
    rfl

/-- The linear map on genuine global sections is injective when coherent
rank-one frames cover the integral scheme. -/
theorem moduleGlobalGenericLinearMap_injective
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (frames : ∀ i, ModuleSheafFrame M (U i))
    (V : X.Opens) [Nonempty V] (frame : ModuleSheafFrame M V) :
    Function.Injective (moduleGlobalGenericLinearMap M V frame) := by
  intro s t h
  have hfamily : moduleGlobalSectionFamily M s = moduleGlobalSectionFamily M t :=
    moduleGenericCoefficient_injective M U hcover frames V frame h
  have heval := congrArg (fun q : M.sections ↦ q.eval (op ⊤)) hfamily
  simpa [moduleGlobalSectionFamily_eval] using heval

/-- With scalar actions compatible with the scheme's global functions,
linear independence of actual global sections is preserved by taking generic
coefficients. In particular the independence is over the given base field,
not over the function field. -/
theorem module_generic_coefficients_linearIndependent
    (K : Type*) [Field K] [Algebra K Γ(X, ⊤)] [Algebra K X.functionField]
    [Module K (M.val.obj (op ⊤))]
    [IsScalarTower K Γ(X, ⊤) (M.val.obj (op ⊤))]
    [IsScalarTower K Γ(X, ⊤) X.functionField]
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (frames : ∀ i, ModuleSheafFrame M (U i))
    (V : X.Opens) [Nonempty V] (frame : ModuleSheafFrame M V)
    {κ : Type*} (s : κ → M.val.obj (op ⊤)) (hs : LinearIndependent K s) :
    LinearIndependent K ((moduleGlobalGenericLinearMap M V frame) ∘ s) := by
  let f : M.val.obj (op ⊤) →ₗ[K] X.functionField :=
    (moduleGlobalGenericLinearMap M V frame).restrictScalars K
  exact hs.map_injOn f
    (moduleGlobalGenericLinearMap_injective M U hcover frames V frame).injOn

end EvenQuinticConic
