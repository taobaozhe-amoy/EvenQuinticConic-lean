import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import EvenQuinticConic.SheafGluing

/-!
# Trivializations of actual sheaves of modules

This file constructs isomorphisms in mathlib's `SheafOfModules` category.
The input section is an actual compatible family, and its associated morphism
sends a function `r` to `r • s`.  Local geometric existence of such a section
is deliberately not asserted here.
-/

open CategoryTheory Opposite

universe u v w

namespace EvenQuinticConic

section Modules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}}
  {M N : SheafOfModules.{w} R}

/-- A morphism of actual sheaves of modules whose maps on sections are
bijective gives an actual isomorphism of sheaves of modules. -/
noncomputable def moduleSheafIsoOfBijective (f : M ⟶ N)
    (hf : ∀ U, Function.Bijective (f.val.app U)) : M ≅ N where
  hom := f
  inv := ⟨(PresheafOfModules.isoMk
    (fun U ↦ (LinearEquiv.ofBijective (f.val.app U).hom (hf U)).toModuleIso)
    (fun {X Y} g ↦ f.val.naturality g)).inv⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.isoMk
      (fun U ↦ (LinearEquiv.ofBijective (f.val.app U).hom (hf U)).toModuleIso)
      (fun {X Y} g ↦ f.val.naturality g)).hom_inv_id
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.isoMk
      (fun U ↦ (LinearEquiv.ofBijective (f.val.app U).hom (hf U)).toModuleIso)
      (fun {X Y} g ↦ f.val.naturality g)).inv_hom_id

@[simp]
theorem moduleSheafIsoOfBijective_hom (f : M ⟶ N)
    (hf : ∀ U, Function.Bijective (f.val.app U)) :
    (moduleSheafIsoOfBijective f hf).hom = f := rfl

variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- The genuine sheaf morphism from the structure module determined by a
compatible section of `M`. -/
noncomputable def sectionToModuleHom (s : M.sections) : SheafOfModules.unit R ⟶ M :=
  M.unitHomEquiv.symm s

@[simp]
theorem sectionToModuleHom_apply (s : M.sections) (U : Cᵒᵖ) (r : R.val.obj U) :
    (sectionToModuleHom s).val.app U r = r • s.eval U := rfl

/-- A section which generates freely on every object trivializes the actual
module sheaf, without postulating an isomorphism. -/
noncomputable def moduleSheafTrivialization (s : M.sections)
    (hs : ∀ U, Function.Bijective (fun r : R.val.obj U ↦ r • s.eval U)) :
    SheafOfModules.unit R ≅ M :=
  moduleSheafIsoOfBijective (sectionToModuleHom s) hs

@[simp]
theorem moduleSheafTrivialization_hom_apply (s : M.sections)
    (hs : ∀ U, Function.Bijective (fun r : R.val.obj U ↦ r • s.eval U))
    (U : Cᵒᵖ) (r : R.val.obj U) :
    (moduleSheafTrivialization s hs).hom.val.app U r = r • s.eval U := rfl

end Modules

section LocalFrame

variable {A : Type u} [Ring A] {V : Type v} [AddCommGroup V] [Module A V]

/-- In a genuine rank-one module, a vector with unit coefficient in a frame
is a free generator.  This holds over arbitrary rings. -/
theorem smul_vector_bijective_of_unit_coordinate (frame : V ≃ₗ[A] A)
    (s : V) (hs : IsUnit (frame s)) :
    Function.Bijective (fun r : A ↦ r • s) := by
  have hmul : Function.Bijective (fun r : A ↦ r * frame s) :=
    (IsUnit.isUnit_iff_mulRight_bijective).mp hs
  have heq : (fun r : A ↦ frame (r • s)) = (fun r : A ↦ r * frame s) := by
    funext r
    simp
  have hcomp : Function.Bijective (frame ∘ (fun r : A ↦ r • s)) := by
    change Function.Bijective (fun r : A ↦ frame (r • s))
    rw [heq]
    exact hmul
  constructor
  · intro a b h
    exact hcomp.1 (congrArg frame h)
  · intro y
    obtain ⟨r, hr⟩ := hcomp.2 (frame y)
    exact ⟨r, frame.injective hr⟩

end LocalFrame

section GlobalSection

open TopologicalSpace

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (M : SheafOfModules.{u} R)

/-- A section over the whole space supplies the compatible family used by
`unitHomEquiv`.  This is constructed by actual restriction maps. -/
noncomputable def moduleGlobalSectionFamily (s : M.val.obj (op ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun V ↦ M.val.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op s)
    (by
      intro U V f
      change M.val.presheaf.map f (M.val.presheaf.map
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op s) =
        M.val.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op s
      rw [← ConcreteCategory.comp_apply, ← M.val.presheaf.map_comp]
      rfl)

@[simp]
theorem moduleGlobalSectionFamily_eval (s : M.val.obj (op ⊤)) (V : Opens X) :
    (moduleGlobalSectionFamily M s).eval (op V) =
      M.val.map (homOfLE (show V ≤ ⊤ from le_top)).op s := rfl

end GlobalSection

section LocalTrivialization

open TopologicalSpace

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (M : SheafOfModules.{u} R) {ι : Type*}

/-- A global section that has a unit coordinate in local rank-one frames
trivializes the actual sheaf of modules.  The local frames may be given on
all subopens of the cover; the sheaf axioms supply the global inverse. -/
noncomputable def moduleSheafTrivializationOfLocalUnit
    (s : M.sections) (U : ι → Opens X) (hcover : iSup U = ⊤)
    (frame : ∀ i V, V ≤ U i →
      M.val.obj (op V) ≃ₗ[R.val.obj (op V)] R.val.obj (op V))
    (hs : ∀ i V (h : V ≤ U i), IsUnit (frame i V h (s.eval (op V)))) :
    SheafOfModules.unit R ≅ M := by
  let f := sectionToModuleHom s
  apply moduleSheafIsoOfBijective f
  intro V
  exact sheaf_app_bijective_of_cover
    ((SheafOfModules.toSheaf R).obj (SheafOfModules.unit R))
    ((SheafOfModules.toSheaf R).obj M)
    ((SheafOfModules.toSheaf R).map f).val U hcover
    (fun i W h ↦ smul_vector_bijective_of_unit_coordinate
      (frame i W h) (s.eval (op W)) (hs i W h)) V.unop

@[simp]
theorem moduleSheafTrivializationOfLocalUnit_hom_apply
    (s : M.sections) (U : ι → Opens X) (hcover : iSup U = ⊤)
    (frame : ∀ i V, V ≤ U i →
      M.val.obj (op V) ≃ₗ[R.val.obj (op V)] R.val.obj (op V))
    (hs : ∀ i V (h : V ≤ U i), IsUnit (frame i V h (s.eval (op V))))
    (V : Opens X) (r : R.val.obj (op V)) :
    (moduleSheafTrivializationOfLocalUnit M s U hcover frame hs).hom.val.app (op V) r =
      r • s.eval (op V) := rfl

end LocalTrivialization

end EvenQuinticConic
