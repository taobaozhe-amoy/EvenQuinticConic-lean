import EvenQuinticConic.LocalFrames
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Local unit-sheaf isomorphisms and coherent frames

A trivialization here is an actual isomorphism of sheaves of modules on the
site of opens contained in an open set. Evaluating it constructs coherent
linear coordinates, including on the empty open.
-/

open CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  {M : SheafOfModules.{u} R} {U : Opens X}

/-- Coordinates obtained by evaluating a genuine local sheaf isomorphism. -/
noncomputable def moduleSheafFrameOfLocalIso
    (e : M.over U ≅ SheafOfModules.unit (R.over U)) : ModuleSheafFrame M U where
  coordinate V hV :=
    ((SheafOfModules.evaluation (R.over U) (op (Over.mk (homOfLE hV)))).mapIso e).toLinearEquiv
  coordinate_restrict V W hV hW hWV s := by
    let f : Over.mk (homOfLE hW) ⟶ Over.mk (homOfLE hV) :=
      Over.homMk (homOfLE hWV) (Subsingleton.elim _ _)
    exact PresheafOfModules.naturality_apply e.hom.val f.op s

@[simp]
theorem moduleSheafFrameOfLocalIso_coordinate
    (e : M.over U ≅ SheafOfModules.unit (R.over U))
    (V : Opens X) (hV : V ≤ U) (s : M.val.obj (op V)) :
    (moduleSheafFrameOfLocalIso e).coordinate V hV s =
      e.hom.val.app (op (Over.mk (homOfLE hV))) s := rfl

/-- Coherent coordinates define a morphism to the unit sheaf on the local site. -/
noncomputable def ModuleSheafFrame.localUnitHom (frame : ModuleSheafFrame M U) :
    M.over U ⟶ SheafOfModules.unit (R.over U) where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        (frame.coordinate V.unop.left V.unop.hom.le).toLinearMap
      naturality := by
        intro V W f
        ext s
        exact frame.coordinate_restrict V.unop.left W.unop.left
          V.unop.hom.le W.unop.hom.le f.unop.left.le s }

/-- A coherent frame yields an actual local unit-sheaf isomorphism. -/
noncomputable def ModuleSheafFrame.localUnitIso (frame : ModuleSheafFrame M U) :
    M.over U ≅ SheafOfModules.unit (R.over U) :=
  moduleSheafIsoOfBijective frame.localUnitHom
    (fun V ↦ (frame.coordinate V.unop.left V.unop.hom.le).bijective)

@[simp]
theorem ModuleSheafFrame.localUnitIso_hom_apply (frame : ModuleSheafFrame M U)
    (V : Opens X) (hV : V ≤ U) (s : M.val.obj (op V)) :
    frame.localUnitIso.hom.val.app (op (Over.mk (homOfLE hV))) s =
      frame.coordinate V hV s := rfl

/-- The local-frame interface is equivalent to an actual local isomorphism
with the structure module, with neither extra global assumption nor omission
of restriction compatibility. -/
theorem nonempty_moduleSheafFrame_iff_localUnitIso :
    Nonempty (ModuleSheafFrame M U) ↔
      Nonempty (M.over U ≅ SheafOfModules.unit (R.over U)) := by
  constructor
  · rintro ⟨frame⟩
    exact ⟨frame.localUnitIso⟩
  · rintro ⟨e⟩
    exact ⟨moduleSheafFrameOfLocalIso e⟩

end EvenQuinticConic
