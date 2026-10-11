/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Cocontinuity of direct image on opens

An open map induces a cocontinuous functor between the sites of open sets.
Unlike continuity of this functor, cocontinuity does not require injectivity.
-/

open CategoryTheory TopologicalSpace Topology

namespace EvenQuinticConic

/-- The direct-image functor on opens associated to an open map is cocontinuous. -/
theorem openImageFunctor_isCocontinuous
    {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) :
    hf.functor.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := by
  constructor
  intro U S hS x hx
  obtain ⟨V, i, hi, hfx⟩ := hS (f x) ⟨x, hx, rfl⟩
  let W : Opens X := U ⊓ (Opens.map f).obj V
  let j : W ⟶ U := homOfLE inf_le_left
  let k : hf.functor.obj W ⟶ V := homOfLE (by
    rintro y ⟨z, hz, rfl⟩
    exact hz.2)
  refine ⟨W, j, ?_, ⟨hx, hfx⟩⟩
  change S (hf.functor.map j)
  have heq : hf.functor.map j = k ≫ i := Subsingleton.elim _ _
  rw [heq]
  exact S.downward_closed hi k

end EvenQuinticConic
