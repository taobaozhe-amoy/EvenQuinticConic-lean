import EvenQuinticConic.LocalFrames
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Descent data for rank-one module sheaves

This file records unit-valued changes of coordinates on all subordinate
opens. `LineBundlePresheaf` constructs the compatible regular-function
families, and `LineBundleSheaf` proves that they form an actual sheaf.
No target module sheaf is assumed in this construction.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u
namespace EvenQuinticConic

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)

/-- Unit transition functions, on arbitrary common subopens.  The convention
is `coordinate i = transition i j * coordinate j`. -/
structure UnitTransition where
  transition : ∀ i j (W : X.Opens), W ≤ U i → W ≤ U j → Γ(X, W)ˣ
  restrict : ∀ i j W V (hi : W ≤ U i) (hj : W ≤ U j) (hVW : V ≤ W),
    Units.map (X.presheaf.map (homOfLE hVW).op).hom
      (transition i j W hi hj) =
      transition i j V (hVW.trans hi) (hVW.trans hj)
  self : ∀ i W (hi : W ≤ U i), transition i i W hi hi = 1
  cocycle : ∀ i j k W (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
    transition i j W hi hj * transition j k W hj hk = transition i k W hi hk

namespace UnitTransition

variable {X U} (g : UnitTransition X U)

/-- Restriction of regular functions, with explicit open-inclusion evidence. -/
def res {V W : X.Opens} (h : W ≤ V) : Γ(X, V) →+* Γ(X, W) :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp] theorem res_refl (V : X.Opens) (s : Γ(X,V)) :
    res (X := X) (le_refl V) s = s := by
  simp [res]

@[simp] theorem res_res {V W Z : X.Opens} (hWV : W ≤ V) (hZW : Z ≤ W)
    (s : Γ(X,V)) : res hZW (res hWV s) = res (hZW.trans hWV) s := by
  simp only [res, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

@[simp] theorem res_transition i j V W (hi : V ≤ U i) (hj : V ≤ U j)
    (hWV : W ≤ V) :
    res hWV (g.transition i j V hi hj : Γ(X,V)) =
      (g.transition i j W (hWV.trans hi) (hWV.trans hj) : Γ(X,W)) :=
  congrArg Units.val (g.restrict i j V W hi hj hWV)


end UnitTransition
end EvenQuinticConic
