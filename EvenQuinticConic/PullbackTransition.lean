import EvenQuinticConic.LineBundleGluing

/-!
# Pullback of unit transition functions along actual scheme morphisms

All coefficient maps in this file are the actual maps on regular functions
induced by a scheme morphism. The inverse-image cover and compatibility with
restriction are derived from that morphism.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Pullback of a unit regular function using the scheme morphism's actual
map on regular functions. -/
def pullbackUnit (U : X.Opens) : Γ(X, U)ˣ →* Γ(Y, f ⁻¹ᵁ U)ˣ :=
  Units.map (f.app U).hom.toMonoidHom

@[simp]
theorem pullbackUnit_val (U : X.Opens) (s : Γ(X, U)ˣ) :
    ((pullbackUnit f U s : Γ(Y, f ⁻¹ᵁ U)ˣ) : Γ(Y, f ⁻¹ᵁ U)) = f.app U s := rfl

/-- Pullback followed by restriction to a smaller source open. -/
def pullbackUnitLE (U : X.Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, V)ˣ :=
  Units.map (f.appLE U V hV).hom.toMonoidHom

@[simp]
theorem pullbackUnitLE_val (U : X.Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U)
    (s : Γ(X, U)ˣ) :
    ((pullbackUnitLE f U V hV s : Γ(Y, V)ˣ) : Γ(Y, V)) = f.appLE U V hV s := rfl

/-- Pullback of units commutes with the actual restriction maps. -/
theorem pullbackUnit_restrict {U V : X.Opens} (hVU : V ≤ U) (s : Γ(X, U)ˣ) :
    pullbackUnit f V (Units.map
      (X.presheaf.map (homOfLE hVU).op).hom.toMonoidHom s) =
    Units.map (Y.presheaf.map
      (homOfLE (f.preimage_le_preimage_of_le hVU)).op).hom.toMonoidHom
        (pullbackUnit f U s) := by
  apply Units.ext
  exact congrArg (fun φ : Γ(X, U) ⟶ Γ(Y, f ⁻¹ᵁ V) => φ (s : Γ(X, U)))
    (f.naturality (homOfLE hVU).op)

/-- The inverse images of an actual open cover again form an open cover. -/
theorem pullback_cover {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    (⨆ i, f ⁻¹ᵁ U i) = ⊤ :=
  f.preimage_iSup_eq_top hU

/-- The source restriction of a pulled-back unit is the smaller `appLE`
pullback, with no separately supplied naturality condition. -/
theorem pullbackUnitLE_restrict {U : X.Opens} {V W : Y.Opens}
    (hV : V ≤ f ⁻¹ᵁ U) (hWV : W ≤ V) (s : Γ(X, U)ˣ) :
    Units.map (Y.presheaf.map (homOfLE hWV).op).hom.toMonoidHom
      (pullbackUnitLE f U V hV s) =
    pullbackUnitLE f U W (hWV.trans hV) s := by
  apply Units.ext
  exact congrArg (fun φ : Γ(X, U) ⟶ Γ(Y, W) => φ (s : Γ(X, U)))
    (f.appLE_map hV (homOfLE hWV).op)

/-- A restriction in the target followed by pullback agrees with direct
pullback from the larger target open. -/
theorem restrict_pullbackUnitLE {U V : X.Opens} {W : Y.Opens}
    (hVU : V ≤ U) (hW : W ≤ f ⁻¹ᵁ V) (s : Γ(X, U)ˣ) :
    pullbackUnitLE f V W hW
      (Units.map (X.presheaf.map (homOfLE hVU).op).hom.toMonoidHom s) =
    pullbackUnitLE f U W (hW.trans (f.preimage_le_preimage_of_le hVU)) s := by
  apply Units.ext
  exact congrArg (fun φ : Γ(X, U) ⟶ Γ(Y, W) => φ (s : Γ(X, U)))
    (f.map_appLE hW (homOfLE hVU).op)

/-- Pullback preserves a multiplicative relation of unit sections on any
common target open, in particular every transition cocycle relation. -/
theorem pullbackUnit_relation
    {U V W Z : X.Opens} (hZU : Z ≤ U) (hZV : Z ≤ V) (hZW : Z ≤ W)
    (a : Γ(X, U)ˣ) (b : Γ(X, V)ˣ) (c : Γ(X, W)ˣ)
    (h : Units.map (X.presheaf.map (homOfLE hZU).op).hom.toMonoidHom a *
      Units.map (X.presheaf.map (homOfLE hZV).op).hom.toMonoidHom b =
      Units.map (X.presheaf.map (homOfLE hZW).op).hom.toMonoidHom c) :
    Units.map (Y.presheaf.map (homOfLE
        (f.preimage_le_preimage_of_le hZU)).op).hom.toMonoidHom
        (pullbackUnit f U a) *
      Units.map (Y.presheaf.map (homOfLE
        (f.preimage_le_preimage_of_le hZV)).op).hom.toMonoidHom
        (pullbackUnit f V b) =
      Units.map (Y.presheaf.map (homOfLE
        (f.preimage_le_preimage_of_le hZW)).op).hom.toMonoidHom
        (pullbackUnit f W c) := by
  rw [← pullbackUnit_restrict f hZU a, ← pullbackUnit_restrict f hZV b,
    ← pullbackUnit_restrict f hZW c, ← map_mul, h]

section Cocycle

variable {ι : Type u} {U : ι → X.Opens}

/-- The transition unit pulled back from the actual target overlap, then
restricted to an arbitrary open in its inverse image. -/
def pullbackTransitionUnit (g : UnitTransition X U) (i j : ι)
    (W : Y.Opens) (hi : W ≤ f ⁻¹ᵁ U i) (hj : W ≤ f ⁻¹ᵁ U j) : Γ(Y, W)ˣ :=
  pullbackUnitLE f (U i ⊓ U j) W (fun _ h => ⟨hi h, hj h⟩)
    (g.transition i j (U i ⊓ U j) inf_le_left inf_le_right)

/-- The pulled-back coefficient may be computed on any smaller target
common open whose inverse image contains the source open. This follows
from the original transition naturality and the actual morphism naturality. -/
theorem pullbackTransitionUnit_eq (g : UnitTransition X U) (i j : ι)
    (W : Y.Opens) (hi : W ≤ f ⁻¹ᵁ U i) (hj : W ≤ f ⁻¹ᵁ U j)
    (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j)
    (hW : W ≤ f ⁻¹ᵁ V) :
    pullbackTransitionUnit f g i j W hi hj =
      pullbackUnitLE f V W hW (g.transition i j V hVi hVj) := by
  let hV : V ≤ U i ⊓ U j := le_inf hVi hVj
  have hg := g.restrict i j (U i ⊓ U j) V inf_le_left inf_le_right hV
  rw [← hg]
  exact (restrict_pullbackUnitLE f hV hW
    (g.transition i j (U i ⊓ U j) inf_le_left inf_le_right)).symm

/-- The actual transition cocycle is transported along an actual scheme
morphism. Its restriction, identity and cocycle laws are proved from those
of the original system, using the actual pullbacks of regular functions. -/
def UnitTransition.pullback (g : UnitTransition X U) :
    UnitTransition Y (fun i => f ⁻¹ᵁ U i) where
  transition := pullbackTransitionUnit f g
  restrict i j W V hi hj hVW := by
    exact pullbackUnitLE_restrict f (U := U i ⊓ U j) (fun _ h => ⟨hi h, hj h⟩) hVW
      (g.transition i j (U i ⊓ U j) inf_le_left inf_le_right)
  self i W hi := by
    dsimp only [pullbackTransitionUnit]
    rw [g.self, map_one]
  cocycle i j k W hi hj hk := by
    let V := (U i ⊓ U j) ⊓ U k
    have hVi : V ≤ U i := inf_le_left.trans inf_le_left
    have hVj : V ≤ U j := inf_le_left.trans inf_le_right
    have hVk : V ≤ U k := inf_le_right
    have hW : W ≤ f ⁻¹ᵁ V := fun _ h => ⟨⟨hi h, hj h⟩, hk h⟩
    rw [pullbackTransitionUnit_eq f g i j W hi hj V hVi hVj hW,
      pullbackTransitionUnit_eq f g j k W hj hk V hVj hVk hW,
      pullbackTransitionUnit_eq f g i k W hi hk V hVi hVk hW,
      ← map_mul, g.cocycle]

/-- In any inverse image of a target common open, the constructed pullback
cocycle is exactly the map of the original transition unit. -/
theorem UnitTransition.pullback_transition (g : UnitTransition X U)
    (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    (g.pullback f).transition i j (f ⁻¹ᵁ V)
      (f.preimage_le_preimage_of_le hi) (f.preimage_le_preimage_of_le hj) =
    pullbackUnit f V (g.transition i j V hi hj) := by
  dsimp only [UnitTransition.pullback]
  rw [pullbackTransitionUnit_eq f g i j _ _ _ V hi hj le_rfl]
  simp only [pullbackUnitLE, Scheme.Hom.appLE_eq_app, pullbackUnit]

/-- Compatible regular-function coordinates pull back to compatible
coordinates for the constructed inverse-image cocycle. This produces the
coordinate data used to build actual pulled-back global sections. -/
theorem pullback_compatible_coordinates (g : UnitTransition X U)
    (s : ∀ i, Γ(X, U i))
    (hs : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      X.presheaf.map (homOfLE hi).op (s i) =
        (g.transition i j V hi hj : Γ(X, V)) *
          X.presheaf.map (homOfLE hj).op (s j))
    (i j : ι) (W : Y.Opens) (hi : W ≤ f ⁻¹ᵁ U i) (hj : W ≤ f ⁻¹ᵁ U j) :
    Y.presheaf.map (homOfLE hi).op (f.app (U i) (s i)) =
      ((g.pullback f).transition i j W hi hj : Γ(Y, W)) *
        Y.presheaf.map (homOfLE hj).op (f.app (U j) (s j)) := by
  let V := U i ⊓ U j
  have hW : W ≤ f ⁻¹ᵁ V := fun _ h => ⟨hi h, hj h⟩
  have heq := congrArg (fun z : Γ(X, V) => f.appLE V W hW z)
    (hs i j V inf_le_left inf_le_right)
  change (f.appLE V W hW).hom
      (X.presheaf.map (homOfLE (show V ≤ U i from inf_le_left)).op (s i)) =
    (f.appLE V W hW).hom
      ((g.transition i j V inf_le_left inf_le_right : Γ(X, V)) *
        X.presheaf.map (homOfLE (show V ≤ U j from inf_le_right)).op (s j)) at heq
  rw [map_mul] at heq
  have hleft : f.appLE V W hW
      (X.presheaf.map (homOfLE (show V ≤ U i from inf_le_left)).op (s i)) =
      Y.presheaf.map (homOfLE hi).op (f.app (U i) (s i)) := by
    exact congrArg (fun φ : Γ(X, U i) ⟶ Γ(Y, W) => φ (s i))
      (f.map_appLE hW (homOfLE (show V ≤ U i from inf_le_left)).op)
  have hright : f.appLE V W hW
      (X.presheaf.map (homOfLE (show V ≤ U j from inf_le_right)).op (s j)) =
      Y.presheaf.map (homOfLE hj).op (f.app (U j) (s j)) := by
    exact congrArg (fun φ : Γ(X, U j) ⟶ Γ(Y, W) => φ (s j))
      (f.map_appLE hW (homOfLE (show V ≤ U j from inf_le_right)).op)
  rw [hleft, hright] at heq
  exact heq

end Cocycle

end EvenQuinticConic
