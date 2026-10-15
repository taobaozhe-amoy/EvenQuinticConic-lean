import EvenQuinticConic.AffinePushforwardModule
import EvenQuinticConic.KummerModuleAtlas

/-!
# Algebra charts on the actual pushforward over an arbitrary scheme

The coordinates in this file are ring isomorphisms from the actual source
section rings. Their compatibility with the scheme's coefficient map makes
them linear for the genuine pushforward module action. Overlap algebra maps
are constructed, rather than supplied. No existence of these charts for an
arbitrary finite étale morphism is asserted here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace EvenQuinticConic
variable {X Y : Scheme.{u}}

/-- The actual direct image of the source structure module. -/
abbrev schemePushforwardStructureModule (f : X ⟶ Y) : Y.Modules :=
  (schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf)

/-- Multiplicative local coordinates, with their actual scalar and restriction
laws, on the structure sheaf of the preimage of every chart subopen. -/
structure PushforwardKummerChart (f : X ⟶ Y) (U : Y.Opens) (u : Γ(Y, U)ˣ) where
  coordinate : ∀ V (hV : V ≤ U), Γ(X, f ⁻¹ᵁ V) ≃+*
    KummerAlgebra (Y.presheaf.map (homOfLE hV).op (u : Γ(Y, U)))
  coefficient : ∀ V (hV : V ≤ U) (r : Γ(Y, V)),
    coordinate V hV (f.app V r) = algebraMap _ _ r
  re_restrict : ∀ V W (hV : V ≤ U) (hW : W ≤ U) (hWV : W ≤ V)
    (s : Γ(X, f ⁻¹ᵁ V)),
    (coordinate W hW (X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op s)).re =
      Y.presheaf.map (homOfLE hWV).op (coordinate V hV s).re
  im_restrict : ∀ V W (hV : V ≤ U) (hW : W ≤ U) (hWV : W ≤ V)
    (s : Γ(X, f ⁻¹ᵁ V)),
    (coordinate W hW (X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op s)).im =
      Y.presheaf.map (homOfLE hWV).op (coordinate V hV s).im

namespace PushforwardKummerChart
variable {f : X ⟶ Y} {U : Y.Opens} {u : Γ(Y, U)ˣ}
    (c : PushforwardKummerChart f U u)

/-- Ring coordinates preserve the actual scalar action of the pushforward. -/
def linearCoordinate (V : Y.Opens) (hV : V ≤ U) :
    (schemePushforwardStructureModule f).val.obj (op V) ≃ₗ[Γ(Y, V)]
      KummerAlgebra (Y.presheaf.map (homOfLE hV).op (u : Γ(Y, U))) where
  __ := (c.coordinate V hV).toAddEquiv
  map_smul' r s := by
    change c.coordinate V hV (f.app V r * (show Γ(X, f ⁻¹ᵁ V) from s)) =
      r • c.coordinate V hV s
    rw [map_mul, c.coefficient, Algebra.smul_def]

/-- A multiplicative chart supplies coherent coordinates on the actual module. -/
def moduleChart : KummerModuleChart (schemePushforwardStructureModule f) U u where
  coordinate := c.linearCoordinate
  re_restrict := c.re_restrict
  im_restrict := c.im_restrict

/-- Comparing through the same genuine section ring constructs the overlap map. -/
def overlap {W : Y.Opens} {w : Γ(Y, W)ˣ}
    (d : PushforwardKummerChart f W w) (V : Y.Opens) (hi : V ≤ U) (hj : V ≤ W) :
    KummerAlgebra (Y.presheaf.map (homOfLE hj).op (w : Γ(Y, W))) ≃ₐ[Γ(Y, V)]
      KummerAlgebra (Y.presheaf.map (homOfLE hi).op (u : Γ(Y, U))) where
  __ := (d.coordinate V hj).symm.trans (c.coordinate V hi)
  commutes' r := by
    change c.coordinate V hi ((d.coordinate V hj).symm (algebraMap _ _ r)) = _
    have h : (d.coordinate V hj).symm (algebraMap _ _ r) = f.app V r := by
      apply (d.coordinate V hj).injective
      rw [RingEquiv.apply_symm_apply, d.coefficient]
    rw [h, c.coefficient]

/-- The constructed overlap compares the original coordinates exactly. -/
theorem overlap_coordinate {W : Y.Opens} {w : Γ(Y, W)ˣ}
    (d : PushforwardKummerChart f W w) (V : Y.Opens) (hi : V ≤ U) (hj : V ≤ W)
    (s : Γ(X, f ⁻¹ᵁ V)) :
    c.overlap d V hi hj (d.coordinate V hj s) = c.coordinate V hi s :=
  congrArg (c.coordinate V hi) ((d.coordinate V hj).symm_apply_apply s)

/-- The local algebra trace is independent of which multiplicative chart is used. -/
theorem trace_coordinate_eq {W : Y.Opens} {w : Γ(Y, W)ˣ}
    (d : PushforwardKummerChart f W w) (V : Y.Opens) (hi : V ≤ U) (hj : V ≤ W)
    (s : Γ(X, f ⁻¹ᵁ V)) :
    Algebra.trace Γ(Y, V) _ (c.coordinate V hi s) =
      Algebra.trace Γ(Y, V) _ (d.coordinate V hj s) := by
  rw [← c.overlap_coordinate d V hi hj s]
  exact kummer_trace_map (c.overlap d V hi hj) _

end PushforwardKummerChart

/-- Multiplicative charts of one actual morphism automatically form a module
atlas; cross-chart compatibility is a conclusion, not an additional premise. -/
def pushforwardKummerAtlas {f : X ⟶ Y} {ι : Type u} (U : ι → Y.Opens)
    (u : ∀ i, Γ(Y, U i)ˣ) (c : ∀ i, PushforwardKummerChart f (U i) (u i)) :
    KummerModuleAtlas (schemePushforwardStructureModule f) U where
  parameter := u
  chart i := (c i).moduleChart
  overlap i j V hi hj := (c i).overlap (c j) V hi hj
  overlap_coordinate i j V hi hj s := (c i).overlap_coordinate (c j) V hi hj s

end EvenQuinticConic
