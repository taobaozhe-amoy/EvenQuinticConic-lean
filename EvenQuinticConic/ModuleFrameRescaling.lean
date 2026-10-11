import EvenQuinticConic.FrameCocycleDescent

/-!
# Rescaling actual coherent module-sheaf frames by regular units

A unit on the framing open rescales the genuine generator on every subopen.
Coordinates are multiplied by the inverse restricted unit, and transition
units change by the corresponding coboundary. All operations use the actual
structure-sheaf restriction maps, including on empty subopens.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace EvenQuinticConic

universe u

variable {X : Scheme.{u}} {M : X.Modules}

local instance moduleFrameRescalingSectionCommRing (V : X.Opens) : CommRing (X.ringCatSheaf.val.obj (op V)) :=
  inferInstanceAs (CommRing Γ(X, V))

/-- Rescale a genuine local generator by a regular unit. Its coordinate
maps multiply the original coordinates by the restricted inverse unit. -/
def ModuleSheafFrame.rescale {U : X.Opens}
    (e : ModuleSheafFrame M U) (w : Γ(X, U)ˣ) : ModuleSheafFrame M U where
  coordinate V hV := (e.coordinate V hV).trans
    (LinearEquiv.smulOfUnit (R := X.ringCatSheaf.val.obj (op V))
      (M := X.ringCatSheaf.val.obj (op V))
      (Units.map (X.ringCatSheaf.val.map (homOfLE hV).op).hom.toMonoidHom
        (show (X.ringCatSheaf.val.obj (op U))ˣ from w⁻¹)))
  coordinate_restrict V W hV hW hWV s := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfUnit,
      DistribMulAction.toLinearEquiv_apply, Units.smul_def]
    change X.presheaf.map (homOfLE hW).op (↑w⁻¹ : Γ(X, U)) *
        (show Γ(X, W) from e.coordinate W hW (M.val.map (homOfLE hWV).op s)) =
      X.presheaf.map (homOfLE hWV).op
        (X.presheaf.map (homOfLE hV).op (↑w⁻¹ : Γ(X, U)) *
          (show Γ(X, V) from e.coordinate V hV s))
    rw [e.coordinate_restrict V W hV hW hWV, map_mul]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    rfl

/-- Exact coordinate formula for a unit-rescaled actual frame. -/
theorem ModuleSheafFrame.rescale_coordinate {U : X.Opens}
    (e : ModuleSheafFrame M U) (w : Γ(X, U)ˣ)
    (V : X.Opens) (hV : V ≤ U) (s : M.val.obj (op V)) :
    (e.rescale w).coordinate V hV s =
      X.presheaf.map (homOfLE hV).op (↑w⁻¹ : Γ(X, U)) *
        (show Γ(X, V) from e.coordinate V hV s) := rfl

/-- The actual new generator is the original generator multiplied by the
restriction of the specified regular unit. -/
theorem ModuleSheafFrame.rescale_generator {U : X.Opens}
    (e : ModuleSheafFrame M U) (w : Γ(X, U)ˣ)
    (V : X.Opens) (hV : V ≤ U) :
    ((e.rescale w).coordinate V hV).symm 1 =
      X.presheaf.map (homOfLE hV).op (w : Γ(X, U)) • (e.coordinate V hV).symm 1 := by
  apply ((e.rescale w).coordinate V hV).injective
  rw [LinearEquiv.apply_symm_apply, e.rescale_coordinate, LinearEquiv.map_smul,
    LinearEquiv.apply_symm_apply]
  change (1 : Γ(X, V)) =
    X.presheaf.map (homOfLE hV).op (↑w⁻¹ : Γ(X, U)) *
      (X.presheaf.map (homOfLE hV).op (w : Γ(X, U)) * 1)
  rw [mul_one, ← map_mul]
  simp only [Units.inv_mul, map_one]

/-- Rescaled coordinates commute with genuine restriction maps. -/
theorem ModuleSheafFrame.rescale_coordinate_restrict {U : X.Opens}
    (e : ModuleSheafFrame M U) (w : Γ(X, U)ˣ)
    (V W : X.Opens) (hV : V ≤ U) (hW : W ≤ U) (hWV : W ≤ V)
    (s : M.val.obj (op V)) :
    (e.rescale w).coordinate W hW (moduleRestrict M hWV s) =
      X.presheaf.map (homOfLE hWV).op ((e.rescale w).coordinate V hV s) :=
  (e.rescale w).coordinate_restrict V W hV hW hWV s

/-- The actual rescaled generators themselves form a compatible family. -/
theorem ModuleSheafFrame.rescale_restrict_generator {U : X.Opens}
    (e : ModuleSheafFrame M U) (w : Γ(X, U)ˣ)
    (V W : X.Opens) (hV : V ≤ U) (hW : W ≤ U) (hWV : W ≤ V) :
    moduleRestrict M hWV (((e.rescale w).coordinate V hV).symm 1) =
      ((e.rescale w).coordinate W hW).symm 1 :=
  (e.rescale w).restrict_generator V W hV hW hWV

/-- Changes of coordinates for the rescaled frames are obtained by the
restricted inverse source coefficient and restricted target coefficient. -/
theorem frameChangeCoefficient_rescale {U V : X.Opens}
    (a : ModuleSheafFrame M U) (b : ModuleSheafFrame M V)
    (wa : Γ(X, U)ˣ) (wb : Γ(X, V)ˣ)
    (W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) :
    frameChangeCoefficient (a.rescale wa) (b.rescale wb) W hU hV =
      X.presheaf.map (homOfLE hU).op (↑wa⁻¹ : Γ(X, U)) *
        frameChangeCoefficient a b W hU hV *
          X.presheaf.map (homOfLE hV).op (wb : Γ(X, V)) := by
  unfold frameChangeCoefficient
  rw [b.rescale_generator, a.rescale_coordinate, LinearEquiv.map_smul]
  change _ * (_ * _) = _ * _ * _
  ring

/-- The exact coboundary formula for the genuine transition units of two
unit-rescaled actual frames. -/
theorem frameChangeUnit_rescale {U V : X.Opens}
    (a : ModuleSheafFrame M U) (b : ModuleSheafFrame M V)
    (wa : Γ(X, U)ˣ) (wb : Γ(X, V)ˣ)
    (W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) :
    frameChangeUnit (a.rescale wa) (b.rescale wb) W hU hV =
      (Units.map (X.presheaf.map (homOfLE hU).op).hom wa)⁻¹ *
        frameChangeUnit a b W hU hV *
          Units.map (X.presheaf.map (homOfLE hV).op).hom wb := by
  apply Units.ext
  exact frameChangeCoefficient_rescale a b wa wb W hU hV

end EvenQuinticConic
