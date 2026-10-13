import EvenQuinticConic.LineBundleRefinement
import EvenQuinticConic.ModuleFrameRescaling

/-!
# Constructing a square trivialization from local multiplication coefficients

If the local generator on chart j equals gᵢⱼ times the generator on chart i,
its square coefficient satisfies uⱼ = uᵢ gᵢⱼ². Actual regular units satisfying
these identities construct an isomorphism of the descended square with O.
No global square isomorphism is an input.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace EvenQuinticConic
variable {X : Scheme.{u}}

/-- The tautological coherent frame of the actual structure module. -/
def structureModuleFrame (U : X.Opens) :
    ModuleSheafFrame (SheafOfModules.unit X.ringCatSheaf) U where
  coordinate V _ := LinearEquiv.refl (X.ringCatSheaf.val.obj (op V)) (X.ringCatSheaf.val.obj (op V))
  coordinate_restrict _ _ _ _ _ _ := rfl

namespace UnitTransition
variable {ι : Type u} {U : ι → X.Opens} (g : UnitTransition X U)

/-- Actual local square coefficients of the frame generators. -/
def SquareCoefficientsCompatible (u : ∀ i, Γ(X, U i)ˣ) : Prop :=
  ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
    X.presheaf.map (homOfLE hj).op (u j : Γ(X, U j)) =
      X.presheaf.map (homOfLE hi).op (u i : Γ(X, U i)) *
        ((g.transition i j V hi hj : Γ(X, V)) * (g.transition i j V hi hj : Γ(X, V)))

/-- The square cocycle and the coefficient-rescaled structure frames have
identical actual transition functions. -/
theorem square_frame_transition (u : ∀ i, Γ(X, U i)ˣ)
    (hu : g.SquareCoefficientsCompatible u)
    (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    frameChangeCoefficient ((g.mul g).frame i) ((g.mul g).frame j) V hi hj =
      frameChangeCoefficient ((structureModuleFrame (U i)).rescale (u i))
        ((structureModuleFrame (U j)).rescale (u j)) V hi hj := by
  rw [frame_changeCoefficient, frameChangeCoefficient_rescale]
  change (g.transition i j V hi hj : Γ(X, V)) * (g.transition i j V hi hj : Γ(X, V)) =
    X.presheaf.map (homOfLE hi).op (↑(u i)⁻¹ : Γ(X, U i)) * 1 *
      X.presheaf.map (homOfLE hj).op (u j : Γ(X, U j))
  rw [hu i j V hi hj, mul_one, ← mul_assoc, ← map_mul]
  simp

/-- Construct the actual square trivialization by gluing multiplication
coefficients on the given cover. -/
def squareIsoOfLocalUnits (hcover : iSup U = ⊤)
    (u : ∀ i, Γ(X, U i)ˣ) (hu : g.SquareCoefficientsCompatible u) :
    (g.mul g).moduleSheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  frameTransitionComparisonIso U hcover (g.mul g).frame
    (fun i ↦ (structureModuleFrame (U i)).rescale (u i))
    (g.square_frame_transition u hu)

/-- The glued morphism multiplies the square coordinate by precisely the
specified local coefficient. -/
theorem squareIsoOfLocalUnits_apply (hcover : iSup U = ⊤)
    (u : ∀ i, Γ(X, U i)ˣ) (hu : g.SquareCoefficientsCompatible u)
    (i : ι) (V : X.Opens) (hi : V ≤ U i)
    (s : (g.mul g).moduleSheaf.val.obj (op V)) :
    (g.squareIsoOfLocalUnits hcover u hu).hom.val.app (op V) s =
      X.presheaf.map (homOfLE hi).op (u i : Γ(X, U i)) *
        (show Γ(X, V) from ((g.mul g).frame i).coordinate V hi s) := by
  have h := frameTransitionComparisonIso_coordinate U hcover (g.mul g).frame
    (fun i ↦ (structureModuleFrame (U i)).rescale (u i))
    (g.square_frame_transition u hu) i V hi s
  change X.presheaf.map (homOfLE hi).op (↑(u i)⁻¹ : Γ(X, U i)) *
      (show Γ(X, V) from (g.squareIsoOfLocalUnits hcover u hu).hom.val.app (op V) s) =
    (show Γ(X, V) from ((g.mul g).frame i).coordinate V hi s) at h
  rw [← h, ← mul_assoc, ← map_mul]
  simp

end UnitTransition
end EvenQuinticConic
