import EvenQuinticConic.LineBundleSheaf

/-!
# Explicit local coordinates on the descended line bundle

The inverse of evaluation in chart `i` is the family `gⱼᵢ · r`.
Consequently the local frame is constructed from the transition cocycle.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe u
namespace EvenQuinticConic.UnitTransition
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (g : UnitTransition X U)

/-- A scalar on one chart determines its full compatible coordinate family. -/
def sectionOfCoordinate (i : ι) (V : X.Opens) (hVi : V ≤ U i) (r : Γ(X,V)) :
    g.Section V :=
  ⟨fun j W ↦ (g.transition j i W.val W.prop.2 (W.prop.1.trans hVi) : Γ(X,W.val)) *
      res W.prop.1 r, by
    constructor
    · intro j W Z hWV hWj hZW
      change res hZW ((g.transition j i W hWj (hWV.trans hVi) : Γ(X,W)) * res hWV r) = _
      rw [map_mul, res_transition, res_res]
      rfl
    · intro j k W hWV hWj hWk
      change (g.transition j i W hWj (hWV.trans hVi) : Γ(X,W)) * res hWV r =
        (g.transition j k W hWj hWk : Γ(X,W)) *
          ((g.transition k i W hWk (hWV.trans hVi) : Γ(X,W)) * res hWV r)
      rw [← mul_assoc, ← Units.val_mul, g.cocycle]⟩

@[simp] theorem sectionOfCoordinate_eval (i : ι) (V : X.Opens) (hVi : V ≤ U i)
    (r : Γ(X,V)) j W hWV hWj :
    (g.sectionOfCoordinate i V hVi r).eval j W hWV hWj =
      (g.transition j i W hWj (hWV.trans hVi) : Γ(X,W)) * res hWV r := rfl

/-- Evaluation on a chart is a linear equivalence, proved using the cocycle. -/
def coordinateEquiv (i : ι) (V : X.Opens) (hVi : V ≤ U i) :
    g.Section V ≃ₗ[Γ(X,V)] Γ(X,V) where
  toFun s := s.eval i V le_rfl hVi
  invFun := g.sectionOfCoordinate i V hVi
  left_inv s := by
    apply Section.ext
    intro j W hWV hWj
    rw [sectionOfCoordinate_eval, s.naturality]
    exact (s.transition j i W hWV hWj (hWV.trans hVi)).symm
  right_inv r := by simp [g.self]
  map_add' := by intros; rfl
  map_smul' := by intros; simp

@[simp] theorem coordinateEquiv_apply (i : ι) (V : X.Opens) (hVi : V ≤ U i)
    (s : g.Section V) : g.coordinateEquiv i V hVi s = s.eval i V le_rfl hVi := rfl

theorem coordinateEquiv_restrict (i : ι) (V W : X.Opens) (hVi : V ≤ U i)
    (hWi : W ≤ U i) (hWV : W ≤ V) (s : g.Section V) :
    g.coordinateEquiv i W hWi (s.restrict hWV) =
      res hWV (g.coordinateEquiv i V hVi s) :=
  (s.naturality i V W le_rfl hVi hWV).symm

/-- The actual descended module sheaf has the prescribed coherent local frames. -/
def frame (i : ι) : ModuleSheafFrame g.moduleSheaf (U i) where
  coordinate V hVi := by
    change g.Section V ≃ₗ[Γ(X,V)] Γ(X,V)
    exact g.coordinateEquiv i V hVi
  coordinate_restrict V W hVi hWi hWV s :=
    g.coordinateEquiv_restrict i V W hVi hWi hWV s

@[simp] theorem frame_coordinate (i : ι) (V : X.Opens) (hVi : V ≤ U i)
    (s : g.moduleSheaf.val.obj (op V)) :
    (g.frame i).coordinate V hVi s =
      (show Γ(X,V) from Section.eval s i V le_rfl hVi) := rfl

/-- Change of coordinates for the constructed frames is exactly the input cocycle. -/
theorem frame_transition (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
    (s : g.moduleSheaf.val.obj (op V)) :
    (show Γ(X,V) from (g.frame i).coordinate V hi s) =
      (g.transition i j V hi hj : Γ(X,V)) *
        (show Γ(X,V) from (g.frame j).coordinate V hj s) :=
  Section.transition s i j V le_rfl hi hj

end EvenQuinticConic.UnitTransition
