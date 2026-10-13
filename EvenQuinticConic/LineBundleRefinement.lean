import EvenQuinticConic.LineBundlePairing
import EvenQuinticConic.FrameTransitionComparison

/-! # Refining the cover of an actual descended line sheaf -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace EvenQuinticConic.UnitTransition
variable {X : Scheme.{u}} {ι κ : Type u} {U : ι → X.Opens}

@[ext] theorem ext {g h : UnitTransition X U}
    (heq : ∀ i j V hi hj, g.transition i j V hi hj = h.transition i j V hi hj) : g = h := by
  cases g
  cases h
  congr
  funext i j V hi hj
  exact heq i j V hi hj

theorem frame_changeCoefficient (g : UnitTransition X U) (i j : ι)
    (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    frameChangeCoefficient (g.frame i) (g.frame j) V hi hj =
      (g.transition i j V hi hj : Γ(X, V)) := by
  have h := g.frame_transition i j V hi hj (((g.frame j).coordinate V hj).symm 1)
  rw [LinearEquiv.apply_symm_apply, mul_one] at h
  exact h

def refine (g : UnitTransition X U) (V : κ → X.Opens) (r : κ → ι)
    (hsub : ∀ a, V a ≤ U (r a)) : UnitTransition X V where
  transition a b W ha hb := g.transition (r a) (r b) W (ha.trans (hsub a)) (hb.trans (hsub b))
  restrict a b W Z _ha _hb hZW := g.restrict (r a) (r b) W Z _ _ hZW
  self a W _ha := g.self (r a) W _
  cocycle a b c W _ha _hb _hc := g.cocycle (r a) (r b) (r c) W _ _ _

theorem refine_mul (g h : UnitTransition X U) (V : κ → X.Opens) (r : κ → ι)
    (hsub : ∀ a, V a ≤ U (r a)) :
    (g.mul h).refine V r hsub = (g.refine V r hsub).mul (h.refine V r hsub) := rfl

def refineIso (g : UnitTransition X U) (V : κ → X.Opens) (r : κ → ι)
    (hsub : ∀ a, V a ≤ U (r a)) (hV : iSup V = ⊤) :
    (g.refine V r hsub).moduleSheaf ≅ g.moduleSheaf :=
  frameTransitionComparisonIso V hV (g.refine V r hsub).frame
    (fun a ↦ (g.frame (r a)).onSubopen (hsub a)) (by
      intro a b W ha hb
      rw [frame_changeCoefficient]
      exact (g.frame_changeCoefficient (r a) (r b) W
        (ha.trans (hsub a)) (hb.trans (hsub b))).symm)

theorem refineIso_coordinate (g : UnitTransition X U) (V : κ → X.Opens) (r : κ → ι)
    (hsub : ∀ a, V a ≤ U (r a)) (hV : iSup V = ⊤)
    (a : κ) (W : X.Opens) (ha : W ≤ V a)
    (s : (g.refine V r hsub).moduleSheaf.val.obj (op W)) :
    (g.frame (r a)).coordinate W (ha.trans (hsub a))
      ((g.refineIso V r hsub hV).hom.val.app (op W) s) =
      ((g.refine V r hsub).frame a).coordinate W ha s :=
  frameTransitionComparisonIso_coordinate V hV (g.refine V r hsub).frame
    (fun a ↦ (g.frame (r a)).onSubopen (hsub a)) _ a W ha s

theorem localTrivializationTransition_frame (g : UnitTransition X U) :
    localTrivializationTransition U (fun i ↦ (g.frame i).localUnitIso) = g := by
  apply ext
  intro i j V hi hj
  apply Units.ext
  have hc (a : ι) (W : X.Opens) (ha : W ≤ U a) :
      (moduleSheafFrameOfLocalIso (g.frame a).localUnitIso).coordinate W ha =
        (g.frame a).coordinate W ha := by
    ext s
    rfl
  change (moduleSheafFrameOfLocalIso (g.frame i).localUnitIso).coordinate V hi
    (((moduleSheafFrameOfLocalIso (g.frame j).localUnitIso).coordinate V hj).symm 1) = _
  rw [hc, hc]
  exact g.frame_changeCoefficient i j V hi hj

end EvenQuinticConic.UnitTransition
