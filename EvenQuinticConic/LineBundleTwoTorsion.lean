import EvenQuinticConic.LineBundleUnitProduct
import EvenQuinticConic.LineBundleRefinement

/-! # Squaring a twist by an actual two-torsion line sheaf -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace EvenQuinticConic.UnitTransition
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}

theorem mul_square_reorder (g h : UnitTransition X U) :
    (g.mul h).mul (g.mul h) = (g.mul g).mul (h.mul h) := by
  apply ext
  intro i j V hi hj
  change (g.transition i j V hi hj * h.transition i j V hi hj) *
    (g.transition i j V hi hj * h.transition i j V hi hj) =
    (g.transition i j V hi hj * g.transition i j V hi hj) *
      (h.transition i j V hi hj * h.transition i j V hi hj)
  ac_rfl

def twoTorsionTwistSquareIso (g h : UnitTransition X U) (hcover : iSup U = ⊤)
    (e : (g.mul g).moduleSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    ((g.mul h).mul (g.mul h)).moduleSheaf ≅ (h.mul h).moduleSheaf :=
  eqToIso (congrArg UnitTransition.moduleSheaf (mul_square_reorder g h)) ≪≫
    (g.mul g).productIsoOfTrivialLeft (h.mul h) hcover e

def refineSquareTrivialization {κ : Type u} (g : UnitTransition X U)
    (V : κ → X.Opens) (r : κ → ι) (hsub : ∀ a, V a ≤ U (r a))
    (hV : iSup V = ⊤)
    (e : (g.mul g).moduleSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    ((g.refine V r hsub).mul (g.refine V r hsub)).moduleSheaf ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (g.mul g).refineIso V r hsub hV ≪≫ e

end EvenQuinticConic.UnitTransition
