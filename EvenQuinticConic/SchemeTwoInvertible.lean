import EvenQuinticConic.SheafGluing
import Mathlib.Algebra.Group.Invertible.Basic

/-! # Invertibility of two on all section rings from an open cover -/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace EvenQuinticConic

variable {X : Scheme} {ι : Type*}

/-- If two is a unit on the members of an actual open cover, it is a unit
in the ring of sections on every open, including the empty open. -/
theorem schemeTwo_isUnit_of_cover (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h2 : ∀ i, IsUnit (2 : Γ(X, U i))) (V : X.Opens) :
    IsUnit (2 : Γ(X, V)) := by
  apply isUnit_of_unit_restrictions X (fun i => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (by simp [← inf_iSup_eq, hU]) (2 : Γ(X, V))
  intro i
  have hi := (X.presheaf.map
    (homOfLE (show V ⊓ U i ≤ U i from inf_le_right)).op).hom.isUnit_map (h2 i)
  change IsUnit ((X.presheaf.map
    (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op).hom (2 : Γ(X, V)))
  simpa only [map_ofNat] using hi

/-- Chosen inverse-of-two instances on every section ring, derived from
invertibility on the cover rather than assumed separately for all opens. -/
def schemeTwoInvertibleOfCover (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h2 : ∀ i, IsUnit (2 : Γ(X, U i))) (V : X.Opens) :
    Invertible (2 : Γ(X, V)) :=
  (schemeTwo_isUnit_of_cover U hU h2 V).invertible

end EvenQuinticConic
