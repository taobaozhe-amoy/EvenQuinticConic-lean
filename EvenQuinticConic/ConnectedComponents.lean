import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The topological final step

This module counts the actual quotient `ConnectedComponents X` of a topological
space. It assumes connectedness explicitly; it does NOT prove that real
rationality implies connectedness of a smooth projective real variety.
-/

namespace EvenQuinticConic

variable (X : Type*) [TopologicalSpace X]

/-- A nonempty connected space has exactly one connected component. -/
theorem connectedComponents_card_eq_one [ConnectedSpace X] :
    Nat.card (ConnectedComponents X) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro a b
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    apply ConnectedComponents.coe_eq_coe.mpr
    simp
  · obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact ⟨ConnectedComponents.mk x⟩

/-- In particular, a connected space cannot have exactly two components. -/
theorem connectedComponents_card_ne_two [ConnectedSpace X] :
    Nat.card (ConnectedComponents X) ≠ 2 := by
  rw [connectedComponents_card_eq_one X]
  decide

end EvenQuinticConic
