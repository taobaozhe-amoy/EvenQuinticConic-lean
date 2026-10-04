import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Nonempty affine common refinements of actual open covers

For two arbitrary open covers of a scheme, choose an affine neighbourhood
of each point contained in a member of each cover. Nonemptiness, coverage,
affineness and the two containment maps are all proved from the original
covers. In particular, a line sheaf need not be trivial on an entire
standard projective coordinate chart.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u v w

namespace EvenQuinticConic

variable {X : Scheme.{u}} {ι : Type v} {κ : Type w}
  (U : ι → X.Opens) (W : κ → X.Opens)

/-- A point-indexed affine cover subordinate to each of two given covers. -/
structure AffineCommonRefinement where
  openSet : X → X.Opens
  leftIndex : X → ι
  rightIndex : X → κ
  affine : ∀ x, IsAffineOpen (openSet x)
  point_mem : ∀ x, x ∈ openSet x
  le_left : ∀ x, openSet x ≤ U (leftIndex x)
  le_right : ∀ x, openSet x ≤ W (rightIndex x)

namespace AffineCommonRefinement

variable {U W} (r : AffineCommonRefinement U W)

instance nonempty (x : X) : Nonempty (r.openSet x) :=
  ⟨⟨x, r.point_mem x⟩⟩

theorem cover : iSup r.openSet = ⊤ := by
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, r.point_mem x⟩

end AffineCommonRefinement

/-- The affine-basis property constructs all refinement data from the two
cover equalities. No refined cover or subordinate chart choices are inputs. -/
def affineCommonRefinement (hU : iSup U = ⊤) (hW : iSup W = ⊤) :
    AffineCommonRefinement U W := by
  have hlocal (x : X) : ∃ (i : ι) (j : κ) (V : X.Opens),
      IsAffineOpen V ∧ x ∈ V ∧ V ≤ U i ∧ V ≤ W j := by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show x ∈ iSup W by rw [hW]; trivial)
    obtain ⟨V, hV, hx, hsub⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ U i ⊓ W j from ⟨hi, hj⟩)
    exact ⟨i, j, V, hV, hx, fun _ h => (hsub h).1, fun _ h => (hsub h).2⟩
  choose i j V hV hx hleft hright using hlocal
  exact ⟨V, i, j, hV, hx, hleft, hright⟩

end EvenQuinticConic
