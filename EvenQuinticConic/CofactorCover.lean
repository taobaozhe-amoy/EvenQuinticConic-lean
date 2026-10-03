import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Cofactor roots and the kernel of a matrix

This file proves the pointwise linear algebra behind a cofactor presentation
of a discriminant cover.  It makes no assertions about existence, descent,
étaleness, or line bundles on a discriminant curve.

All statements concern actual matrices over a field.  In particular, the
kernel conclusion is proved from the equations
`v i * v j = twist * adjugate M i j`
and the determinant equation; it is not introduced as an axiom.

The twist is explicit in every matrix theorem. The default `-1` in the
definition preserves the earlier three-by-three presentation; it must not be
silently used in the five-by-five setting. The proposed discriminant conventions
use `-1` for rank-two degenerations of three-by-three forms and `1` for rank-four
degenerations of five-by-five forms. Identifying either convention with the
geometric discriminant cover is not proved in this file.
-/

namespace EvenQuinticConic

open Matrix

variable {K : Type*} [Field K]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {twist : K}

/-- The quadratic equations used in a cofactor presentation, at one field-valued point. -/
def IsCofactorRoot (M : Matrix n n K) (v : n → K) (twist : K := -1) : Prop :=
  ∀ i j, v i * v j = twist * M.adjugate i j

/-- Multiplying the cofactor equations by a row of `M` proves the kernel equation.
The nonzero-coordinate hypothesis is essential for cancellation. -/
theorem cofactorRoot_mulVec_eq_zero
    (M : Matrix n n K) (v : n → K)
    (hdet : M.det = 0) (hroot : IsCofactorRoot M v twist)
    (hnonzero : ∃ k, v k ≠ 0) : M.mulVec v = 0 := by
  obtain ⟨k, hk⟩ := hnonzero
  funext i
  have hzero : (M.mulVec v) i * v k = 0 := by
    change (∑ j, M i j * v j) * v k = 0
    rw [Finset.sum_mul]
    have hterm : ∀ j, M i j * v j * v k = twist * (M i j * M.adjugate j k) := by
      intro j
      rw [mul_assoc, hroot j k]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    change twist * ((M * M.adjugate) i k) = 0
    rw [Matrix.mul_adjugate, hdet]
    simp
  exact (mul_eq_zero.mp hzero).resolve_right hk

/-- Nonzero cofactor roots of one matrix agree up to one global sign.
This is an algebraic statement about vectors, not a claim that a geometric
cover is étale or connected. -/
theorem cofactorRoots_eq_or_eq_neg
    (M : Matrix n n K) (v w : n → K)
    (hv : IsCofactorRoot M v twist) (hw : IsCofactorRoot M w twist)
    (hnonzero : ∃ k, v k ≠ 0) : w = v ∨ w = -v := by
  obtain ⟨k, hk⟩ := hnonzero
  have hprod : ∀ i j, w i * w j = v i * v j := by
    intro i j
    exact (hw i j).trans (hv i j).symm
  have hfactor : (w k - v k) * (w k + v k) = 0 := by
    calc
      (w k - v k) * (w k + v k) = w k * w k - v k * v k := by ring
      _ = 0 := sub_eq_zero.mpr (hprod k k)
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    have hsign : w k = v k := sub_eq_zero.mp h
    funext i
    apply mul_right_cancel₀ hk
    simpa only [hsign] using hprod i k
  · right
    have hsign : w k = -v k := eq_neg_of_add_eq_zero_left h
    funext i
    apply mul_right_cancel₀ (neg_ne_zero.mpr hk)
    change w i * (-v k) = (-v i) * (-v k)
    calc
      w i * (-v k) = v i * v k := by simpa only [hsign] using hprod i k
      _ = (-v i) * (-v k) := by ring

/-- Negation preserves the cofactor equations. -/
theorem IsCofactorRoot.neg {M : Matrix n n K} {v : n → K}
    (h : IsCofactorRoot M v twist) : IsCofactorRoot M (-v) twist := by
  intro i j
  simpa using h i j

/-- On a rank-one cofactor chart, a square root of the twisted pivot
constructs a root vector by division. The rank-one chart condition is stated
explicitly as vanishing pivot minors; it is not inferred here from a geometric
corank hypothesis. -/
theorem cofactorRoot_of_pivot_minors
    (M : Matrix n n K) (k : n) (r : K)
    (hr : r ≠ 0) (hsquare : r * r = twist * M.adjugate k k)
    (hminor : ∀ i j,
      M.adjugate i j * M.adjugate k k = M.adjugate i k * M.adjugate j k) :
    IsCofactorRoot M (fun i => twist * M.adjugate i k / r) twist := by
  intro i j
  apply mul_right_cancel₀ (mul_ne_zero hr hr)
  calc
    (twist * M.adjugate i k / r * (twist * M.adjugate j k / r)) * (r * r) =
        twist * twist * (M.adjugate i k * M.adjugate j k) := by
          field_simp [hr]
    _ = twist * twist * (M.adjugate i j * M.adjugate k k) := by rw [hminor]
    _ = (twist * M.adjugate i j) * (r * r) := by rw [hsquare]; ring

/-- Existence of a field-valued cofactor root on a nonzero pivot chart is
equivalent to one scalar being a square, assuming the displayed pivot-minor
identities. This does not assert that the square root exists over the field. -/
theorem exists_cofactorRoot_iff_pivot_square
    (M : Matrix n n K) (k : n) (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0)
    (hminor : ∀ i j,
      M.adjugate i j * M.adjugate k k = M.adjugate i k * M.adjugate j k) :
    (∃ v : n → K, IsCofactorRoot M v twist) ↔
      ∃ r : K, r * r = twist * M.adjugate k k := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v k, hv k k⟩
  · rintro ⟨r, hsquare⟩
    have hr : r ≠ 0 := by
      intro hz
      apply mul_ne_zero htwist hpivot
      simpa [hz] using hsquare.symm
    exact ⟨_, cofactorRoot_of_pivot_minors M k r hr hsquare hminor⟩

/-- A cofactor root has a nonzero pivot coordinate whenever the corresponding
diagonal cofactor and the twist are nonzero. -/
theorem cofactorRoot_pivot_ne_zero
    (M : Matrix n n K) (v : n → K) (k : n)
    (hv : IsCofactorRoot M v twist)
    (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0) : v k ≠ 0 := by
  intro hz
  apply mul_ne_zero htwist hpivot
  simpa [hz] using (hv k k).symm

section CharacteristicNotTwo

variable [NeZero (2 : K)]

omit [Fintype n] [DecidableEq n] in
/-- A nonzero vector differs from its negative when the characteristic is not two. -/
theorem cofactorVector_ne_neg (v : n → K) (hnonzero : ∃ k, v k ≠ 0) : v ≠ -v := by
  obtain ⟨k, hk⟩ := hnonzero
  intro h
  have hsign : v k = -v k := congrFun h k
  have hsum : v k + v k = 0 := eq_neg_iff_add_eq_zero.mp hsign
  have hmul : (2 : K) * v k = 0 := by simpa only [two_mul] using hsum
  exact hk ((mul_eq_zero.mp hmul).resolve_left (NeZero.ne (2 : K)))

/-- A cofactor-root fiber with a nonzero field-valued point has exactly the
two roots `v` and `-v`, presented as an equivalence with `Bool`.

This is a statement about a set of field-valued solutions. It neither
constructs an étale morphism nor proves that a family of fibers is flat. -/
noncomputable def cofactorRootFiberEquivBool
    (M : Matrix n n K) (v : n → K)
    (hv : IsCofactorRoot M v twist) (hnonzero : ∃ k, v k ≠ 0) :
    {w : n → K // IsCofactorRoot M w twist} ≃ Bool := by
  classical
  have hne : v ≠ -v := cofactorVector_ne_neg v hnonzero
  refine
    { toFun := fun w => if w.val = v then true else false
      invFun := fun b => if b then ⟨v, hv⟩ else ⟨-v, hv.neg⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    rcases cofactorRoots_eq_or_eq_neg M v w.val hv w.property hnonzero with h | h
    · apply Subtype.ext
      simp [h]
    · apply Subtype.ext
      simp [h, Ne.symm hne]
  · intro b
    cases b <;> simp [Ne.symm hne]

/-- The actual cardinality of the set of cofactor roots, under the stated
nonzero-root and characteristic hypotheses, is two. -/
theorem cofactorRootFiber_card_eq_two
    (M : Matrix n n K) (v : n → K)
    (hv : IsCofactorRoot M v twist) (hnonzero : ∃ k, v k ≠ 0) :
    Nat.card {w : n → K // IsCofactorRoot M w twist} = 2 := by
  calc
    Nat.card {w : n → K // IsCofactorRoot M w twist} = Nat.card Bool :=
      Nat.card_congr (cofactorRootFiberEquivBool M v hv hnonzero)
    _ = 2 := by simp

/-- Combining the explicit construction with the root count gives a
two-element field-valued fiber from the nonzero-pivot minor equations and a
square-root witness alone. -/
theorem cofactorRootFiber_card_eq_two_of_pivot_square
    (M : Matrix n n K) (k : n) (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0)
    (hminor : ∀ i j,
      M.adjugate i j * M.adjugate k k = M.adjugate i k * M.adjugate j k)
    (hsquare : ∃ r : K, r * r = twist * M.adjugate k k) :
    Nat.card {w : n → K // IsCofactorRoot M w twist} = 2 := by
  obtain ⟨v, hv⟩ :=
    (exists_cofactorRoot_iff_pivot_square M k htwist hpivot hminor).mpr hsquare
  exact cofactorRootFiber_card_eq_two M v hv
    ⟨k, cofactorRoot_pivot_ne_zero M v k hv htwist hpivot⟩

end CharacteristicNotTwo

end EvenQuinticConic
