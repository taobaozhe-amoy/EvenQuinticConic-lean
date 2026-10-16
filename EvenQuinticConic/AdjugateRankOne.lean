import EvenQuinticConic.CofactorCover
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Rank-one adjugate charts from the determinant equation

The pivot-minor hypotheses in `CofactorCover` are discharged here for an
actual symmetric matrix with zero determinant and a nonzero diagonal cofactor.
No rank-one condition on the adjugate is assumed.  Replacing one row by a
coordinate row gives an invertible matrix, so a kernel vector is determined
by its pivot coordinate.  Applying this to the columns of the adjugate gives
the required minor identities.

The conclusions concern field-valued cofactor equations.  They do not by
themselves identify those equations with a geometric discriminant cover.
-/

namespace EvenQuinticConic

open Matrix

variable {K : Type*} [Field K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonzero adjugate entry makes the corresponding coordinate injective
on the kernel.  This uses the actual determinant of a row-replacement matrix. -/
theorem kernel_vector_eq_of_adjugate_entry
    (M : Matrix n n K) (a b : n) (hpivot : M.adjugate a b ≠ 0)
    (v w : n → K) (hv : M.mulVec v = 0) (hw : M.mulVec w = 0)
    (hcoord : v a = w a) : v = w := by
  let B : Matrix n n K := M.updateRow b (Pi.single a 1)
  have hdetB : B.det ≠ 0 := by
    simpa only [B, ← Matrix.adjugate_apply] using hpivot
  have hinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (B.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdetB))
  apply hinj
  simp only [B, Matrix.updateRow_mulVec, hv, hw, single_dotProduct, one_mul, hcoord]

/-- The diagonal version of coordinate injectivity on the kernel. -/
theorem kernel_vector_eq_of_cofactor_pivot
    (M : Matrix n n K) (k : n) (hpivot : M.adjugate k k ≠ 0)
    (v w : n → K) (hv : M.mulVec v = 0) (hw : M.mulVec w = 0)
    (hcoord : v k = w k) : v = w :=
  kernel_vector_eq_of_adjugate_entry M k k hpivot v w hv hw hcoord

/-- Every adjugate column is in the kernel at a zero of the determinant. -/
theorem adjugate_column_mem_kernel
    (M : Matrix n n K) (hdet : M.det = 0) (j : n) :
    M.mulVec (fun i => M.adjugate i j) = 0 := by
  funext i
  change (M * M.adjugate) i j = 0
  rw [Matrix.mul_adjugate, hdet]
  simp

/-- All minors through a nonzero entry of the adjugate vanish.
The matrix need not be symmetric for this identity. -/
theorem adjugate_minor_of_det_eq_zero
    (M : Matrix n n K) (a b : n) (hdet : M.det = 0)
    (hpivot : M.adjugate a b ≠ 0) (i j : n) :
    M.adjugate i j * M.adjugate a b =
      M.adjugate i b * M.adjugate a j := by
  have heq :
      M.adjugate a b • (fun c => M.adjugate c j) =
        M.adjugate a j • (fun c => M.adjugate c b) := by
    apply kernel_vector_eq_of_adjugate_entry M a b hpivot
    · rw [Matrix.mulVec_smul, adjugate_column_mem_kernel M hdet j, smul_zero]
    · rw [Matrix.mulVec_smul, adjugate_column_mem_kernel M hdet b, smul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun heq i

/-- The diagonal-pivot instance of the adjugate minor identity. -/
theorem adjugate_pivot_minor_of_det_eq_zero
    (M : Matrix n n K) (k : n) (hdet : M.det = 0)
    (hpivot : M.adjugate k k ≠ 0) (i j : n) :
    M.adjugate i j * M.adjugate k k =
      M.adjugate i k * M.adjugate k j :=
  adjugate_minor_of_det_eq_zero M k k hdet hpivot i j

/-- For a symmetric singular matrix, a nonzero adjugate entry forces the
diagonal entry in the same row to be nonzero. -/
theorem adjugate_diagonal_ne_zero_of_entry
    (M : Matrix n n K) (hM : M.IsSymm) (hdet : M.det = 0)
    (a b : n) (hab : M.adjugate a b ≠ 0) : M.adjugate a a ≠ 0 := by
  have hadj : M.adjugate.IsSymm := by
    change M.adjugate.transpose = M.adjugate
    rw [Matrix.adjugate_transpose, hM]
  have hba : M.adjugate b a ≠ 0 := by rwa [hadj.apply a b]
  have hminor := adjugate_minor_of_det_eq_zero M a b hdet hab b a
  intro haa
  exact mul_ne_zero hba hab (by rw [hminor, haa, mul_zero])

/-- The diagonal cofactor charts cover every symmetric determinant-zero
matrix whose adjugate is nonzero. -/
theorem exists_diagonal_adjugate_ne_zero
    (M : Matrix n n K) (hM : M.IsSymm) (hdet : M.det = 0)
    (hadj : M.adjugate ≠ 0) : ∃ k, M.adjugate k k ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hadj
  ext i j
  by_contra hij
  exact adjugate_diagonal_ne_zero_of_entry M hM hdet i j hij (h i)

/-- Symmetry turns the adjugate minor identity into the symmetric chart
identity used in the cofactor-cover equations. -/
theorem symmetric_adjugate_pivot_minors
    (M : Matrix n n K) (hM : M.IsSymm) (k : n)
    (hdet : M.det = 0) (hpivot : M.adjugate k k ≠ 0) :
    ∀ i j, M.adjugate i j * M.adjugate k k =
      M.adjugate i k * M.adjugate j k := by
  have hadj : M.adjugate.IsSymm := by
    change M.adjugate.transpose = M.adjugate
    rw [Matrix.adjugate_transpose, hM]
  intro i j
  rw [hadj.apply k j]
  exact adjugate_pivot_minor_of_det_eq_zero M k hdet hpivot i j

/-- The ratio of two diagonal cofactors is a square on a nonzero pivot
chart.  This is the explicit square-class transition for the scalar equations. -/
theorem adjugate_diagonal_ratio_eq_square
    (M : Matrix n n K) (hM : M.IsSymm) (k j : n)
    (hdet : M.det = 0) (hpivot : M.adjugate k k ≠ 0) :
    M.adjugate j j / M.adjugate k k =
      (M.adjugate j k / M.adjugate k k) * (M.adjugate j k / M.adjugate k k) := by
  have hminor := symmetric_adjugate_pivot_minors M hM k hdet hpivot j j
  calc
    M.adjugate j j / M.adjugate k k =
        (M.adjugate j j * M.adjugate k k) /
          (M.adjugate k k * M.adjugate k k) := by field_simp [hpivot]
    _ = (M.adjugate j k * M.adjugate j k) /
          (M.adjugate k k * M.adjugate k k) := by rw [hminor]
    _ = _ := by rw [div_mul_div_comm]

/-- On the intersection of two diagonal cofactor charts, the scalar
transition factor is nonzero. -/
theorem adjugate_transition_ne_zero
    (M : Matrix n n K) (hM : M.IsSymm) (k j : n)
    (hdet : M.det = 0) (hk : M.adjugate k k ≠ 0) (hj : M.adjugate j j ≠ 0) :
    M.adjugate j k / M.adjugate k k ≠ 0 := by
  apply div_ne_zero _ hk
  intro hzero
  have hminor := symmetric_adjugate_pivot_minors M hM k hdet hk j j
  exact mul_ne_zero hj hk (by simpa [hzero] using hminor)

/-- On an actual symmetric singular-matrix pivot chart, cofactor-root
existence is equivalent to the twisted diagonal cofactor being a square.
No adjugate-minor identity is an input. -/
theorem exists_cofactorRoot_iff_pivot_square_of_symmetric
    (M : Matrix n n K) (hM : M.IsSymm) (k : n) {twist : K}
    (hdet : M.det = 0) (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0) :
    (∃ v : n → K, IsCofactorRoot M v twist) ↔
      ∃ r : K, r * r = twist * M.adjugate k k :=
  exists_cofactorRoot_iff_pivot_square M k htwist hpivot
    (symmetric_adjugate_pivot_minors M hM k hdet hpivot)

/-- Evaluation at the pivot is an equivalence between cofactor-root vectors
and scalar square roots.  Its inverse is the explicit adjugate-column formula.
This is an equivalence of field-valued solutions, not a scheme isomorphism. -/
def cofactorRootFiberEquivScalarRoots_of_symmetric
    (M : Matrix n n K) (hM : M.IsSymm) (k : n) {twist : K}
    (hdet : M.det = 0) (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0) :
    {v : n → K // IsCofactorRoot M v twist} ≃
      {r : K // r * r = twist * M.adjugate k k} := by
  have hnonzero (r : K) (hr : r * r = twist * M.adjugate k k) : r ≠ 0 := by
    intro hz
    exact mul_ne_zero htwist hpivot (by simpa [hz] using hr.symm)
  refine
    { toFun := fun v => ⟨v.val k, v.property k k⟩
      invFun := fun r => ⟨fun i => twist * M.adjugate i k / r.val,
        cofactorRoot_of_pivot_minors M k r.val (hnonzero r.val r.property) r.property
          (symmetric_adjugate_pivot_minors M hM k hdet hpivot)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro v
    apply Subtype.ext
    funext i
    exact (div_eq_iff (hnonzero (v.val k) (v.property k k))).mpr
      (v.property i k).symm
  · intro r
    apply Subtype.ext
    exact (div_eq_iff (hnonzero r.val r.property)).mpr r.property.symm

/-- A square-root witness gives exactly two cofactor roots for an actual
symmetric singular matrix, in characteristic different from two. -/
theorem cofactorRootFiber_card_eq_two_of_symmetric_pivot_square
    [NeZero (2 : K)]
    (M : Matrix n n K) (hM : M.IsSymm) (k : n) {twist : K}
    (hdet : M.det = 0) (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0)
    (hsquare : ∃ r : K, r * r = twist * M.adjugate k k) :
    Nat.card {v : n → K // IsCofactorRoot M v twist} = 2 :=
  cofactorRootFiber_card_eq_two_of_pivot_square M k htwist hpivot
    (symmetric_adjugate_pivot_minors M hM k hdet hpivot) hsquare

end EvenQuinticConic
