import EvenQuinticConic.NetBasePoint

/-!
# Moving a common point to a coordinate point in an actual matrix net

An invertible matrix with prescribed first column is constructed by replacing
one column of the identity and then swapping columns. Congruence by this
matrix preserves the actual determinant Jacobian condition: the determinant
polynomial, and every partial derivative, are multiplied by the nonzero
constant square of the coordinate matrix determinant. Consequently an
arbitrary nonzero common isotropic vector can be moved to the first coordinate
vector without assuming any coordinate-choice or determinant identity.
-/

noncomputable section
namespace EvenQuinticConic
open Matrix MvPolynomial

variable {K : Type*} [Field K]

/-- An explicit column replacement and permutation complete a nonzero vector
to an invertible coordinate matrix. -/
theorem exists_invertible_matrix_first_column {m : ℕ}
    (P : Fin (m + 1) → K) (hP : P ≠ 0) :
    ∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) K,
      B.det ≠ 0 ∧ ∀ j, B j 0 = P j := by
  have hcoord : ∃ k, P k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (funext h)
  obtain ⟨k, hk⟩ := hcoord
  let A : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).updateCol k P
  have hdetA : A.det = P k := by
    change ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).updateCol k P).det = P k
    rw [← Matrix.cramer_apply, Matrix.cramer_one]
    rfl
  let B := A.submatrix (Equiv.refl _) (Equiv.swap 0 k)
  have hA : IsUnit A := A.isUnit_iff_isUnit_det.mpr
    (isUnit_iff_ne_zero.mpr (hdetA ▸ hk))
  have hB : IsUnit B :=
    (Matrix.isUnit_submatrix_equiv (Equiv.refl _) (Equiv.swap 0 k)).mpr hA
  refine ⟨B, isUnit_iff_ne_zero.mp (B.isUnit_iff_isUnit_det.mp hB), ?_⟩
  intro j
  simp [B, A, Matrix.submatrix_apply]

variable {n σ : Type*} [Fintype n] [DecidableEq n] [Fintype σ] [DecidableEq σ]

/-- Congruence changes the vector coordinates in every member of the net. -/
def matrixNetCongruence (M : σ → Matrix n n K) (B : Matrix n n K) :
    σ → Matrix n n K := fun i => B.transpose * M i * B

omit [DecidableEq n] [Fintype σ] [DecidableEq σ] in
/-- Symmetry is preserved by the actual congruence formula. -/
theorem matrixNetCongruence_isSymm (M : σ → Matrix n n K)
    (hM : ∀ i, (M i).IsSymm) (B : Matrix n n K) (i : σ) :
    (matrixNetCongruence M B i).IsSymm := by
  change (B.transpose * M i * B).transpose = B.transpose * M i * B
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hM i]
  exact (Matrix.mul_assoc _ _ _).symm

omit [Fintype n] [DecidableEq n] [DecidableEq σ] in
/-- The polynomial matrix is a literal linear combination of constant matrices. -/
theorem linearMatrixNet_eq_sum_smul (M : σ → Matrix n n K) :
    linearMatrixNet M = ∑ i, (X i : MvPolynomial σ K) • (M i).map C := by
  ext r c
  simp [linearMatrixNet, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

omit [DecidableEq n] [DecidableEq σ] in
/-- Congruence commutes with constructing the actual polynomial matrix. -/
theorem linearMatrixNet_congruence (M : σ → Matrix n n K) (B : Matrix n n K) :
    linearMatrixNet (matrixNetCongruence M B) =
      (B.map (C : K →+* MvPolynomial σ K)).transpose * linearMatrixNet M * B.map C := by
  rw [linearMatrixNet_eq_sum_smul, linearMatrixNet_eq_sum_smul]
  simp only [matrixNetCongruence, Matrix.map_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rfl

omit [DecidableEq σ] in
/-- The determinant polynomial changes by the constant square `det(B)^2`. -/
theorem linearMatrixNet_congruence_det (M : σ → Matrix n n K) (B : Matrix n n K) :
    (linearMatrixNet (matrixNetCongruence M B)).det =
      C (B.det * B.det) * (linearMatrixNet M).det := by
  have hmap : (B.map (C : K →+* MvPolynomial σ K)).det = C B.det :=
    ((C : K →+* MvPolynomial σ K).map_det B).symm
  rw [linearMatrixNet_congruence, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hmap, map_mul]
  ring

omit [DecidableEq σ] in
/-- The same constant square scales every actual formal partial derivative. -/
theorem linearMatrixNet_congruence_pderiv (M : σ → Matrix n n K)
    (B : Matrix n n K) (i : σ) :
    pderiv i (linearMatrixNet (matrixNetCongruence M B)).det =
      C (B.det * B.det) * pderiv i (linearMatrixNet M).det := by
  rw [linearMatrixNet_congruence_det, pderiv_C_mul]

omit [DecidableEq σ] in
/-- Invertible coordinate changes preserve the explicit actual determinant
Jacobian nonsingularity condition. -/
theorem linearMatrixNet_congruence_jacobian (M : σ → Matrix n n K)
    (B : Matrix n n K) (hB : B.det ≠ 0)
    (hsmooth : ∀ t : σ → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∀ t : σ → K, t ≠ 0 → eval t (linearMatrixNet (matrixNetCongruence M B)).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet (matrixNetCongruence M B)).det) ≠ 0 := by
  intro t ht hzero
  have hscale : B.det * B.det ≠ 0 := mul_ne_zero hB hB
  rw [linearMatrixNet_congruence_det, map_mul, eval_C] at hzero
  have hzeroM := (mul_eq_zero.mp hzero).resolve_left hscale
  obtain ⟨i, hi⟩ := hsmooth t ht hzeroM
  refine ⟨i, ?_⟩
  rw [linearMatrixNet_congruence_pderiv, map_mul, eval_C]
  exact mul_ne_zero hscale hi

omit [Fintype σ] [DecidableEq σ] in
/-- The `(0,0)` entry after congruence is the original quadratic form at
the prescribed first column. -/
theorem matrixNetCongruence_zero_zero {m : ℕ}
    (M : σ → Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (P : Fin (m + 1) → K) (hcol : ∀ j, B j 0 = P j) (i : σ) :
    matrixNetCongruence M B i 0 0 = dotProduct P ((M i).mulVec P) := by
  simp only [matrixNetCongruence, Matrix.mul_apply, Matrix.transpose_apply,
    hcol, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro c hc
  ring

/-- An arbitrary nonzero common point admits an actual invertible coordinate
change taking it to the first coordinate point. Symmetry, the determinant
Jacobian condition, and independence of the remaining polar coefficients
are all conclusions for the transformed net. -/
theorem exists_normalized_matrixNet_common_point {m : ℕ}
    (M : σ → Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : ∀ i, (M i).IsSymm) (P : Fin (m + 1) → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : σ → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) K,
      B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      (∀ i, (matrixNetCongruence M B i).IsSymm) ∧
      (∀ i, matrixNetCongruence M B i 0 0 = 0) ∧
      (∀ t : σ → K, t ≠ 0 → eval t (linearMatrixNet (matrixNetCongruence M B)).det = 0 →
        ∃ i, eval t (pderiv i (linearMatrixNet (matrixNetCongruence M B)).det) ≠ 0) ∧
      LinearIndependent K (fun i (j : Fin m) => matrixNetCongruence M B i j.succ 0) := by
  obtain ⟨B, hB, hcol⟩ := exists_invertible_matrix_first_column P hP
  have hsym := matrixNetCongruence_isSymm M hM B
  have hbase : ∀ i, matrixNetCongruence M B i 0 0 = 0 := by
    intro i
    rw [matrixNetCongruence_zero_zero M B P hcol i, hisotropic i]
  have hgrad := linearMatrixNet_congruence_jacobian M B hB hsmooth
  exact ⟨B, hB, hcol, hsym, hbase, hgrad,
    linearMatrixNet_polar_tails_linearIndependent (matrixNetCongruence M B) hsym hbase hgrad⟩

end EvenQuinticConic
