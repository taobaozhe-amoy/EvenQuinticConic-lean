import EvenQuinticConic.DeterminantGradient
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Polar independence at a common point of a symmetric matrix net

For a linear family of symmetric matrices, a common nonzero isotropic vector
cannot lie in the kernel of a nonzero member if the actual determinant
polynomial has a nonzero gradient at every nonzero zero. The proof derives
both the rank-one adjugate formula and Jacobi's formula; neither is assumed.
The smoothness input is explicitly a field-valued Jacobian condition. This
file does not identify that condition with smoothness of a projective scheme.
-/

noncomputable section
namespace EvenQuinticConic
open Matrix MvPolynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- A nonzero kernel vector forces the actual determinant to vanish. -/
theorem det_eq_zero_of_nonzero_kernel (A : Matrix n n K) (P : n → K)
    (hP : P ≠ 0) (hker : A.mulVec P = 0) : A.det = 0 := by
  by_contra hdet
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  exact hP (hinj (hker.trans (Matrix.mulVec_zero A).symm))

/-- A symmetric matrix with nonzero adjugate and a specified nonzero kernel
vector has adjugate exactly a nonzero scalar times that vector's outer square.
The rank-one formula is a conclusion, not an input. -/
theorem adjugate_eq_kernel_outer (A : Matrix n n K) (hA : A.IsSymm)
    (P : n → K) (hP : P ≠ 0) (hker : A.mulVec P = 0)
    (hadj : A.adjugate ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ i j, A.adjugate i j = c * P i * P j := by
  have hdet := det_eq_zero_of_nonzero_kernel A P hP hker
  obtain ⟨k, hk⟩ := exists_diagonal_adjugate_ne_zero A hA hdet hadj
  have hPk : P k ≠ 0 := by
    intro hz
    apply hP
    exact kernel_vector_eq_of_cofactor_pivot A k hk P 0 hker
      (Matrix.mulVec_zero A) hz
  have hprop (i j : n) : P k * A.adjugate i j = A.adjugate k j * P i := by
    have heq : P k • (fun r => A.adjugate r j) = A.adjugate k j • P := by
      apply kernel_vector_eq_of_cofactor_pivot A k hk
      · rw [Matrix.mulVec_smul, adjugate_column_mem_kernel A hdet j, smul_zero]
      · rw [Matrix.mulVec_smul, hker, smul_zero]
      · simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
    exact congrFun heq i
  have hsym : A.adjugate.IsSymm := by
    change A.adjugate.transpose = A.adjugate
    rw [Matrix.adjugate_transpose, hA]
  refine ⟨A.adjugate k k / (P k * P k), div_ne_zero hk (mul_ne_zero hPk hPk), ?_⟩
  intro i j
  have h1 := hprop i j
  have h2 := hprop j k
  rw [hsym.apply k j] at h2
  have heq : A.adjugate i j * (P k * P k) = A.adjugate k k * P i * P j := by
    linear_combination P k * h1 + P i * h2
  calc
    A.adjugate i j = (A.adjugate k k * P i * P j) / (P k * P k) :=
      (eq_div_iff (mul_ne_zero hPk hPk)).mpr heq
    _ = A.adjugate k k / (P k * P k) * P i * P j := by ring

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The actual polynomial matrix of a linear family of matrices. -/
def linearMatrixNet (M : σ → Matrix n n K) : Matrix n n (MvPolynomial σ K) :=
  fun r c => ∑ i, C (M i r c) * X i

omit [Fintype n] [DecidableEq n] [DecidableEq σ] in
/-- Evaluation gives the expected linear combination of matrices. -/
theorem linearMatrixNet_eval (M : σ → Matrix n n K) (t : σ → K) :
    (linearMatrixNet M).map (eval t) = ∑ i, t i • M i := by
  ext r c
  simp [linearMatrixNet, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

omit [Fintype n] [DecidableEq n] in
/-- Each actual formal partial derivative is its coefficient matrix entry. -/
theorem linearMatrixNet_pderiv (M : σ → Matrix n n K) (i : σ) (r c : n) :
    pderiv i (linearMatrixNet M r c) = C (M i r c) := by
  simp [linearMatrixNet, map_sum, pderiv_X, Pi.single_apply]

/-- Evaluating the formal Jacobi formula for a linear net. -/
theorem linearMatrixNet_det_partial (M : σ → Matrix n n K) (t : σ → K) (i : σ) :
    eval t (pderiv i (linearMatrixNet M).det) =
      ∑ r, ∑ c, M i r c * ((linearMatrixNet M).map (eval t)).adjugate c r := by
  rw [eval_pderiv_det_eq_sum_adjugate]
  simp only [linearMatrixNet_pderiv, eval_C]

omit [Fintype n] [DecidableEq n] [DecidableEq σ] in
/-- A linear combination of symmetric coefficient matrices is symmetric. -/
theorem linearMatrixNet_eval_isSymm (M : σ → Matrix n n K)
    (hM : ∀ i, (M i).IsSymm) (t : σ → K) :
    ((linearMatrixNet M).map (eval t)).IsSymm := by
  rw [linearMatrixNet_eval]
  apply Matrix.IsSymm.ext
  intro r c
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(hM i).apply]

/-- At a common isotropic vector in a matrix kernel, every actual partial
of the determinant vanishes, even without any smoothness hypothesis. -/
theorem linearMatrixNet_gradient_zero_of_common_kernel
    (M : σ → Matrix n n K) (hM : ∀ i, (M i).IsSymm)
    (P : n → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (t : σ → K) (hker : ((linearMatrixNet M).map (eval t)).mulVec P = 0) :
    ∀ i, eval t (pderiv i (linearMatrixNet M).det) = 0 := by
  let A := (linearMatrixNet M).map (eval t)
  by_cases ha : A.adjugate = 0
  · exact eval_pderiv_det_eq_zero_of_adjugate_eq_zero (linearMatrixNet M) t ha
  obtain ⟨c, hc, houter⟩ := adjugate_eq_kernel_outer A
    (linearMatrixNet_eval_isSymm M hM t) P hP hker ha
  intro i
  rw [linearMatrixNet_det_partial]
  change (∑ r, ∑ s, M i r s * A.adjugate s r) = 0
  simp_rw [houter]
  calc
    (∑ r, ∑ s, M i r s * (c * P s * P r)) =
        c * dotProduct P ((M i).mulVec P) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = 0 := by rw [hisotropic i, mul_zero]

/-- A common nonzero isotropic vector is in no nonzero member's kernel
when every nonzero determinant-zero vector has a nonzero actual partial.
No geometric smoothness-to-Jacobian comparison is hidden in this input. -/
theorem linearMatrixNet_common_kernel_eq_zero
    (M : σ → Matrix n n K) (hM : ∀ i, (M i).IsSymm)
    (P : n → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : σ → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0)
    (t : σ → K) (hker : ((linearMatrixNet M).map (eval t)).mulVec P = 0) : t = 0 := by
  by_contra ht
  have hdet := det_eq_zero_of_nonzero_kernel
    ((linearMatrixNet M).map (eval t)) P hP hker
  have heval : eval t (linearMatrixNet M).det = 0 :=
    ((eval t).map_det (linearMatrixNet M)).trans hdet
  obtain ⟨i, hi⟩ := hsmooth t ht heval
  exact hi (linearMatrixNet_gradient_zero_of_common_kernel M hM P hP hisotropic t hker i)

/-- The polar coefficient vectors at a common nonzero isotropic vector are
linearly independent under the explicit determinant Jacobian condition. -/
theorem linearMatrixNet_polar_vectors_linearIndependent
    (M : σ → Matrix n n K) (hM : ∀ i, (M i).IsSymm)
    (P : n → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : σ → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    LinearIndependent K (fun i => (M i).mulVec P) := by
  apply Fintype.linearIndependent_iff.mpr
  intro t ht i
  have hker : ((linearMatrixNet M).map (eval t)).mulVec P = 0 := by
    rw [linearMatrixNet_eval, Matrix.sum_mulVec]
    simpa only [Matrix.smul_mulVec] using ht
  exact congrFun (linearMatrixNet_common_kernel_eq_zero M hM P hP hisotropic hsmooth t hker) i

/-- The parameter-to-polar-vector map is genuinely injective. -/
theorem linearMatrixNet_polar_parameter_injective
    (M : σ → Matrix n n K) (hM : ∀ i, (M i).IsSymm)
    (P : n → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : σ → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    Function.Injective (fun t : σ → K => ∑ i, t i • (M i).mulVec P) := by
  have h := (linearMatrixNet_polar_vectors_linearIndependent M hM P hP
    hisotropic hsmooth).fintypeLinearCombination_injective
  simpa only [Fintype.linearCombination_apply] using h

/-- The actual linear functionals with coefficients `Mᵢ P` are independent.
For symmetric matrices these are the polar forms `y ↦ Pᵗ Mᵢ y`. -/
theorem linearMatrixNet_polar_forms_linearIndependent
    (M : σ → Matrix n n K) (hM : ∀ i, (M i).IsSymm)
    (P : n → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : σ → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    LinearIndependent K
      (fun i => (dotProductBilin K K : (n → K) →ₗ[K] (n → K) →ₗ[K] K)
        ((M i).mulVec P)) := by
  have hinj : Function.Injective
      (dotProductBilin K K : (n → K) →ₗ[K] (n → K) →ₗ[K] K) := by
    intro v w h
    funext j
    have he := congrArg (fun f : (n → K) →ₗ[K] K => f (Pi.single j 1)) h
    simpa only [dotProductBilin_apply_apply, dotProduct_single_one] using he
  exact (linearMatrixNet_polar_vectors_linearIndependent M hM P hP
    hisotropic hsmooth).map' _ (LinearMap.ker_eq_bot.mpr hinj)

/-- Once the common point is the first coordinate vector, the first
coordinate of each polar vector vanishes. The remaining coefficients are
therefore still independent; these are precisely the linear forms used in
the incidence model. -/
theorem linearMatrixNet_polar_tails_linearIndependent
    {m : ℕ} (M : σ → Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : ∀ i, (M i).IsSymm) (hbase : ∀ i, M i 0 0 = 0)
    (hsmooth : ∀ t : σ → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    LinearIndependent K (fun i (j : Fin m) => M i j.succ 0) := by
  have hP : (Pi.single 0 1 : Fin (m + 1) → K) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hiso : ∀ i, dotProduct (Pi.single 0 1)
      ((M i).mulVec (Pi.single 0 1)) = 0 := by
    intro i
    simp [single_dotProduct, hbase i]
  have hind := linearMatrixNet_polar_vectors_linearIndependent M hM
    (Pi.single 0 1) hP hiso hsmooth
  apply Fintype.linearIndependent_iff.mpr
  intro t ht i
  apply Fintype.linearIndependent_iff.mp hind t ?_ i
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Finset.sum_apply, Matrix.col, hbase]
  · have hk := congrFun ht k
    simpa [Finset.sum_apply, Matrix.mulVec_single_one, Matrix.col] using hk

end EvenQuinticConic
