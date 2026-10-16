import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.MvPolynomial.PDeriv
import EvenQuinticConic.AdjugateRankOne

/-!
# The actual gradient of a polynomial matrix determinant

Jacobi's formula is proved from the permutation expansion and the Leibniz
rule. The formula is not a hypothesis. Evaluation identifies its cofactor
terms with the adjugate of the evaluated matrix. Consequently a nonzero
partial derivative forces a nonzero adjugate; at a symmetric singular matrix,
it supplies an actual nonzero diagonal cofactor chart.

These are field-valued Jacobian statements, not an identification of the
cofactor equations with the geometric discriminant cover.
-/

noncomputable section

open Matrix Finset
namespace EvenQuinticConic
variable {R A n : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype n] [DecidableEq n]

omit [Fintype n] in
private theorem derivation_prod_erase (D : Derivation R A A) (s : Finset n) (f : n → A) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha]
    simp only [smul_eq_mul, Finset.erase_insert ha]
    rw [Finset.mul_sum, mul_comm (∏ j ∈ s, f j) (D (f a)), add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≠ a := by intro h; exact ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hia.symm,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ac_rfl

private theorem det_updateCol_derivation (D : Derivation R A A) (M : Matrix n n A)
    (i : n) :
    (M.updateCol i (fun j => D (M j i))).det =
      ∑ s : Equiv.Perm n, ((Equiv.Perm.sign s : ℤ) : A) *
        (D (M (s i) i) * ∏ j ∈ Finset.univ.erase i, M (s j) j) := by
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => M.updateCol i (fun k => D (M k i)) (s j) j) (Finset.mem_univ i)]
  rw [Matrix.updateCol_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact Matrix.updateCol_ne (Finset.mem_erase.mp hj).1

/-- Jacobi's determinant formula for an arbitrary algebraic derivation. -/
theorem derivation_det_eq_sum_adjugate (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, ∑ j, M.adjugate i j * D (M j i) := by
  have h : D M.det = ∑ i, (M.updateCol i (fun j => D (M j i))).det := by
    rw [Matrix.det_apply', map_sum]
    simp only [D.leibniz, D.map_intCast, smul_eq_mul, mul_zero, add_zero,
      derivation_prod_erase, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact (det_updateCol_derivation D M i).symm
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

section Polynomial

open MvPolynomial

variable {σ K : Type*} [CommRing K]

/-- Jacobi's formula for formal partial derivatives of an arbitrary polynomial matrix. -/
theorem pderiv_det_eq_sum_adjugate
    (M : Matrix n n (MvPolynomial σ K)) (i : σ) :
    pderiv i M.det = ∑ r, ∑ c, pderiv i (M r c) * M.adjugate c r := by
  rw [derivation_det_eq_sum_adjugate, Finset.sum_comm]
  simp only [mul_comm]

/-- Evaluation of Jacobi's formula uses the adjugate of the evaluated matrix. -/
theorem eval_pderiv_det_eq_sum_adjugate
    (M : Matrix n n (MvPolynomial σ K)) (v : σ → K) (i : σ) :
    eval v (pderiv i M.det) =
      ∑ r, ∑ c, eval v (pderiv i (M r c)) * (M.map (eval v)).adjugate c r := by
  have hadj : M.adjugate.map (eval v) = (M.map (eval v)).adjugate :=
    (eval v).map_adjugate M
  rw [pderiv_det_eq_sum_adjugate, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [map_mul]
  congr 1
  exact congrFun (congrFun hadj c) r

/-- A vanishing adjugate annihilates every actual partial derivative of the determinant. -/
theorem eval_pderiv_det_eq_zero_of_adjugate_eq_zero
    (M : Matrix n n (MvPolynomial σ K)) (v : σ → K)
    (h : (M.map (eval v)).adjugate = 0) (i : σ) :
    eval v (pderiv i M.det) = 0 := by
  rw [eval_pderiv_det_eq_sum_adjugate]
  simp [h]

/-- One nonzero actual partial derivative forces a nonzero evaluated adjugate. -/
theorem adjugate_ne_zero_of_eval_pderiv_det_ne_zero
    (M : Matrix n n (MvPolynomial σ K)) (v : σ → K) (i : σ)
    (hi : eval v (pderiv i M.det) ≠ 0) :
    (M.map (eval v)).adjugate ≠ 0 := by
  intro h
  exact hi (eval_pderiv_det_eq_zero_of_adjugate_eq_zero M v h i)

end Polynomial

section Field

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- A nonsingular point of a symmetric determinant equation lies on an actual
nonzero diagonal cofactor chart. No corank-one or cofactor-minor assumption is needed. -/
theorem exists_diagonal_adjugate_ne_zero_of_gradient
    (M : Matrix n n (MvPolynomial σ K)) (v : σ → K)
    (hsymm : (M.map (eval v)).IsSymm) (hdet : eval v M.det = 0)
    (hgrad : ∃ i, eval v (pderiv i M.det) ≠ 0) :
    ∃ k, (M.map (eval v)).adjugate k k ≠ 0 := by
  obtain ⟨i, hi⟩ := hgrad
  apply exists_diagonal_adjugate_ne_zero (M.map (eval v)) hsymm
  · exact ((eval v).map_det M).symm.trans hdet
  · exact adjugate_ne_zero_of_eval_pderiv_det_ne_zero M v i hi

end Field

end EvenQuinticConic
