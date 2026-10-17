import EvenQuinticConic.IncidenceMinorFromDeterminant
import EvenQuinticConic.NetBasePoint

/-!
# Excluding a zero conic equation in a fiber

A five-dimensional quadratic form divisible by a linear polynomial has
zero adjugate, not merely zero determinant. Consequently every actual
determinant partial of a matrix net vanishes at such a parameter. The
Jacobian hypothesis therefore excludes this degeneration even at singular
members of the net. All assertions here are over the displayed field;
application over a larger field requires a Jacobian hypothesis there.
-/

noncomputable section
set_option maxRecDepth 4096
namespace EvenQuinticConic.Incidence
open Matrix MvPolynomial

variable {K : Type*} [Field K]

/-- A square matrix of size greater than two factoring through two columns
has zero determinant. -/
theorem det_eq_zero_of_factor_through_two {n : ℕ}
    (U : Matrix (Fin (n + 3)) (Fin 2) K)
    (V : Matrix (Fin 2) (Fin (n + 3)) K) : (U * V).det = 0 := by
  by_contra hdet
  have hu : IsUnit (U * V) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hdet)
  have hfull := Matrix.rank_of_isUnit (U * V) hu
  have hle := (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)
  simp only [Fintype.card_fin] at hfull hle
  omega

/-- Every four-by-four cofactor vanishes for an actual five-by-five
matrix factoring through two columns. -/
theorem adjugate_eq_zero_of_factor_through_two
    (U : Matrix (Fin 5) (Fin 2) K) (V : Matrix (Fin 2) (Fin 5) K) :
    (U * V).adjugate = 0 := by
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hsub : (U * V).submatrix j.succAbove i.succAbove =
      U.submatrix j.succAbove id * V.submatrix id i.succAbove := by
    ext a b
    rfl
  rw [hsub, det_eq_zero_of_factor_through_two, mul_zero]
  rfl

/-- A symmetric sum of two outer products has zero adjugate in dimension five. -/
theorem adjugate_outer_sum_eq_zero (a b : Fin 5 → K) :
    Matrix.adjugate (fun i j => a i * b j + b i * a j : Matrix (Fin 5) (Fin 5) K) = 0 := by
  let U : Matrix (Fin 5) (Fin 2) K := fun i j => if j = 0 then a i else b i
  let V : Matrix (Fin 2) (Fin 5) K := fun i j => if i = 0 then b j else a j
  have heq : (fun i j => a i * b j + b i * a j : Matrix (Fin 5) (Fin 5) K) =
      U * V := by
    ext i j
    simp [U, V, Matrix.mul_apply, Fin.sum_univ_two]
  rw [heq]
  exact adjugate_eq_zero_of_factor_through_two U V

/-- The Hessian of a polynomial with a linear factor has zero adjugate. -/
theorem adjugate_hessianAtZero_linear_mul (a : Fin 5 → K)
    (g : MvPolynomial (Fin 5) K) :
    (hessianAtZero (linearPolynomial a * g)).adjugate = 0 := by
  have heq : hessianAtZero (linearPolynomial a * g) =
      (fun i j => a i * eval (fun _ => 0) (pderiv j g) +
        eval (fun _ => 0) (pderiv i g) * a j) := by
    ext i j
    rw [hessianAtZero_linear_mul]
    ring
  rw [heq]
  exact adjugate_outer_sum_eq_zero a (fun i => eval (fun _ => 0) (pderiv i g))

/-- In characteristic different from two a linear factor forces all
cofactors of the symmetric quadratic matrix to vanish. -/
theorem adjugate_eq_zero_of_matrixQuadraticPolynomial_factor
    (h2 : (2 : K) ≠ 0) (A : Matrix (Fin 5) (Fin 5) K) (hA : A.IsSymm)
    (a : Fin 5 → K) (g : MvPolynomial (Fin 5) K)
    (hf : matrixQuadraticPolynomial A = linearPolynomial a * g) : A.adjugate = 0 := by
  have hh := adjugate_hessianAtZero_linear_mul a g
  rw [← hf, hessianAtZero_matrixQuadraticPolynomial, hA] at hh
  have hdouble : A + A = (2 : K) • A := by
    ext i j
    simp [two_mul]
  rw [hdouble, Matrix.adjugate_smul] at hh
  ext i j
  have hij := congrFun (congrFun hh i) j
  change (2 : K) ^ (Fintype.card (Fin 5) - 1) * A.adjugate i j = 0 at hij
  exact (mul_eq_zero.mp hij).resolve_left (pow_ne_zero _ h2)

/-- A member with a linear quadratic-form factor makes every actual
partial derivative of the net determinant zero at its parameter. -/
theorem linearMatrixNet_gradient_zero_of_linear_factor
    (h2 : (2 : K) ≠ 0) (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm) (t : Fin 3 → K)
    (a : Fin 5 → K) (g : MvPolynomial (Fin 5) K)
    (hf : matrixQuadraticPolynomial ((linearMatrixNet M).map (eval t)) =
      linearPolynomial a * g) :
    ∀ i, eval t (pderiv i (linearMatrixNet M).det) = 0 :=
  eval_pderiv_det_eq_zero_of_adjugate_eq_zero (linearMatrixNet M) t
    (adjugate_eq_zero_of_matrixQuadraticPolynomial_factor h2 _
      (linearMatrixNet_eval_isSymm M hM t) a g hf)

/-- The actual Jacobian condition excludes a linear factor in every
nonzero parameter's five-dimensional quadratic form. -/
theorem linearMatrixNet_no_linear_factor_of_jacobian
    (h2 : (2 : K) ≠ 0) (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm)
    (hJac : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0)
    (t : Fin 3 → K) (ht : t ≠ 0) (a : Fin 5 → K)
    (g : MvPolynomial (Fin 5) K) :
    matrixQuadraticPolynomial ((linearMatrixNet M).map (eval t)) ≠
      linearPolynomial a * g := by
  intro hf
  have hd := det_eq_zero_of_matrixQuadraticPolynomial_factor h2 _
    (linearMatrixNet_eval_isSymm M hM t) a g hf
  have he : eval t (linearMatrixNet M).det = 0 :=
    ((eval t).map_det (linearMatrixNet M)).trans hd
  obtain ⟨i, hi⟩ := hJac t ht he
  exact hi (linearMatrixNet_gradient_zero_of_linear_factor h2 M hM t a g hf i)

end EvenQuinticConic.Incidence
