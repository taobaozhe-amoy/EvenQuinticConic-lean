import EvenQuinticConic.IncidenceGenericConicNondegeneracy
import EvenQuinticConic.IncidenceLinearElimination

/-!
# Compatibility of the two actual conic eliminations

Normalizing spatial coordinate `p` and then eliminating affine coordinate
`q` leaves the same ordered pair of coordinates as eliminating homogeneous
coordinate `p.succAbove q` and then normalizing coordinate `q.predAbove p`.
The residual polynomial is exactly the dehomogenized quadratic polynomial
of the previously constructed ternary matrix.
-/

noncomputable section
set_option maxRecDepth 4096

namespace EvenQuinticConic.Incidence

open MvPolynomial Matrix

variable {F : Type*} [Field F]

/-- The retained homogeneous coordinate corresponding to the original
normalizing coordinate. -/
@[simp] theorem incidenceConic_normalizing_index (p : Fin 4) (q : Fin 3) :
    (p.succAbove q).succAbove (q.predAbove p) = p :=
  Fin.succAbove_succAbove_predAbove p q

/-- Both orders of deleting the two specified coordinates retain the same
ordered pair; no additional permutation of the two affine variables occurs. -/
@[simp] theorem incidenceConic_retained_index (p : Fin 4) (q : Fin 3) (j : Fin 2) :
    (p.succAbove q).succAbove ((q.predAbove p).succAbove j) =
      p.succAbove (q.succAbove j) :=
  Fin.succAbove_succAbove_succAbove_predAbove p q j

/-- The actual four spatial coordinates after normalization and affine
polar elimination. -/
def incidenceAffineSpatialCoordinates (A : Matrix (Fin 5) (Fin 5) F)
    (p : Fin 4) (q : Fin 3) : Fin 4 → MvPolynomial (Fin 2) F :=
  chartLift p (Fin.insertNth q
    (affineEliminatedCoordinate (fun j => A (p.succAbove j).succ 0) (A p.succ 0) q) X)

@[simp] theorem incidenceAffineSpatialCoordinates_pivot
    (A : Matrix (Fin 5) (Fin 5) F) (p : Fin 4) (q : Fin 3) :
    incidenceAffineSpatialCoordinates A p q p = 1 := by
  simp [incidenceAffineSpatialCoordinates]

@[simp] theorem incidenceAffineSpatialCoordinates_eliminated
    (A : Matrix (Fin 5) (Fin 5) F) (p : Fin 4) (q : Fin 3) :
    incidenceAffineSpatialCoordinates A p q (p.succAbove q) =
      affineEliminatedCoordinate (fun j => A (p.succAbove j).succ 0) (A p.succ 0) q := by
  simp [incidenceAffineSpatialCoordinates]

@[simp] theorem incidenceAffineSpatialCoordinates_retained
    (A : Matrix (Fin 5) (Fin 5) F) (p : Fin 4) (q : Fin 3) (j : Fin 2) :
    incidenceAffineSpatialCoordinates A p q (p.succAbove (q.succAbove j)) = X j := by
  simp [incidenceAffineSpatialCoordinates]

theorem dehomogenizeAt_linearPolynomial {n : ℕ} (s : Fin (n + 1))
    (b : Fin (n + 1) → F) :
    dehomogenizeAt s (linearPolynomial b) =
      C (b s) + ∑ j, C (b (s.succAbove j)) * X j := by
  simp only [linearPolynomial, map_sum, map_mul, dehomogenizeAt_C]
  rw [Fin.sum_univ_succAbove _ s]
  simp

/-- The solved polar coordinate agrees in the two elimination procedures. -/
theorem incidenceConic_eliminated_coordinate
    (A : Matrix (Fin 5) (Fin 5) F) (p : Fin 4) (q : Fin 3) :
    dehomogenizeAt (q.predAbove p)
      (linearPolynomial (incidenceEliminationMatrix (incidencePivotMatrix A (p.succAbove q)) 1)) =
    affineEliminatedCoordinate (fun j => A (p.succAbove j).succ 0) (A p.succ 0) q := by
  rw [dehomogenizeAt_linearPolynomial]
  simp only [incidenceEliminationMatrix_one, incidencePivotMatrix, Matrix.submatrix_apply,
    incidencePivotEquiv_tail, incidencePivotEquiv_one, incidencePivotEquiv_zero,
    incidenceConic_normalizing_index, incidenceConic_retained_index,
    affineEliminatedCoordinate, div_eq_mul_inv, map_neg, map_mul]
  rw [mul_add, Finset.mul_sum]
  -- Keep inverses in the coefficient field; the polynomial coefficient map
  -- is not a map of fields.
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · ring

/-- Every coordinate of the homogeneous elimination, followed by the
retained normalization, is the corresponding affine-elimination coordinate. -/
theorem incidenceConic_elimination_coordinates
    (A : Matrix (Fin 5) (Fin 5) F) (p : Fin 4) (q : Fin 3) (i : Fin 5) :
    dehomogenizeAt (q.predAbove p)
      (linearPolynomial (incidenceEliminationMatrix
        (incidencePivotMatrix A (p.succAbove q)) i)) =
      Fin.cases 0 (incidenceAffineSpatialCoordinates A p q)
        (incidencePivotEquiv (p.succAbove q) i) := by
  classical
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [linearPolynomial]
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa using incidenceConic_eliminated_coordinate A p q
    · simp only [incidencePivotEquiv_tail, Fin.cases_succ]
      have hlinear : linearPolynomial (incidenceEliminationMatrix
          (incidencePivotMatrix A (p.succAbove q)) j.succ.succ) = X j := by
        simp [linearPolynomial]
      rw [hlinear]
      induction j using Fin.succAboveCases (q.predAbove p) with
      | x => simp
      | p j => simp

/-- The composite affine substitution acts on all polynomials by the
displayed four actual spatial coordinates. -/
theorem incidenceAffineSpatialCoordinates_substitution
    (A : Matrix (Fin 5) (Fin 5) F) (p : Fin 4) (q : Fin 3)
    (P : MvPolynomial (Fin 4) F) :
    affineEliminationSubstitution (fun j => A (p.succAbove j).succ 0) (A p.succ 0) q
      (dehomogenizeAt p P) = aeval (incidenceAffineSpatialCoordinates A p q) P := by
  have he : (affineEliminationSubstitution (fun j => A (p.succAbove j).succ 0)
      (A p.succ 0) q).comp (dehomogenizeAt p) =
        aeval (incidenceAffineSpatialCoordinates A p q) := by
    ext i
    induction i using Fin.succAboveCases p with
    | x => simp
    | p j =>
      induction j using Fin.succAboveCases q with
      | x => simp
      | p j => simp
  exact congrArg (fun f : MvPolynomial (Fin 4) F →ₐ[F] MvPolynomial (Fin 2) F => f P) he

/-- Simultaneously reindexing a quadratic matrix and its coordinates
preserves its actual polynomial evaluation. -/
theorem matrixQuadraticPolynomial_aeval_reindex
    {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R] [Algebra F R]
    (A : Matrix κ κ F) (e : ι ≃ κ) (x : κ → R) :
    aeval (x ∘ e) (matrixQuadraticPolynomial (A.submatrix e e)) =
      aeval x (matrixQuadraticPolynomial A) := by
  simp only [matrixQuadraticPolynomial, map_sum, map_mul, aeval_C, aeval_X,
    Matrix.submatrix_apply, Function.comp_apply]
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  rfl

/-- Inserting the distinguished zero coordinate recovers the full quadratic
from its spatial four-by-four block. -/
theorem matrixQuadraticPolynomial_aeval_zero_cons
    {R : Type*} [CommRing R] [Algebra F R]
    (A : Matrix (Fin 5) (Fin 5) F) (x : Fin 4 → R) :
    aeval x (matrixQuadraticPolynomial (A.submatrix Fin.succ Fin.succ)) =
      aeval (Fin.cases 0 x) (matrixQuadraticPolynomial A) := by
  simp only [matrixQuadraticPolynomial, map_sum, map_mul, aeval_C, aeval_X,
    Matrix.submatrix_apply]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
    Fin.cases_succ]
  apply Finset.sum_congr rfl
  intro i _
  conv_rhs => rw [Fin.sum_univ_succ]
  simp

/-- The residual affine quadratic is exactly the dehomogenization of the
ternary matrix quadratic. This is a polynomial identity, so no smoothness,
symmetry, or nonzero-pivot hypothesis is needed for this compatibility alone. -/
theorem affineElimination_incidenceQuadratic_eq_dehomogenize
    (A : Matrix (Fin 5) (Fin 5) F) (p : Fin 4) (q : Fin 3) :
    affineEliminationSubstitution (fun j => A (p.succAbove j).succ 0) (A p.succ 0) q
      (dehomogenizeAt p (matrixQuadraticPolynomial (A.submatrix Fin.succ Fin.succ))) =
    dehomogenizeAt (q.predAbove p)
      (matrixQuadraticPolynomial
        (incidenceRestrictedMatrix (incidencePivotMatrix A (p.succAbove q)))) := by
  let B := incidencePivotMatrix A (p.succAbove q)
  let x : Fin 5 → MvPolynomial (Fin 2) F :=
    Fin.cases 0 (incidenceAffineSpatialCoordinates A p q)
  have he : (dehomogenizeAt (q.predAbove p)).comp
      (aeval (fun i => linearPolynomial (incidenceEliminationMatrix B i))) =
        aeval (x ∘ incidencePivotEquiv (p.succAbove q)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X]
    exact incidenceConic_elimination_coordinates A p q i
  have heP := congrArg
    (fun f : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 2) F =>
      f (matrixQuadraticPolynomial B)) he
  calc
    _ = aeval (incidenceAffineSpatialCoordinates A p q)
        (matrixQuadraticPolynomial (A.submatrix Fin.succ Fin.succ)) :=
      incidenceAffineSpatialCoordinates_substitution A p q _
    _ = aeval x (matrixQuadraticPolynomial A) :=
      matrixQuadraticPolynomial_aeval_zero_cons A _
    _ = aeval (x ∘ incidencePivotEquiv (p.succAbove q))
        (matrixQuadraticPolynomial B) :=
      (matrixQuadraticPolynomial_aeval_reindex A (incidencePivotEquiv (p.succAbove q)) x).symm
    _ = dehomogenizeAt (q.predAbove p)
        (aeval (fun i => linearPolynomial (incidenceEliminationMatrix B i))
          (matrixQuadraticPolynomial B)) := heP.symm
    _ = _ := by rw [incidenceRestrictedQuadratic_substitution]

/-- Specialization to the actual generic matrix over the actual Cramer
parameter subfield, with exactly the two affine variables used by the
generic-fiber presentation. -/
theorem incidenceGenericConicMatrix_dehomogenize
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) F) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) (q : Fin 3) :
    let A := incidenceGenericMatrix M k p h
    affineEliminationSubstitution (fun j => A (p.succAbove j).succ 0) (A p.succ 0) q
      (dehomogenizeAt p (matrixQuadraticPolynomial (A.submatrix Fin.succ Fin.succ))) =
    dehomogenizeAt (q.predAbove p)
      (matrixQuadraticPolynomial (incidenceGenericConicMatrix M k p h (p.succAbove q))) :=
  affineElimination_incidenceQuadratic_eq_dehomogenize _ p q

end EvenQuinticConic.Incidence
