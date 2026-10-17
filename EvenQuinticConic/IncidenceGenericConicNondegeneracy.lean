import EvenQuinticConic.IncidenceParameterFieldIdentification

/-!
# A nonsingular actual generic conic matrix

The actual generic five-dimensional matrix is nonsingular by the geometric
Jacobian certificate. Its isotropic distinguished coordinate therefore has a
nonzero polar coefficient among the other four coordinates. We choose that
pivot, explicitly permute it into the elimination position, and apply the
proved polar restriction calculation. The resulting actual ternary matrix
is symmetric and has nonzero determinant.

The final theorem assumes neither a chosen nonzero polar coefficient nor
nonsingularity of the restricted matrix. No conic scheme or smoothness of a
scheme is asserted by this matrix calculation alone.
-/

noncomputable section
set_option maxRecDepth 4096

namespace EvenQuinticConic.Incidence

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- A nonsingular matrix whose distinguished diagonal entry is zero must
have a nonzero polar coefficient in one of the remaining positions. -/
theorem exists_incidence_polar_pivot_of_det_ne_zero
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hbase : A 0 0 = 0) (hdet : A.det ≠ 0) :
    ∃ r : Fin (n + 1), A r.succ 0 ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  apply hdet
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  exact Fin.cases hbase (fun r => hn r) i

/-- Putting a polar pivot into position one permutes rows and columns
together, so it preserves the determinant exactly. -/
@[simp] theorem incidencePivotMatrix_det
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (r : Fin (n + 1)) :
    (incidencePivotMatrix A r).det = A.det :=
  Matrix.det_submatrix_equiv_self (incidencePivotEquiv r) A

/-- The existing restriction theorem applies at any nonzero polar pivot,
not just at the initially numbered coordinate one. -/
theorem incidencePivotRestrictedMatrix_det_ne_zero
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (hA : A.IsSymm)
    (hbase : A 0 0 = 0) (r : Fin (n + 1)) (hr : A r.succ 0 ≠ 0)
    (hdet : A.det ≠ 0) :
    (incidenceRestrictedMatrix (incidencePivotMatrix A r)).det ≠ 0 := by
  apply incidenceRestrictedMatrix_det_ne_zero
    (incidencePivotMatrix A r) (incidencePivotMatrix_isSymm A hA r)
  · simpa only [incidencePivotMatrix, Matrix.submatrix_apply,
      incidencePivotEquiv_zero] using hbase
  · simpa only [incidencePivotMatrix, Matrix.submatrix_apply,
      incidencePivotEquiv_one, incidencePivotEquiv_zero] using hr
  · simpa only [incidencePivotMatrix_det] using hdet

/-- Both the nonzero pivot and the nonsingular polar restriction follow
from the original matrix's nonsingularity. -/
theorem exists_incidence_nonsingular_polar_restriction
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (hA : A.IsSymm)
    (hbase : A 0 0 = 0) (hdet : A.det ≠ 0) :
    ∃ r : Fin (n + 1), A r.succ 0 ≠ 0 ∧
      (incidenceRestrictedMatrix (incidencePivotMatrix A r)).det ≠ 0 := by
  obtain ⟨r, hr⟩ := exists_incidence_polar_pivot_of_det_ne_zero A hbase hdet
  exact ⟨r, hr, incidencePivotRestrictedMatrix_det_ne_zero A hA hbase r hr hdet⟩

/-- The actual ternary matrix obtained from the actual generic member of
the matrix net by eliminating the specified polar coordinate. -/
def incidenceGenericConicMatrix
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) (r : Fin 4) :
    Matrix (Fin 3) (Fin 3) (incidenceParameterSubfield M k p h) :=
  incidenceRestrictedMatrix (incidencePivotMatrix (incidenceGenericMatrix M k p h) r)

/-- The constructed generic conic matrix is symmetric. -/
theorem incidenceGenericConicMatrix_isSymm
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) (r : Fin 4) :
    (incidenceGenericConicMatrix M k p h r).IsSymm :=
  incidenceRestrictedMatrix_isSymm _
    (incidencePivotMatrix_isSymm _ (incidenceGenericMatrix_isSymm M hM k p h) r)

/-- Its entries are the literal coefficients after solving the actual polar
equation for coordinate `r`, in `r.succAbove` order. -/
theorem incidenceGenericConicMatrix_apply
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (r : Fin 4) (i j : Fin 3) :
    let A := incidenceGenericMatrix M k p h
    incidenceGenericConicMatrix M k p h r i j =
      A (r.succAbove i).succ (r.succAbove j).succ -
      A (r.succAbove i).succ r.succ * A (r.succAbove j).succ 0 / A r.succ 0 -
      A (r.succAbove i).succ 0 / A r.succ 0 * A r.succ (r.succAbove j).succ +
      A (r.succAbove i).succ 0 * A r.succ r.succ * A (r.succAbove j).succ 0 /
        (A r.succ 0)^2 :=
  incidencePivotRestrictedMatrix_apply _ r i j

/-- The ternary quadratic expression equals the original quadratic
expression after the explicit pivot permutation and polar substitution. -/
theorem incidenceGenericConicMatrix_quadratic
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (r : Fin 4) (v : Fin 3 → incidenceParameterSubfield M k p h) :
    let A := incidencePivotMatrix (incidenceGenericMatrix M k p h) r
    let E := incidenceEliminationMatrix A
    dotProduct v ((incidenceGenericConicMatrix M k p h r).mulVec v) =
      dotProduct (E.mulVec v) (A.mulVec (E.mulVec v)) :=
  incidenceRestrictedMatrix_quadratic _ v

/-- From the actual geometric hypotheses, choose a polar pivot and obtain
the actual symmetric nonsingular ternary matrix over the actual parameter
subfield. No pivot or determinant nonvanishing is an additional input. -/
theorem exists_incidenceGenericConicMatrix_nondegenerate [Infinite K]
    (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    ∃ r : Fin 4, incidenceGenericMatrix M k p h r.succ 0 ≠ 0 ∧
      (incidenceGenericConicMatrix M k p h r).IsSymm ∧
      (incidenceGenericConicMatrix M k p h r).det ≠ 0 := by
  obtain ⟨r, hr, hdet⟩ := exists_incidence_nonsingular_polar_restriction
    (incidenceGenericMatrix M k p h)
    (incidenceGenericMatrix_isSymm M hM k p h)
    (incidenceGenericMatrix_zero_zero M hbase k p h)
    (incidenceGenericMatrix_det_ne_zero h2 M hM hbase hCert k p h)
  exact ⟨r, hr, incidenceGenericConicMatrix_isSymm M hM k p h r, hdet⟩

/-- One can choose the eliminated coordinate among the affine coordinates
of the given spatial chart. Thus the construction also retains its original
dehomogenizing coordinate. -/
theorem exists_incidenceGenericConicMatrix_nondegenerate_affine [Infinite K]
    (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    ∃ q : Fin 3,
      incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0 ∧
      (incidenceGenericConicMatrix M k p h (p.succAbove q)).IsSymm ∧
      (incidenceGenericConicMatrix M k p h (p.succAbove q)).det ≠ 0 := by
  obtain ⟨q, hq⟩ :=
    incidenceGenericMatrix_exists_affine_coefficient_ne_zero M hM hbase hCert k p h
  refine ⟨q, hq, incidenceGenericConicMatrix_isSymm M hM k p h _, ?_⟩
  exact incidencePivotRestrictedMatrix_det_ne_zero
    (incidenceGenericMatrix M k p h)
    (incidenceGenericMatrix_isSymm M hM k p h)
    (incidenceGenericMatrix_zero_zero M hbase k p h)
    (p.succAbove q) hq
    (incidenceGenericMatrix_det_ne_zero h2 M hM hbase hCert k p h)

end EvenQuinticConic.Incidence
