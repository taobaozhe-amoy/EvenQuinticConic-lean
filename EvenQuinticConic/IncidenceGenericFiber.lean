import EvenQuinticConic.IncidenceDehomogenization
import EvenQuinticConic.IncidenceFiberNondegeneracy

/-!
# The actual restricted conic matrix on a polar chart

A nonsingular symmetric matrix with an isotropic first coordinate induces a
nonsingular quadratic form after imposing its polar linear equation and
quotienting by that isotropic coordinate. This file constructs the elimination
matrix explicitly; nonsingularity of the restricted matrix is a conclusion.
No irreducibility, generic-fiber identification, or dominance is assumed or
claimed by this calculation.
-/

noncomputable section
namespace EvenQuinticConic.Incidence
open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The columns give the solutions with zeroth coordinate zero of the polar
linear equation, using the nonzero coefficient in position `(1,0)`. -/
def incidenceEliminationMatrix (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) :
    Matrix (Fin (n + 2)) (Fin n) K :=
  fun i j => Fin.cases 0
    (Fin.cases (-(A j.succ.succ 0 / A 1 0)) (fun k => if k = j then 1 else 0)) i

/-- The actual restricted quadratic form in the remaining coordinates. -/
def incidenceRestrictedMatrix (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) :
    Matrix (Fin n) (Fin n) K :=
  (incidenceEliminationMatrix A).transpose * A * incidenceEliminationMatrix A

@[simp] theorem incidenceEliminationMatrix_zero
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (j : Fin n) :
    incidenceEliminationMatrix A 0 j = 0 := rfl

@[simp] theorem incidenceEliminationMatrix_one
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (j : Fin n) :
    incidenceEliminationMatrix A 1 j = -(A j.succ.succ 0 / A 1 0) := rfl

@[simp] theorem incidenceEliminationMatrix_tail
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (i j : Fin n) :
    incidenceEliminationMatrix A i.succ.succ j = if i = j then 1 else 0 := rfl

@[simp] theorem incidenceEliminationMatrix_mulVec_zero
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (v : Fin n → K) :
    (incidenceEliminationMatrix A).mulVec v 0 = 0 := by
  simp [Matrix.mulVec, dotProduct]

@[simp] theorem incidenceEliminationMatrix_mulVec_one
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (v : Fin n → K) :
    (incidenceEliminationMatrix A).mulVec v 1 =
      -(∑ j, A j.succ.succ 0 * v j) / A 1 0 := by
  simp only [Matrix.mulVec, dotProduct, incidenceEliminationMatrix_one,
    div_eq_mul_inv, neg_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp] theorem incidenceEliminationMatrix_mulVec_tail
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (v : Fin n → K) (i : Fin n) :
    (incidenceEliminationMatrix A).mulVec v i.succ.succ = v i := by
  classical
  simp [Matrix.mulVec, dotProduct]

@[simp] theorem incidenceEliminationMatrix_transpose_mulVec
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (w : Fin (n + 2) → K) (i : Fin n) :
    (incidenceEliminationMatrix A).transpose.mulVec w i =
      w i.succ.succ - A i.succ.succ 0 / A 1 0 * w 1 := by
  classical
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.transpose_apply,
    sub_eq_add_neg, add_comm]

/-- The elimination columns really satisfy the polar equation. -/
theorem incidenceEliminationMatrix_polar_zero
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hpivot : A 1 0 ≠ 0) (v : Fin n → K) :
    A.mulVec ((incidenceEliminationMatrix A).mulVec v) 0 = 0 := by
  change (∑ i, A 0 i * (incidenceEliminationMatrix A).mulVec v i) = 0
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [incidenceEliminationMatrix_mulVec_zero,
    incidenceEliminationMatrix_mulVec_one, incidenceEliminationMatrix_mulVec_tail,
    Fin.succ_zero_eq_one, mul_zero, zero_add]
  rw [← hA.apply 0 1]
  have hsum : (∑ j : Fin n, A 0 j.succ.succ * v j) =
      ∑ j : Fin n, A j.succ.succ 0 * v j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hA.apply 0 j.succ.succ]
  rw [hsum]
  field_simp
  ring

/-- Restriction preserves symmetry. -/
theorem incidenceRestrictedMatrix_isSymm
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (hA : A.IsSymm) :
    (incidenceRestrictedMatrix A).IsSymm := by
  unfold incidenceRestrictedMatrix
  change ((incidenceEliminationMatrix A).transpose * A *
    incidenceEliminationMatrix A).transpose = _
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA,
    Matrix.mul_assoc]

/-- Coefficients of the actual quadratic obtained by eliminating the pivot
variable in the polar equation. -/
theorem incidenceRestrictedMatrix_apply
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (i j : Fin n) :
    incidenceRestrictedMatrix A i j =
      A i.succ.succ j.succ.succ - A i.succ.succ 1 * A j.succ.succ 0 / A 1 0 -
      A i.succ.succ 0 / A 1 0 * A 1 j.succ.succ +
      A i.succ.succ 0 * A 1 1 * A j.succ.succ 0 / (A 1 0)^2 := by
  classical
  simp [incidenceRestrictedMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_succ]
  ring

/-- If the actual restricted matrix vanishes, the original matrix is the
sum of two explicitly displayed outer products. -/
theorem incidenceRestrictedMatrix_eq_zero_reconstruction
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0) (hpivot : A 1 0 ≠ 0)
    (hB : incidenceRestrictedMatrix A = 0) (i j : Fin (n + 2)) :
    A i j = A i 0 * (A 1 j / A 1 0 - A 1 1 * A j 0 / (A 1 0)^2) +
      (A i 1 / A 1 0) * A j 0 := by
  have h01 : A 0 1 = A 1 0 := hA.apply 1 0
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · rw [hbase, h01]
    simp only [zero_mul, zero_add, div_self hpivot, one_mul]
    exact hA.apply j 0
  · change A 1 j = A 1 0 * (A 1 j / A 1 0 - A 1 1 * A j 0 / (A 1 0)^2) +
      (A 1 1 / A 1 0) * A j 0
    field_simp
    ring
  · refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    · simp [hbase, hpivot]
    · change A i.succ.succ 1 =
        A i.succ.succ 0 * (A 1 1 / A 1 0 - A 1 1 * A 1 0 / (A 1 0)^2) +
          (A i.succ.succ 1 / A 1 0) * A 1 0
      field_simp
      ring
    · have h := congrArg (fun B => B i j) hB
      change incidenceRestrictedMatrix A i j = 0 at h
      rw [incidenceRestrictedMatrix_apply] at h
      change A i.succ.succ j.succ.succ -
        A i.succ.succ 1 * A j.succ.succ 0 / A 1 0 -
        A i.succ.succ 0 / A 1 0 * A 1 j.succ.succ +
        A i.succ.succ 0 * A 1 1 * A j.succ.succ 0 / (A 1 0)^2 = 0 at h
      field_simp at h ⊢
      linear_combination h

/-- Vanishing of the restricted quadratic matrix gives a genuine
factorization through a two-dimensional vector space. -/
theorem incidenceRestrictedMatrix_eq_zero_factorization
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0) (hpivot : A 1 0 ≠ 0)
    (hB : incidenceRestrictedMatrix A = 0) :
    ∃ U : Matrix (Fin (n + 2)) (Fin 2) K,
      ∃ V : Matrix (Fin 2) (Fin (n + 2)) K, A = U * V := by
  let U : Matrix (Fin (n + 2)) (Fin 2) K :=
    fun i k => if k = 0 then A i 0 else A i 1 / A 1 0
  let V : Matrix (Fin 2) (Fin (n + 2)) K :=
    fun k j => if k = 0 then A 1 j / A 1 0 - A 1 1 * A j 0 / (A 1 0)^2 else A j 0
  refine ⟨U, V, ?_⟩
  ext i j
  simpa [U, V, Matrix.mul_apply, Fin.sum_univ_two] using
    incidenceRestrictedMatrix_eq_zero_reconstruction A hA hbase hpivot hB i j

/-- Evaluation of the restricted quadratic is evaluation of the original
quadratic at the displayed elimination coordinates. -/
theorem incidenceRestrictedMatrix_quadratic
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (v : Fin n → K) :
    dotProduct v ((incidenceRestrictedMatrix A).mulVec v) =
      dotProduct ((incidenceEliminationMatrix A).mulVec v)
        (A.mulVec ((incidenceEliminationMatrix A).mulVec v)) := by
  unfold incidenceRestrictedMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp only [Matrix.vecMul_transpose]

/-- A kernel vector of the restricted matrix lifts to a kernel vector of
`A` after a correction in its isotropic coordinate. -/
theorem incidenceRestrictedMatrix_kernel_eq_zero
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0) (hpivot : A 1 0 ≠ 0)
    (hdet : A.det ≠ 0) (v : Fin n → K)
    (hv : (incidenceRestrictedMatrix A).mulVec v = 0) : v = 0 := by
  let L := incidenceEliminationMatrix A
  let w := A.mulVec (L.mulVec v)
  have hwzero : w 0 = 0 := incidenceEliminationMatrix_polar_zero A hA hpivot v
  have hwtail (j : Fin n) : w j.succ.succ = A j.succ.succ 0 / A 1 0 * w 1 := by
    have h := congrFun hv j
    change ((L.transpose * A * L).mulVec v) j = 0 at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
    change (incidenceEliminationMatrix A).transpose.mulVec w j = 0 at h
    rw [incidenceEliminationMatrix_transpose_mulVec] at h
    exact sub_eq_zero.mp h
  let c := w 1 / A 1 0
  have hkernel : A.mulVec (L.mulVec v - c • (Pi.single 0 1 : Fin (n + 2) → K)) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one]
    change w - c • A.col 0 = 0
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
    · simp [Pi.sub_apply, Pi.smul_apply, Matrix.col, hwzero, hbase]
    · change w 1 - c * A 1 0 = 0
      dsimp [c]
      field_simp
      ring
    · change w j.succ.succ - c * A j.succ.succ 0 = 0
      rw [hwtail]
      dsimp [c]
      ring
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    (A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  have hcorrected : L.mulVec v - c • (Pi.single 0 1 : Fin (n + 2) → K) = 0 :=
    hinj (hkernel.trans (Matrix.mulVec_zero A).symm)
  funext j
  have hj := congrFun hcorrected j.succ.succ
  simpa [L, Pi.sub_apply, Pi.smul_apply, Pi.single_apply] using hj

/-- Nonsingularity of the original matrix implies nonsingularity of the
actual restriction. In dimension five this is the ternary conic matrix. -/
theorem incidenceRestrictedMatrix_det_ne_zero
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0) (hpivot : A 1 0 ≠ 0)
    (hdet : A.det ≠ 0) : (incidenceRestrictedMatrix A).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (incidenceRestrictedMatrix A).isUnit_iff_isUnit_det.mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w h
  have hz : (incidenceRestrictedMatrix A).mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.mp (incidenceRestrictedMatrix_kernel_eq_zero A hA hbase hpivot hdet
    (v - w) hz)

/-- Evaluation of the polynomial associated to a matrix agrees with its
ordinary quadratic expression, over any coefficient homomorphism. -/
theorem matrixQuadraticPolynomial_eval₂
    {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]
    (f : R →+* S) (x : ι → S) (A : Matrix ι ι R) :
    MvPolynomial.eval₂ f x (matrixQuadraticPolynomial A) =
      dotProduct x ((A.map f).mulVec x) := by
  simp only [matrixQuadraticPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A linear substitution in the actual quadratic polynomial gives the
congruent matrix, as an equality of polynomials. -/
theorem matrixQuadraticPolynomial_linear_substitution
    {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
    (A : Matrix ι ι R) (L : Matrix ι κ R) :
    MvPolynomial.aeval (fun i => linearPolynomial (L i))
        (matrixQuadraticPolynomial A) =
      matrixQuadraticPolynomial (L.transpose * A * L) := by
  let f : R →+* MvPolynomial κ R := MvPolynomial.C
  have hX (B : Matrix κ κ R) : matrixQuadraticPolynomial B =
      dotProduct MvPolynomial.X ((B.map f).mulVec MvPolynomial.X) := by
    simpa only [f, MvPolynomial.eval₂_eta] using
      matrixQuadraticPolynomial_eval₂ f MvPolynomial.X B
  have hlinear : (fun i => linearPolynomial (L i)) =
      (L.map f).mulVec MvPolynomial.X := by
    rfl
  change MvPolynomial.eval₂ f (fun i => linearPolynomial (L i))
      (matrixQuadraticPolynomial A) = _
  rw [matrixQuadraticPolynomial_eval₂, hlinear, hX]
  rw [Matrix.map_mul, Matrix.map_mul]
  change dotProduct ((L.map f).mulVec MvPolynomial.X)
      ((A.map f).mulVec ((L.map f).mulVec MvPolynomial.X)) =
    dotProduct MvPolynomial.X
      (((L.map f).transpose * A.map f * L.map f).mulVec MvPolynomial.X)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  symm
  rw [Matrix.dotProduct_mulVec]
  simp only [Matrix.vecMul_transpose]

/-- Substituting the displayed solutions of the polar equation produces
exactly the restricted quadratic used above. -/
theorem incidenceRestrictedQuadratic_substitution
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) :
    MvPolynomial.aeval (fun i => linearPolynomial (incidenceEliminationMatrix A i))
        (matrixQuadraticPolynomial A) =
      matrixQuadraticPolynomial (incidenceRestrictedMatrix A) :=
  matrixQuadraticPolynomial_linear_substitution A (incidenceEliminationMatrix A)

/-- In characteristic different from two a nonzero symmetric matrix gives
a nonzero actual quadratic polynomial. -/
theorem matrixQuadraticPolynomial_ne_zero_of_isSymm
    {ι : Type*} [Fintype ι] (h2 : (2 : K) ≠ 0)
    (B : Matrix ι ι K) (hB : B.IsSymm) (hBzero : B ≠ 0) :
    matrixQuadraticPolynomial B ≠ 0 := by
  intro hzero
  have hh := congrArg hessianAtZero hzero
  rw [hessianAtZero_matrixQuadraticPolynomial, hB] at hh
  apply hBzero
  ext i j
  have hij := congrArg (fun A : Matrix ι ι K => A i j) hh
  change B i j + B i j = 0 at hij
  exact (mul_eq_zero.mp (show (2 : K) * B i j = 0 by simpa [two_mul] using hij)).resolve_left h2

/-- The eliminated conic is a nonzero polynomial whenever its displayed
symmetric coefficient matrix is nonzero. -/
theorem incidenceRestrictedQuadratic_ne_zero
    (h2 : (2 : K) ≠ 0) (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : A.IsSymm) (hB : incidenceRestrictedMatrix A ≠ 0) :
    matrixQuadraticPolynomial (incidenceRestrictedMatrix A) ≠ 0 :=
  matrixQuadraticPolynomial_ne_zero_of_isSymm h2 _
    (incidenceRestrictedMatrix_isSymm A hA) hB

/-- A nonzero adjugate already excludes a zero restricted matrix; a nonzero
determinant is not required, so rank-four singular members are included. -/
theorem incidenceRestrictedMatrix_ne_zero_of_adjugate
    (A : Matrix (Fin 5) (Fin 5) K) (hA : A.IsSymm)
    (hbase : A 0 0 = 0) (hpivot : A 1 0 ≠ 0) (hadj : A.adjugate ≠ 0) :
    incidenceRestrictedMatrix A ≠ 0 := by
  intro hB
  obtain ⟨U, V, hUV⟩ := incidenceRestrictedMatrix_eq_zero_factorization A hA hbase hpivot hB
  apply hadj
  rw [hUV]
  exact adjugate_eq_zero_of_factor_through_two U V

/-- Reorder the tail coordinates so its first coordinate is the selected
polar pivot and its remaining coordinates keep their original order. -/
def incidenceTailPivotEquiv (p : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) :=
  (finSuccEquiv' 0).trans (finSuccEquiv' p).symm

@[simp] theorem incidenceTailPivotEquiv_zero (p : Fin (n + 1)) :
    incidenceTailPivotEquiv p 0 = p := by simp [incidenceTailPivotEquiv]

@[simp] theorem incidenceTailPivotEquiv_succ (p : Fin (n + 1)) (j : Fin n) :
    incidenceTailPivotEquiv p j.succ = p.succAbove j := by
  change (finSuccEquiv' p).symm ((finSuccEquiv' 0) ((0 : Fin (n + 1)).succAbove j)) = _
  rw [finSuccEquiv'_succAbove, finSuccEquiv'_symm_some]

/-- Extend the tail reordering by fixing the distinguished isotropic
coordinate. -/
def incidencePivotEquiv (p : Fin (n + 1)) : Fin (n + 2) ≃ Fin (n + 2) :=
  (finSuccEquiv' 0).trans
    ((Equiv.optionCongr (incidenceTailPivotEquiv p)).trans (finSuccEquiv' 0).symm)

@[simp] theorem incidencePivotEquiv_zero (p : Fin (n + 1)) :
    incidencePivotEquiv p 0 = 0 := by simp [incidencePivotEquiv]

@[simp] theorem incidencePivotEquiv_succ (p : Fin (n + 1)) (j : Fin (n + 1)) :
    incidencePivotEquiv p j.succ = (incidenceTailPivotEquiv p j).succ := by
  change (finSuccEquiv' 0).symm
    (Equiv.optionCongr (incidenceTailPivotEquiv p)
      ((finSuccEquiv' 0) ((0 : Fin (n + 2)).succAbove j))) = _
  rw [finSuccEquiv'_succAbove]
  rfl

@[simp] theorem incidencePivotEquiv_one (p : Fin (n + 1)) :
    incidencePivotEquiv p 1 = p.succ := by
  change incidencePivotEquiv p (Fin.succ 0) = p.succ
  simp only [incidencePivotEquiv_succ, incidenceTailPivotEquiv_zero]

@[simp] theorem incidencePivotEquiv_tail (p : Fin (n + 1)) (j : Fin n) :
    incidencePivotEquiv p j.succ.succ = (p.succAbove j).succ := by
  simp only [incidencePivotEquiv_succ, incidenceTailPivotEquiv_succ]

/-- The original matrix with an arbitrary polar pivot put into position one. -/
def incidencePivotMatrix (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (p : Fin (n + 1)) : Matrix (Fin (n + 2)) (Fin (n + 2)) K :=
  A.submatrix (incidencePivotEquiv p) (incidencePivotEquiv p)

omit [Field K] in
/-- The coordinate permutation preserves symmetry. -/
theorem incidencePivotMatrix_isSymm
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (hA : A.IsSymm)
    (p : Fin (n + 1)) : (incidencePivotMatrix A p).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact hA.apply (incidencePivotEquiv p i) (incidencePivotEquiv p j)

/-- Explicit coefficients after eliminating an arbitrary polar pivot,
with the uneliminated coordinates in `succAbove` order. -/
theorem incidencePivotRestrictedMatrix_apply
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (p : Fin (n + 1)) (i j : Fin n) :
    incidenceRestrictedMatrix (incidencePivotMatrix A p) i j =
      A (p.succAbove i).succ (p.succAbove j).succ -
      A (p.succAbove i).succ p.succ * A (p.succAbove j).succ 0 / A p.succ 0 -
      A (p.succAbove i).succ 0 / A p.succ 0 * A p.succ (p.succAbove j).succ +
      A (p.succAbove i).succ 0 * A p.succ p.succ * A (p.succAbove j).succ 0 /
        (A p.succ 0)^2 := by
  rw [incidenceRestrictedMatrix_apply]
  simp only [incidencePivotMatrix, Matrix.submatrix_apply, incidencePivotEquiv_tail,
    incidencePivotEquiv_one, incidencePivotEquiv_zero]

/-- The rank-two obstruction transports back along the actual coordinate
permutation, so the selected pivot need not originally be position one. -/
theorem incidencePivotRestrictedMatrix_ne_zero_of_adjugate
    (A : Matrix (Fin 5) (Fin 5) K) (hA : A.IsSymm) (hbase : A 0 0 = 0)
    (p : Fin 4) (hpivot : A p.succ 0 ≠ 0) (hadj : A.adjugate ≠ 0) :
    incidenceRestrictedMatrix (incidencePivotMatrix A p) ≠ 0 := by
  let e := incidencePivotEquiv p
  have hs := incidencePivotMatrix_isSymm A hA p
  have h0 : incidencePivotMatrix A p 0 0 = 0 := by
    simpa [incidencePivotMatrix] using hbase
  have h1 : incidencePivotMatrix A p 1 0 ≠ 0 := by
    simpa [incidencePivotMatrix] using hpivot
  intro hB
  obtain ⟨U, V, hUV⟩ :=
    incidenceRestrictedMatrix_eq_zero_factorization _ hs h0 h1 hB
  have hback : A = U.submatrix e.symm id * V.submatrix id e.symm := by
    ext i j
    have h := congrArg (fun B : Matrix (Fin 5) (Fin 5) K => B (e.symm i) (e.symm j)) hUV
    change A (e (e.symm i)) (e (e.symm j)) = (U * V) (e.symm i) (e.symm j) at h
    simpa only [e.apply_symm_apply, Matrix.mul_apply, Matrix.submatrix_apply,
      id_eq] using h
  apply hadj
  rw [hback]
  exact adjugate_eq_zero_of_factor_through_two _ _

/-- Over an infinite field, every fixed standard chart retains a nonzero
homogeneous polynomial. Nonvanishing is derived by evaluating `F * X p`. -/
theorem dehomogenizeAt_ne_zero_of_homogeneous [Infinite K]
    (p : Fin (n + 1)) (F : MvPolynomial (Fin (n + 1)) K)
    (d : ℕ) (hF : F.IsHomogeneous d) (hne : F ≠ 0) :
    dehomogenizeAt p F ≠ 0 := by
  have hprod : F * MvPolynomial.X p ≠ 0 := mul_ne_zero hne (MvPolynomial.X_ne_zero p)
  obtain ⟨y, hy⟩ := exists_eval_ne_zero_of_polynomial_ne_zero _ hprod
  have hy' : MvPolynomial.eval y F * y p ≠ 0 := by
    simpa only [map_mul, MvPolynomial.eval_X] using hy
  have hf : MvPolynomial.eval y F ≠ 0 := (mul_ne_zero_iff.mp hy').1
  have hp : y p ≠ 0 := (mul_ne_zero_iff.mp hy').2
  intro hz
  have h := eval_dehomogenizeAt_ne_zero p y hp F d hF hf
  rw [hz, map_zero] at h
  exact h rfl

/-- Every projective standard chart of a nonzero symmetric ternary form
has a nonzero actual two-variable defining polynomial. -/
theorem incidenceRestrictedQuadratic_dehomogenize_ne_zero [Infinite K]
    (h2 : (2 : K) ≠ 0) (A : Matrix (Fin 5) (Fin 5) K)
    (hA : A.IsSymm) (hB : incidenceRestrictedMatrix A ≠ 0) (p : Fin 3) :
    dehomogenizeAt p (matrixQuadraticPolynomial (incidenceRestrictedMatrix A)) ≠ 0 :=
  dehomogenizeAt_ne_zero_of_homogeneous p _ 2 (matrixQuadraticPolynomial_homogeneous _)
    (incidenceRestrictedQuadratic_ne_zero h2 A hA hB)

/-- Nonzero actual adjugate ensures that eliminating any nonzero polar
coefficient and dehomogenizing any remaining coordinate leaves a nonzero
actual two-variable conic equation. -/
theorem incidencePivotRestrictedQuadratic_dehomogenize_ne_zero [Infinite K]
    (h2 : (2 : K) ≠ 0) (A : Matrix (Fin 5) (Fin 5) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0)
    (p : Fin 4) (hpivot : A p.succ 0 ≠ 0) (hadj : A.adjugate ≠ 0) (q : Fin 3) :
    dehomogenizeAt q
      (matrixQuadraticPolynomial (incidenceRestrictedMatrix (incidencePivotMatrix A p))) ≠ 0 :=
  incidenceRestrictedQuadratic_dehomogenize_ne_zero h2 _
    (incidencePivotMatrix_isSymm A hA p)
    (incidencePivotRestrictedMatrix_ne_zero_of_adjugate A hA hbase p hpivot hadj) q

/-- In every chart distinct from the eliminated polar coordinate, there
is a vector satisfying the polar equation on which the residual quadratic
does not vanish. This witnesses a nonzero affine conic equation directly. -/
theorem exists_polar_zero_quadratic_ne_zero_of_adjugate [Infinite K]
    (h2 : (2 : K) ≠ 0) (A : Matrix (Fin 5) (Fin 5) K)
    (hA : A.IsSymm) (hbase : A 0 0 = 0)
    (r p : Fin 4) (hpr : p ≠ r) (hr : A r.succ 0 ≠ 0) (hadj : A.adjugate ≠ 0) :
    ∃ y : Fin 4 → K, y p ≠ 0 ∧ (∑ i, A i.succ 0 * y i) = 0 ∧
      MvPolynomial.eval y (matrixQuadraticPolynomial (A.submatrix Fin.succ Fin.succ)) ≠ 0 := by
  obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq hpr
  let e := incidencePivotEquiv r
  let A' := incidencePivotMatrix A r
  let B := incidenceRestrictedMatrix A'
  let H := matrixQuadraticPolynomial B
  have hs : A'.IsSymm := incidencePivotMatrix_isSymm A hA r
  have hr' : A' 1 0 ≠ 0 := by simpa [A', incidencePivotMatrix] using hr
  have hH : H ≠ 0 := incidenceRestrictedQuadratic_ne_zero h2 A' hs
    (incidencePivotRestrictedMatrix_ne_zero_of_adjugate A hA hbase r hr hadj)
  obtain ⟨z, hz⟩ := exists_eval_ne_zero_of_polynomial_ne_zero (H * MvPolynomial.X q)
    (mul_ne_zero hH (MvPolynomial.X_ne_zero q))
  have hz' : MvPolynomial.eval z H ≠ 0 ∧ z q ≠ 0 := by
    simpa only [map_mul, MvPolynomial.eval_X, mul_ne_zero_iff] using hz
  let v := (incidenceEliminationMatrix A').mulVec z
  let x := v ∘ e.symm
  let y : Fin 4 → K := fun i => x i.succ
  have he0 : e.symm 0 = 0 := e.symm_apply_eq.mpr (incidencePivotEquiv_zero r).symm
  have hx0 : x 0 = 0 := by simp [x, he0, v]
  have hxcomp : x ∘ e = v := by funext i; simp [x]
  have hmul : A'.mulVec v = (A.mulVec x) ∘ e := by
    exact Matrix.submatrix_mulVec_equiv A v e e
  have hp : y p ≠ 0 := by
    have heq : e q.succ.succ = p.succ := by
      simp [e, hq]
    have hyp : y p = z q := by
      change v (e.symm p.succ) = z q
      rw [← heq, e.symm_apply_apply]
      exact incidenceEliminationMatrix_mulVec_tail A' z q
    rw [hyp]
    exact hz'.2
  have hpolar : A.mulVec x 0 = 0 := by
    have h := incidenceEliminationMatrix_polar_zero A' hs hr' z
    change A'.mulVec v 0 = 0 at h
    rw [hmul] at h
    simpa [e] using h
  have hpolary : (∑ i, A i.succ 0 * y i) = 0 := by
    change (∑ i, A 0 i * x i) = 0 at hpolar
    rw [Fin.sum_univ_succ] at hpolar
    simp only [hx0, mul_zero, zero_add] at hpolar
    convert hpolar using 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun a => a * y i) (hA.apply 0 i.succ)
  have hquad : dotProduct v (A'.mulVec v) = dotProduct x (A.mulVec x) := by
    rw [hmul, ← hxcomp]
    exact comp_equiv_dotProduct_comp_equiv x (A.mulVec x) e
  have hHval : MvPolynomial.eval z H = dotProduct x (A.mulVec x) := by
    change MvPolynomial.eval₂ (RingHom.id K) z (matrixQuadraticPolynomial B) = _
    rw [matrixQuadraticPolynomial_eval₂]
    change dotProduct z (B.mulVec z) = _
    rw [incidenceRestrictedMatrix_quadratic]
    exact hquad
  have htail : MvPolynomial.eval y
      (matrixQuadraticPolynomial (A.submatrix Fin.succ Fin.succ)) =
        dotProduct x (A.mulVec x) := by
    change MvPolynomial.eval₂ (RingHom.id K) y
      (matrixQuadraticPolynomial (A.submatrix Fin.succ Fin.succ)) = _
    rw [matrixQuadraticPolynomial_eval₂]
    change (∑ i : Fin 4, y i * ∑ j : Fin 4, A i.succ j.succ * y j) =
      ∑ i : Fin 5, x i * ∑ j : Fin 5, A i j * x j
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [hx0, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [hx0, mul_zero, zero_add]
    rfl
  refine ⟨y, hp, hpolary, ?_⟩
  rw [htail, ← hHval]
  exact hz'.1

end EvenQuinticConic.Incidence
