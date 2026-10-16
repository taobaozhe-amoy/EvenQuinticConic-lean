import EvenQuinticConic.IncidenceMinorFromDeterminant
import EvenQuinticConic.LinearCoordinateNormalization
import EvenQuinticConic.NetCoordinateChange
import EvenQuinticConic.IncidenceAffineChart

/-!
# A nonzero incidence minor from a symmetric net and its determinant Jacobian

The linear and quadratic rows are extracted from the actual coefficient
matrices at the common first-coordinate point.  The determinant Jacobian
condition supplies their linear independence and an actual coordinate
normalization.  Vanishing of the original minors would then factor the
original generic quadratic form, contradicting its actual determinant.

The conclusions are a nonzero polynomial minor, an actual nonzero evaluation
point, and a nonempty localized affine cone incidence scheme, including
after a constructed invertible normalization of an arbitrary nonzero common
point. Scheme smoothness-to-Jacobian comparison, existence
of a common point, and global birationality remain separate geometric steps.
-/

noncomputable section
set_option maxRecDepth 4096

namespace EvenQuinticConic.Incidence
open MvPolynomial

variable {K : Type*} [Field K]

/-- The actual polar linear row at the first coordinate point. -/
def netLinearRow (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (i : Fin 3) :
    MvPolynomial (Fin 4) K :=
  coefficientLinearPolynomial (fun j => M i j.succ 0)

/-- The actual quadratic row obtained by restricting to the last four coordinates. -/
def netQuadraticRow (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (i : Fin 3) :
    MvPolynomial (Fin 4) K :=
  matrixQuadraticPolynomial (fun j k : Fin 4 => M i j.succ k.succ)

/-- The actual two-column minor of the polar and quadratic rows. -/
def netIncidenceMinor (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (i j : Fin 3) :
    MvPolynomial (Fin 4) K :=
  netLinearRow M i * netQuadraticRow M j - netLinearRow M j * netQuadraticRow M i

theorem genericNetMatrix_eq_linearMatrixNet
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    genericNetMatrix M = linearMatrixNet M := by
  funext i j
  simp only [genericNetMatrix, linearMatrixNet, mul_comm]

/-- The explicit field-valued Jacobian condition already excludes an
identically zero determinant polynomial. -/
theorem linearMatrixNet_det_ne_zero_of_jacobian
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    (linearMatrixNet M).det ≠ 0 := by
  intro hz
  have ht : (Pi.single 0 1 : Fin 3 → K) ≠ 0 := by
    intro heq
    have := congrFun heq 0
    simp at this
  obtain ⟨i, hi⟩ := hsmooth (Pi.single 0 1) ht (by simp [hz])
  simp [hz] at hi

/-- This is the polynomial identity obtained by expanding the actual
symmetric matrix at its common first-coordinate zero. -/
theorem matrixQuadraticPolynomial_basepoint_decomposition
    (A : Matrix (Fin 5) (Fin 5) K) (hA : A.IsSymm) (hbase : A 0 0 = 0) :
    matrixQuadraticPolynomial A =
      2 * X 0 * rename Fin.succ (coefficientLinearPolynomial (fun j : Fin 4 => A j.succ 0)) +
      rename Fin.succ (matrixQuadraticPolynomial (fun j k : Fin 4 => A j.succ k.succ)) := by
  simp only [matrixQuadraticPolynomial, coefficientLinearPolynomial,
    map_sum, map_mul, rename_C, rename_X, Finset.mul_sum]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp only [hbase, C_0, zero_mul, zero_add]
  have htail (i : Fin 4) :
      (∑ j : Fin 5, C (A i.succ j) * X i.succ * X j) =
      C (A i.succ 0) * X i.succ * X 0 +
      ∑ j : Fin 4, C (A i.succ j.succ) * X i.succ * X j.succ :=
    Fin.sum_univ_succ _
  simp_rw [htail]
  rw [Finset.sum_add_distrib]
  have hcross :
      (∑ j : Fin 4, C (A 0 j.succ) * X 0 * X j.succ) +
      (∑ j : Fin 4, C (A j.succ 0) * X j.succ * X 0) =
      ∑ j : Fin 4, 2 * X 0 * (C (A j.succ 0) * X j.succ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hA.apply j.succ 0]
    ring
  rw [← add_assoc, hcross]


/-- Vanishing original minors, transported through the constructed
coordinate equivalence, produces a common factor of the original row. -/
theorem net_common_factor_of_minors_zero
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm) (hbase : ∀ i, M i 0 0 = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0)
    (hminor : ∀ i j, netIncidenceMinor M i j = 0) :
    ∃ h : MvPolynomial (Fin 4) K, ∀ i, netQuadraticRow M i = netLinearRow M i * h := by
  obtain ⟨e, he, _, _⟩ :=
    linearMatrixNet_exists_normalizing_polar_coordinates M hM hbase hsmooth
  have htrans (i j : Fin 3) : coordinateMinor (fun k => e (netQuadraticRow M k)) i j = 0 := by
    have hh := congrArg e (hminor i j)
    simpa only [netIncidenceMinor, map_sub, map_mul, map_zero, netLinearRow, he,
      coordinateMinor, coordinateLinear] using hh
  obtain ⟨h, hh⟩ := common_factor_of_coordinateMinors_zero
    (fun i => e (netQuadraticRow M i)) htrans
  refine ⟨e.symm h, fun i => ?_⟩
  apply e.injective
  rw [map_mul, AlgEquiv.apply_symm_apply]
  simpa only [netLinearRow, he, coordinateLinear] using hh i

/-- The coefficient vector of the actual generic polar linear form. -/
def netGenericPolarCoefficients (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    Fin 5 → MvPolynomial (Fin 3) K :=
  Fin.cases 0 (fun j => ∑ i, X i * C (M i j.succ 0))

theorem netGenericPolarCoefficients_linearPolynomial
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    linearPolynomial (netGenericPolarCoefficients M) =
      ∑ i, C (X i) * liftedQuadraticRow (netLinearRow M i) := by
  rw [linearPolynomial, Fin.sum_univ_succ]
  simp only [netGenericPolarCoefficients, Fin.cases_zero, Fin.cases_succ, C_0, zero_mul,
    zero_add, liftedQuadraticRow, netLinearRow, coefficientLinearPolynomial,
    map_sum, map_mul, rename_C, rename_X, MvPolynomial.map_C, MvPolynomial.map_X,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A common factor in the rows extracted from the original matrices forces
the determinant of the original generic net to vanish. No matrix coordinate
change or congruence hypothesis is required. -/
theorem net_det_eq_zero_of_common_factor
    (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm) (hbase : ∀ i, M i 0 0 = 0)
    (h : MvPolynomial (Fin 4) K)
    (hh : ∀ i, netQuadraticRow M i = netLinearRow M i * h) :
    (linearMatrixNet M).det = 0 := by
  rw [← genericNetMatrix_eq_linearMatrixNet]
  refine det_eq_zero_of_matrixQuadraticPolynomial_factor
    (R := MvPolynomial (Fin 3) K) ?_ (genericNetMatrix M)
    (genericNetMatrix_isSymm M hM) (netGenericPolarCoefficients M)
    (2 * X 0 + liftedQuadraticRow h) ?_
  · intro hz
    apply h2
    have hzK := congrArg (constantCoeff (σ := Fin 3) (R := K)) hz
    simpa only [map_ofNat, map_zero] using hzK
  · rw [matrixQuadraticPolynomial_genericNetMatrix,
      netGenericPolarCoefficients_linearPolynomial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [matrixQuadraticPolynomial_basepoint_decomposition (M i) (hM i) (hbase i)]
    change C (X i) * map C (2 * X 0 * rename Fin.succ (netLinearRow M i) +
      rename Fin.succ (netQuadraticRow M i)) = _
    rw [hh i]
    simp only [liftedQuadraticRow, map_add, map_mul, map_ofNat,
      MvPolynomial.map_X]
    ring

/-- From the actual Jacobian condition and common coordinate point, the
actual polar/quadratic rows have a nonzero polynomial minor. -/
theorem exists_netIncidenceMinor_ne_zero_of_jacobian
    (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm) (hbase : ∀ i, M i 0 0 = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ i j, netIncidenceMinor M i j ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  obtain ⟨h, hh⟩ := net_common_factor_of_minors_zero M hM hbase hsmooth hzero
  exact linearMatrixNet_det_ne_zero_of_jacobian M hsmooth
    (net_det_eq_zero_of_common_factor h2 M hM hbase h hh)

/-- Over an infinite field the minor is nonzero at an actual nonzero vector,
which therefore represents a projective parameter point. -/
theorem exists_projective_netIncidenceMinor_ne_zero_of_jacobian
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm) (hbase : ∀ i, M i 0 0 = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ (i j : Fin 3) (y : Fin 4 → K), i ≠ j ∧ y ≠ 0 ∧ eval y (netIncidenceMinor M i j) ≠ 0 := by
  obtain ⟨i, j, hij⟩ := exists_netIncidenceMinor_ne_zero_of_jacobian h2 M hM hbase hsmooth
  obtain ⟨y, hy⟩ := exists_eval_ne_zero_of_polynomial_ne_zero _ hij
  refine ⟨i, j, y, ?_, ?_, hy⟩
  · intro heq
    subst j
    simp [netIncidenceMinor] at hij
  · intro hz
    subst y
    simp [netIncidenceMinor, netLinearRow, coefficientLinearPolynomial] at hy

/-- Starting at an arbitrary nonzero common isotropic vector, an actual
invertible coordinate change yields an actual nonempty incidence-minor
chart. All matrix and polynomial normalizations are constructed internally. -/
theorem exists_projective_netIncidenceMinor_after_common_point_normalization
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ (i j : Fin 3) (y : Fin 4 → K), i ≠ j ∧ y ≠ 0 ∧
        eval y (netIncidenceMinor (matrixNetCongruence M B) i j) ≠ 0 := by
  obtain ⟨B, hB, hcol, hsym, hbase, hgrad, _⟩ :=
    exists_normalized_matrixNet_common_point M hM P hP hisotropic hsmooth
  exact ⟨B, hB, hcol,
    exists_projective_netIncidenceMinor_ne_zero_of_jacobian h2
      (matrixNetCongruence M B) hsym hbase hgrad⟩

/-- The polynomial linear row with the selected three columns. -/
def netSelectedLinearPolynomialRow (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (i j k : Fin 3) : Vec3 (MvPolynomial (Fin 4) K) :=
  ⟨netLinearRow M i, netLinearRow M j, netLinearRow M k⟩

/-- The polynomial quadratic row with the same selected columns. -/
def netSelectedQuadraticPolynomialRow (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (i j k : Fin 3) : Vec3 (MvPolynomial (Fin 4) K) :=
  ⟨netQuadraticRow M i, netQuadraticRow M j, netQuadraticRow M k⟩

/-- An actual affine incidence scheme over the minor principal open in
four-dimensional affine space, with the third selected parameter set to one.
This is a cone chart; its identification with a global projective incidence
open is not asserted by this definition. -/
def netAffineConeIncidenceChart (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (i j k : Fin 3) : AlgebraicGeometry.Scheme :=
  let a := netSelectedLinearPolynomialRow M i j k
  let b := netSelectedQuadraticPolynomialRow M i j k
  AlgebraicGeometry.Spec (CommRingCat.of
    (AffineIncidenceAlgebra (localizedRow a b a) (localizedRow a b b)))

/-- The nonzero actual minor supplies a point of the actual localized
incidence scheme, via the previously constructed scheme isomorphism. -/
theorem netAffineConeIncidenceChart_nonempty_of_eval
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (i j k : Fin 3) (y : Fin 4 → K)
    (hy : eval y (netIncidenceMinor M i j) ≠ 0) :
    Nonempty (netAffineConeIncidenceChart M i j k) := by
  unfold netAffineConeIncidenceChart
  apply localizedIncidenceScheme_nonempty_of_eval (eval y)
  simpa only [cross, netSelectedLinearPolynomialRow, netSelectedQuadraticPolynomialRow,
    netIncidenceMinor] using hy

/-- From an arbitrary nonzero common point and the actual determinant
Jacobian condition, some actual affine cone incidence chart is nonempty.
All three selected columns are distinct. This theorem does not identify the
chart with an open of the desired global projective incidence scheme. -/
theorem exists_nonempty_affineConeIncidenceChart_of_common_point
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        Nonempty (netAffineConeIncidenceChart (matrixNetCongruence M B) i j k) := by
  obtain ⟨B, hB, hcol, i, j, y, hij, _, hy⟩ :=
    exists_projective_netIncidenceMinor_after_common_point_normalization
      h2 M hM P hP hisotropic hsmooth
  have hk : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  obtain ⟨k, hik, hjk⟩ := hk
  exact ⟨B, hB, hcol, i, j, k, hij, hik, hjk,
    netAffineConeIncidenceChart_nonempty_of_eval (matrixNetCongruence M B) i j k y hy⟩

end EvenQuinticConic.Incidence
