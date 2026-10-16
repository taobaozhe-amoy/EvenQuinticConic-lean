import EvenQuinticConic.Incidence
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases

/-!
# Nonzero minors for the normalized incidence equations

For the normalized row of independent linear forms `(X₀, X₁, X₂)`,
vanishing of all minors with a row of quadratic forms forces the quadratic
forms to have one common linear factor: `rᵢ = Xᵢ * h`. Consequently, absence
of this factorization gives a genuinely nonempty minor chart over an infinite
field. The factorization is derived coefficientwise, not assumed.

These are polynomial and set-theoretic results. They do not establish the
change of coordinates from arbitrary independent linear forms, the geometric
exclusion of the factorization from discriminant smoothness, or birationality
of schemes.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open MvPolynomial

section VariableDivisibility

variable {R : Type*} [CommSemiring R] {σ : Type*}

/-- Distinct coordinate variables have the required cancellation property for
divisibility. This coefficientwise proof even allows zero divisors in `R`. -/
theorem X_dvd_of_distinct_cross_eq {i j : σ} (hij : i ≠ j)
    (p q : MvPolynomial σ R) (heq : X j * p = X i * q) : X i ∣ p := by
  classical
  rw [X_dvd_iff_modMonomial_eq_zero]
  ext d
  rw [coeff_zero]
  by_cases hd : Finsupp.single i 1 ≤ d
  · exact coeff_modMonomial_of_le p hd
  · rw [coeff_modMonomial_of_not_le p hd]
    have hdi : d i = 0 := by
      rw [Finsupp.single_le_iff] at hd
      omega
    have hm := congrArg (coeff (Finsupp.single j 1 + d)) heq
    rw [coeff_X_mul] at hm
    rw [coeff_X_mul'] at hm
    simpa [Finsupp.mem_support_iff, Finsupp.single_apply, hij, Ne.symm hij, hdi] using hm

/-- Dividing a quadratic homogeneous polynomial by a coordinate variable
produces a linear homogeneous polynomial, including when the result is zero. -/
theorem isHomogeneous_one_of_X_mul (i : σ) (h : MvPolynomial σ R)
    (hh : (X i * h).IsHomogeneous 2) : h.IsHomogeneous 1 := by
  intro d hd
  have hcoeff : coeff (Finsupp.single i 1 + d) (X i * h) ≠ 0 := by
    simpa only [coeff_X_mul] using hd
  have hdeg : (Finsupp.single i 1 + d).degree = 2 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hh hcoeff
  rw [Finsupp.degree_add, Finsupp.degree_single] at hdeg
  change Finsupp.weight (fun _ : σ => (1 : ℕ)) d = 1
  rw [← Finsupp.degree_eq_weight_one]
  omega

end VariableDivisibility

section NormalizedRow

variable {K : Type*} [Field K]

/-- The coordinate inclusion for the first three variables of four. -/
def coordinateLinear (i : Fin 3) : MvPolynomial (Fin 4) K := X i.castSucc

/-- A two-column minor of the linear row and the row `r`. -/
def coordinateMinor (r : Fin 3 → MvPolynomial (Fin 4) K) (i j : Fin 3) :
    MvPolynomial (Fin 4) K := coordinateLinear i * r j - coordinateLinear j * r i

/-- The polynomial factorization forced by vanishing minors does not require
any homogeneity assumption. -/
theorem common_factor_of_coordinateMinors_zero
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hminor : ∀ i j, coordinateMinor r i j = 0) :
    ∃ h : MvPolynomial (Fin 4) K, ∀ i, r i = coordinateLinear i * h := by
  have hcross (i j : Fin 3) : coordinateLinear i * r j = coordinateLinear j * r i :=
    sub_eq_zero.mp (hminor i j)
  have hdiv : coordinateLinear (0 : Fin 3) ∣ r 0 :=
    X_dvd_of_distinct_cross_eq (by decide :
      (0 : Fin 3).castSucc ≠ (1 : Fin 3).castSucc) (r 0) (r 1) (hcross 1 0)
  obtain ⟨h, hh⟩ := hdiv
  refine ⟨h, fun i => ?_⟩
  apply mul_left_cancel₀ (show coordinateLinear (0 : Fin 3) ≠ (0 : MvPolynomial (Fin 4) K)
    from X_ne_zero _)
  calc
    coordinateLinear 0 * r i = coordinateLinear i * r 0 := hcross 0 i
    _ = coordinateLinear i * (coordinateLinear 0 * h) := by rw [hh]
    _ = coordinateLinear 0 * (coordinateLinear i * h) := by ring

/-- For quadrics the common polynomial supplied by the minors is homogeneous
of degree one. This establishes the linear factor rather than postulating it. -/
theorem common_linear_factor_of_coordinateMinors_zero
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hminor : ∀ i j, coordinateMinor r i j = 0) :
    ∃ h : MvPolynomial (Fin 4) K, h.IsHomogeneous 1 ∧
      ∀ i, r i = coordinateLinear i * h := by
  obtain ⟨h, hh⟩ := common_factor_of_coordinateMinors_zero r hminor
  refine ⟨h, ?_, hh⟩
  apply isHomogeneous_one_of_X_mul (0 : Fin 3).castSucc
  change (coordinateLinear (0 : Fin 3) * h).IsHomogeneous 2
  rw [← hh 0]
  exact hr 0

/-- The quadratic pencil written after putting its common zero at the first
coordinate point. Here `z` stands for the distinguished coordinate; allowing
an arbitrary polynomial makes the identity stable under substitution. -/
def normalizedPencil (r : Fin 3 → MvPolynomial (Fin 4) K)
    (t : Fin 3 → K) (z : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  ∑ i, C (t i) * (2 * z * coordinateLinear i + r i)

/-- A common linear factor of the quadratic row factors every member of the
pencil into the corresponding two linear expressions. -/
theorem normalizedPencil_factorization
    (r : Fin 3 → MvPolynomial (Fin 4) K) (h : MvPolynomial (Fin 4) K)
    (hh : ∀ i, r i = coordinateLinear i * h)
    (t : Fin 3 → K) (z : MvPolynomial (Fin 4) K) :
    normalizedPencil r t z =
      (∑ i, C (t i) * coordinateLinear i) * (2 * z + h) := by
  rw [normalizedPencil, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hh i]
  ring

/-- The pencil factorization follows from the minors, with a homogeneous
linear factor actually constructed from the quadrics. -/
theorem normalizedPencil_factorization_of_coordinateMinors_zero
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hminor : ∀ i j, coordinateMinor r i j = 0) :
    ∃ h : MvPolynomial (Fin 4) K, h.IsHomogeneous 1 ∧
      ∀ (t : Fin 3 → K) (z : MvPolynomial (Fin 4) K),
        normalizedPencil r t z =
          (∑ i, C (t i) * coordinateLinear i) * (2 * z + h) := by
  obtain ⟨h, hhom, hh⟩ := common_linear_factor_of_coordinateMinors_zero r hr hminor
  exact ⟨h, hhom, normalizedPencil_factorization r h hh⟩

/-- If the common linear factorization is excluded, at least one minor is a
nonzero polynomial. -/
theorem exists_coordinateMinor_ne_zero
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hfactor : ¬ ∃ h : MvPolynomial (Fin 4) K, h.IsHomogeneous 1 ∧
      ∀ i, r i = coordinateLinear i * h) :
    ∃ i j, coordinateMinor r i j ≠ 0 := by
  by_contra h
  push_neg at h
  exact hfactor (common_linear_factor_of_coordinateMinors_zero r hr h)

variable [Infinite K]

/-- A nonzero multivariate polynomial over an infinite field takes a nonzero
value at some field-valued point. -/
theorem exists_eval_ne_zero_of_polynomial_ne_zero {σ : Type*}
    (p : MvPolynomial σ K) (hp : p ≠ 0) : ∃ y : σ → K, eval y p ≠ 0 := by
  by_contra h
  push_neg at h
  apply hp
  exact MvPolynomial.funext (fun y => by simpa using h y)

/-- The nonzero minor is nonzero at an actual affine parameter point. -/
theorem exists_coordinateMinor_eval_ne_zero
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hfactor : ¬ ∃ h : MvPolynomial (Fin 4) K, h.IsHomogeneous 1 ∧
      ∀ i, r i = coordinateLinear i * h) :
    ∃ (i j : Fin 3) (y : Fin 4 → K), eval y (coordinateMinor r i j) ≠ 0 := by
  obtain ⟨i, j, hij⟩ := exists_coordinateMinor_ne_zero r hr hfactor
  obtain ⟨y, hy⟩ := exists_eval_ne_zero_of_polynomial_ne_zero _ hij
  exact ⟨i, j, y, hy⟩

/-- The witnessing indices are distinct, and the parameter is a nonzero
vector, so it is a valid representative of a projective parameter point. -/
theorem exists_projective_coordinateMinor_ne_zero
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hfactor : ¬ ∃ h : MvPolynomial (Fin 4) K, h.IsHomogeneous 1 ∧
      ∀ i, r i = coordinateLinear i * h) :
    ∃ (i j : Fin 3) (y : Fin 4 → K),
      i ≠ j ∧ y ≠ 0 ∧ eval y (coordinateMinor r i j) ≠ 0 := by
  obtain ⟨i, j, y, hy⟩ := exists_coordinateMinor_eval_ne_zero r hr hfactor
  refine ⟨i, j, y, ?_, ?_, hy⟩
  · intro hij
    subst j
    simp [coordinateMinor] at hy
  · intro hyzero
    subst y
    simp [coordinateMinor, coordinateLinear] at hy

/-- The linear row with the two selected columns placed first. For an actual
reordering of three columns, take `k` to be the remaining index. -/
def selectedCoordinateRow (i j k : Fin 3) (y : Fin 4 → K) : Vec3 K :=
  ⟨y i.castSucc, y j.castSucc, y k.castSucc⟩

/-- The quadratic row in the same column order as `selectedCoordinateRow`. -/
def selectedQuadraticRow (r : Fin 3 → MvPolynomial (Fin 4) K)
    (i j k : Fin 3) (y : Fin 4 → K) : Vec3 K :=
  ⟨eval y (r i), eval y (r j), eval y (r k)⟩

omit [Infinite K] in
/-- Polynomial minors agree with the minor used by the normalized incidence
chart from `Incidence.lean`. -/
theorem selectedRows_cross_z
    (r : Fin 3 → MvPolynomial (Fin 4) K) (i j k : Fin 3) (y : Fin 4 → K) :
    (cross (selectedCoordinateRow i j k y) (selectedQuadraticRow r i j k y)).z =
      eval y (coordinateMinor r i j) := by
  simp [cross, selectedCoordinateRow, selectedQuadraticRow,
    coordinateMinor, coordinateLinear]

/-- The normalized coordinate hypotheses provide a nonempty minor chart,
rather than assuming a point of that chart. -/
theorem exists_nonempty_selectedMinorChart
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hfactor : ¬ ∃ h : MvPolynomial (Fin 4) K, h.IsHomogeneous 1 ∧
      ∀ i, r i = coordinateLinear i * h) :
    ∃ i j : Fin 3, i ≠ j ∧ ∀ k : Fin 3,
      Nonempty (MinorChart (selectedCoordinateRow i j k) (selectedQuadraticRow r i j k)) := by
  obtain ⟨i, j, y, hij, _, hy⟩ := exists_projective_coordinateMinor_ne_zero r hr hfactor
  refine ⟨i, j, hij, fun k => ⟨⟨y, ?_⟩⟩⟩
  rw [selectedRows_cross_z]
  exact hy

/-- The explicit incidence-chart equivalence now yields an actual point of
an incidence chart under the same polynomial hypotheses. -/
theorem exists_nonempty_selectedIncidenceChart
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hfactor : ¬ ∃ h : MvPolynomial (Fin 4) K, h.IsHomogeneous 1 ∧
      ∀ i, r i = coordinateLinear i * h) :
    ∃ i j : Fin 3, i ≠ j ∧ ∀ k : Fin 3,
      Nonempty (IncidenceChart (selectedCoordinateRow i j k) (selectedQuadraticRow r i j k)) := by
  obtain ⟨i, j, hij, hchart⟩ := exists_nonempty_selectedMinorChart r hr hfactor
  refine ⟨i, j, hij, fun k => ?_⟩
  obtain ⟨p⟩ := hchart k
  exact ⟨(incidenceChartEquiv _ _).symm p⟩

/-- The selected chart can use three distinct indices. Thus each of the
original three columns occurs exactly once. -/
theorem exists_nonempty_reorderedIncidenceChart
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hfactor : ¬ ∃ h : MvPolynomial (Fin 4) K, h.IsHomogeneous 1 ∧
      ∀ i, r i = coordinateLinear i * h) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      Nonempty (IncidenceChart (selectedCoordinateRow i j k) (selectedQuadraticRow r i j k)) := by
  obtain ⟨i, j, hij, hchart⟩ := exists_nonempty_selectedIncidenceChart r hr hfactor
  have hk : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  obtain ⟨k, hik, hjk⟩ := hk
  exact ⟨i, j, k, hij, hik, hjk, hchart k⟩

end NormalizedRow

end EvenQuinticConic.Incidence
