import EvenQuinticConic.RealCofactor
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.LinearCombination

/-!
# The actual factors of a rank-two ternary conic

On the chart where the (0,0) cofactor is nonzero, the negative cofactor is
a square exactly when the ternary quadratic polynomial is a product of two
independent homogeneous linear polynomials. This identifies the field-valued
cofactor-root criterion with actual line factors. It does not construct a
global relative Fano scheme or glue the local comparisons.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial Matrix

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- A homogeneous linear polynomial, with its three actual coefficients. -/
def ternaryLinearPolynomial (l : Fin 3 → K) : MvPolynomial (Fin 3) K :=
  C (l 0) * X 0 + C (l 1) * X 1 + C (l 2) * X 2

/-- The quadratic polynomial of a symmetric ternary matrix. -/
def ternaryQuadraticPolynomial (M : Matrix (Fin 3) (Fin 3) K) :
    MvPolynomial (Fin 3) K :=
  C (M 0 0) * X 0 ^ 2 + C (M 1 1) * X 1 ^ 2 + C (M 2 2) * X 2 ^ 2 +
    C (2 * M 0 1) * X 0 * X 1 + C (2 * M 0 2) * X 0 * X 2 +
    C (2 * M 1 2) * X 1 * X 2

omit [NeZero (2 : K)] in
/-- The displayed linear factors really are homogeneous of degree one. -/
theorem ternaryLinearPolynomial_isHomogeneous (l : Fin 3 → K) :
    (ternaryLinearPolynomial l).IsHomogeneous 1 :=
  ((isHomogeneous_C_mul_X (l 0) 0).add
    (isHomogeneous_C_mul_X (l 1) 1)).add (isHomogeneous_C_mul_X (l 2) 2)

omit [NeZero (2 : K)] in
/-- The polynomial is the actual matrix quadratic form, with both off-diagonal
entries included. -/
theorem eval_ternaryQuadraticPolynomial
    (M : Matrix (Fin 3) (Fin 3) K) (hM : M.IsSymm) (x : Fin 3 → K) :
    eval x (ternaryQuadraticPolynomial M) = dotProduct x (M.mulVec x) := by
  have h10 : M 1 0 = M 0 1 := hM.apply 0 1
  have h20 : M 2 0 = M 0 2 := hM.apply 0 2
  have h21 : M 2 1 = M 1 2 := hM.apply 1 2
  simp [ternaryQuadraticPolynomial, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    h10, h20, h21]
  ring

omit [NeZero (2 : K)] in
private theorem linearPolynomial_independent_of_minor
    (l r : Fin 3 → K) (h : l 1 * r 2 - l 2 * r 1 ≠ 0) :
    LinearIndependent K ![ternaryLinearPolynomial l, ternaryLinearPolynomial r] := by
  rw [LinearIndependent.pair_iff]
  intro s t heq
  have h1 := congrArg (eval ![0, 1, 0]) heq
  have h2 := congrArg (eval ![0, 0, 1]) heq
  simp [ternaryLinearPolynomial] at h1 h2
  have hs : (l 1 * r 2 - l 2 * r 1) * s = 0 := by
    linear_combination r 2 * h1 - r 1 * h2
  have ht : (l 1 * r 2 - l 2 * r 1) * t = 0 := by
    linear_combination l 1 * h2 - l 2 * h1
  exact ⟨(mul_eq_zero.mp hs).resolve_left h, (mul_eq_zero.mp ht).resolve_left h⟩

omit [NeZero (2 : K)] in
private theorem ternary_factor_of_coefficients
    (M : Matrix (Fin 3) (Fin 3) K) (l r : Fin 3 → K)
    (h00 : l 0 * r 0 = M 0 0) (h11 : l 1 * r 1 = M 1 1)
    (h22 : l 2 * r 2 = M 2 2)
    (h01 : l 0 * r 1 + l 1 * r 0 = 2 * M 0 1)
    (h02 : l 0 * r 2 + l 2 * r 0 = 2 * M 0 2)
    (h12 : l 1 * r 2 + l 2 * r 1 = 2 * M 1 2) :
    ternaryQuadraticPolynomial M = ternaryLinearPolynomial l * ternaryLinearPolynomial r := by
  unfold ternaryQuadraticPolynomial ternaryLinearPolynomial
  rw [← h00, ← h11, ← h22, ← h01, ← h02, ← h12]
  simp only [map_mul, map_add]
  ring

/-- Polynomial factorization implies a square signed cofactor. This implication
does not need independence or a rank assumption. -/
theorem ternary_factorization_implies_signed_cofactor_square
    (M : Matrix (Fin 3) (Fin 3) K) (hM : M.IsSymm) (l r : Fin 3 → K)
    (hfactor : ternaryQuadraticPolynomial M =
      ternaryLinearPolynomial l * ternaryLinearPolynomial r) :
    ∃ s : K, s * s = -M.adjugate 0 0 := by
  have ha := congrArg (eval ![0, 1, 0]) hfactor
  have hd := congrArg (eval ![0, 0, 1]) hfactor
  have hb := congrArg (eval ![0, 1, 1]) hfactor
  simp [ternaryQuadraticPolynomial, ternaryLinearPolynomial] at ha hd hb
  have hs : M 2 1 = M 1 2 := hM.apply 1 2
  refine ⟨(l 1 * r 2 - l 2 * r 1) / 2, ?_⟩
  simp only [adjugate_fin_three, of_apply, Matrix.cons_val_zero, hs]
  field_simp
  linear_combination (4 * M 2 2) * ha + (4 * l 1 * r 1) * hd -
    (2 * M 1 2 + l 1 * r 2 + l 2 * r 1) * (hb - ha - hd)

omit [NeZero (2 : K)] in
private theorem ternary_binary_reduction
    (M : Matrix (Fin 3) (Fin 3) K) (hM : M.IsSymm)
    (hdet : M.det = 0) (hpivot : M.adjugate 0 0 ≠ 0) :
    ∃ u v : K,
      M 0 1 = M 1 1 * u + M 1 2 * v ∧
      M 0 2 = M 1 2 * u + M 2 2 * v ∧
      M 0 0 = M 1 1 * u ^ 2 + 2 * M 1 2 * u * v + M 2 2 * v ^ 2 := by
  have h10 : M 1 0 = M 0 1 := hM.apply 0 1
  have h20 : M 2 0 = M 0 2 := hM.apply 0 2
  have h21 : M 2 1 = M 1 2 := hM.apply 1 2
  have hp : M 1 1 * M 2 2 - M 1 2 * M 1 2 ≠ 0 := by
    simpa [adjugate_fin_three, h21] using hpivot
  have hp' : M 1 1 * M 2 2 - M 1 2 ^ 2 ≠ 0 := by simpa [pow_two] using hp
  have hp'' : M 2 2 * M 1 1 - M 1 2 ^ 2 ≠ 0 := by
    simpa only [mul_comm] using hp'
  rw [det_fin_three] at hdet
  simp only [h10, h20, h21] at hdet
  refine ⟨(M 2 2 * M 0 1 - M 1 2 * M 0 2) / (M 1 1 * M 2 2 - M 1 2 * M 1 2),
    (M 1 1 * M 0 2 - M 1 2 * M 0 1) / (M 1 1 * M 2 2 - M 1 2 * M 1 2), ?_, ?_, ?_⟩
  · field_simp [hp, hp', hp'']
    ring
  · field_simp [hp, hp', hp'']
    ring
  · field_simp [hp, hp', hp'']
    linear_combination (M 1 1 * M 2 2 - M 1 2 * M 1 2) * hdet

/-- A square root of the negative cofactor constructs two independent actual
linear factors. Neither existence of factors nor a conic-splitting predicate is
assumed in the hypotheses. -/
theorem ternary_independent_factorization_of_signed_cofactor_square
    (M : Matrix (Fin 3) (Fin 3) K) (hM : M.IsSymm)
    (hdet : M.det = 0) (hpivot : M.adjugate 0 0 ≠ 0)
    (hsquare : ∃ s : K, s * s = -M.adjugate 0 0) :
    ∃ l r : Fin 3 → K,
      ternaryQuadraticPolynomial M = ternaryLinearPolynomial l * ternaryLinearPolynomial r ∧
      LinearIndependent K ![ternaryLinearPolynomial l, ternaryLinearPolynomial r] := by
  obtain ⟨u, v, he, hf, hc⟩ := ternary_binary_reduction M hM hdet hpivot
  obtain ⟨s, hs⟩ := hsquare
  have h21 : M 2 1 = M 1 2 := hM.apply 1 2
  have hp : M 1 1 * M 2 2 - M 1 2 * M 1 2 ≠ 0 := by
    simpa [adjugate_fin_three, h21] using hpivot
  have hs' : s * s = -(M 1 1 * M 2 2 - M 1 2 * M 1 2) := by
    simpa [adjugate_fin_three, h21] using hs
  have hsne : s ≠ 0 := by
    intro hz
    apply hp
    have hz' : -(M 1 1 * M 2 2 - M 1 2 * M 1 2) = 0 := by simpa [hz] using hs'.symm
    exact neg_eq_zero.mp hz'
  by_cases ha : M 1 1 = 0
  · have hb : M 1 2 ≠ 0 := by
      intro hz
      exact hp (by simp [ha, hz])
    refine ⟨![v, 0, 1], ![2 * M 1 2 * u + M 2 2 * v, 2 * M 1 2, M 2 2], ?_, ?_⟩
    · apply ternary_factor_of_coefficients <;> dsimp
      · rw [hc, ha]
        ring
      · simp [ha]
      · simp
      · rw [he, ha]
        ring
      · rw [hf]
        ring
      · ring
    · apply linearPolynomial_independent_of_minor
      simpa using neg_ne_zero.mpr (mul_ne_zero (NeZero.ne (2 : K)) hb)
  · refine ⟨![M 1 1 * u + (M 1 2 + s) * v, M 1 1, M 1 2 + s],
      ![u + (M 1 2 - s) / M 1 1 * v, 1, (M 1 2 - s) / M 1 1], ?_, ?_⟩
    · apply ternary_factor_of_coefficients <;> dsimp
      · rw [hc]
        field_simp [ha]
        linear_combination -(v ^ 2) * hs'
      · simp
      · field_simp [ha]
        linear_combination -hs'
      · rw [he]
        field_simp [ha]
        ring
      · rw [hf]
        field_simp [ha]
        linear_combination -(2 * v) * hs'
      · field_simp [ha]
        ring
    · apply linearPolynomial_independent_of_minor
      change M 1 1 * ((M 1 2 - s) / M 1 1) - (M 1 2 + s) * 1 ≠ 0
      rw [mul_div_cancel₀ _ ha]
      convert neg_ne_zero.mpr (mul_ne_zero (NeZero.ne (2 : K)) hsne) using 1
      ring

/-- The local geometric splitting criterion, expressed as equality of actual
polynomials and genuine linear independence of their factors. -/
theorem ternary_independent_factorization_iff_signed_cofactor_square
    (M : Matrix (Fin 3) (Fin 3) K) (hM : M.IsSymm)
    (hdet : M.det = 0) (hpivot : M.adjugate 0 0 ≠ 0) :
    (∃ l r : Fin 3 → K,
      ternaryQuadraticPolynomial M = ternaryLinearPolynomial l * ternaryLinearPolynomial r ∧
      LinearIndependent K ![ternaryLinearPolynomial l, ternaryLinearPolynomial r]) ↔
      ∃ s : K, s * s = -M.adjugate 0 0 := by
  constructor
  · rintro ⟨l, r, hfactor, _⟩
    exact ternary_factorization_implies_signed_cofactor_square M hM l r hfactor
  · exact ternary_independent_factorization_of_signed_cofactor_square M hM hdet hpivot

/-- The negative-twist cofactor equations have a field-valued solution exactly
when the actual rank-two conic splits into independent lines on this chart. -/
theorem ternary_independent_factorization_iff_cofactorRoot
    (M : Matrix (Fin 3) (Fin 3) K) (hM : M.IsSymm)
    (hdet : M.det = 0) (hpivot : M.adjugate 0 0 ≠ 0) :
    (∃ l r : Fin 3 → K,
      ternaryQuadraticPolynomial M = ternaryLinearPolynomial l * ternaryLinearPolynomial r ∧
      LinearIndependent K ![ternaryLinearPolynomial l, ternaryLinearPolynomial r]) ↔
      ∃ w : Fin 3 → K, IsCofactorRoot M w (-1) := by
  rw [ternary_independent_factorization_iff_signed_cofactor_square M hM hdet hpivot]
  simpa using (exists_cofactorRoot_iff_pivot_square_of_symmetric M hM 0 hdet
    (neg_ne_zero.mpr one_ne_zero) hpivot).symm

/-- Over the real numbers, the two actual line factors exist precisely for a
negative nonzero diagonal cofactor. -/
theorem real_ternary_independent_factorization_iff_negative_cofactor
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.IsSymm)
    (hdet : M.det = 0) (hpivot : M.adjugate 0 0 ≠ 0) :
    (∃ l r : Fin 3 → ℝ,
      ternaryQuadraticPolynomial M = ternaryLinearPolynomial l * ternaryLinearPolynomial r ∧
      LinearIndependent ℝ ![ternaryLinearPolynomial l, ternaryLinearPolynomial r]) ↔
      M.adjugate 0 0 < 0 := by
  rw [ternary_independent_factorization_iff_cofactorRoot M hM hdet hpivot]
  exact real_ternary_cofactorRoot_iff_negative_pivot M hM 0 hdet hpivot

end EvenQuinticConic
