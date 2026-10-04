import EvenQuinticConic.PlaneQuintic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Homogeneous factors

The top homogeneous component of a product is the product of its top
homogeneous components. Hence every nontrivial factorization of a nonzero
homogeneous polynomial yields a factorization by two positive-degree forms.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*}

/-- Taking the top component commutes with multiplication, including when one
of the polynomials is zero. -/
theorem homogeneousComponent_top_mul (G H : MvPolynomial σ K) :
    homogeneousComponent (G.totalDegree + H.totalDegree) (G * H) =
      homogeneousComponent G.totalDegree G * homogeneousComponent H.totalDegree H := by
  classical
  ext d
  by_cases hd : d.degree = G.totalDegree + H.totalDegree
  · rw [coeff_homogeneousComponent, if_pos hd, coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    have hab' : ab.1 + ab.2 = d := Finset.mem_antidiagonal.mp hab
    by_cases hG : coeff ab.1 G = 0
    · simp [coeff_homogeneousComponent, hG]
    by_cases hH : coeff ab.2 H = 0
    · simp [coeff_homogeneousComponent, hH]
    have hGdeg := le_totalDegree (mem_support_iff.mpr hG)
    have hHdeg := le_totalDegree (mem_support_iff.mpr hH)
    have hadd : ab.1.degree + ab.2.degree = d.degree := by
      rw [← Finsupp.degree_add, hab']
    have hGtop : ab.1.degree = G.totalDegree := by
      change ab.1.degree ≤ G.totalDegree at hGdeg
      change ab.2.degree ≤ H.totalDegree at hHdeg
      omega
    have hHtop : ab.2.degree = H.totalDegree := by
      change ab.1.degree ≤ G.totalDegree at hGdeg
      change ab.2.degree ≤ H.totalDegree at hHdeg
      omega
    simp [coeff_homogeneousComponent, hGtop, hHtop]
  · rw [coeff_homogeneousComponent, if_neg hd]
    exact ((homogeneousComponent_isHomogeneous G.totalDegree G).mul
      (homogeneousComponent_isHomogeneous H.totalDegree H)).coeff_eq_zero hd |>.symm

/-- A nonzero polynomial over a field is a nonunit exactly when its degree is
positive. Only this forward direction is needed for nontrivial factors. -/
theorem totalDegree_pos_of_nonzero_nonunit (G : MvPolynomial σ K)
    (hG : G ≠ 0) (hunit : ¬ IsUnit G) : 0 < G.totalDegree := by
  by_contra hpos
  have hdeg : G.totalDegree = 0 := by omega
  have hC := totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hc : G.coeff 0 ≠ 0 := by
    intro hc
    apply hG
    rw [hC, hc, map_zero]
  exact hunit (hC ▸ (isUnit_iff_ne_zero.mpr hc).map C)

/-- Replace a nontrivial factorization of a nonzero homogeneous form by one
whose two factors are homogeneous of positive degrees. -/
theorem homogeneous_positive_factorization_of_nontrivial
    (F G H : MvPolynomial σ K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hF0 : F ≠ 0) (hfactor : F = G * H)
    (hGunit : ¬ IsUnit G) (hHunit : ¬ IsUnit H) :
    ∃ (A B : MvPolynomial σ K) (a b : ℕ),
      0 < a ∧ 0 < b ∧ A.IsHomogeneous a ∧ B.IsHomogeneous b ∧ F = A * B := by
  have hG0 : G ≠ 0 := by intro hz; simp [hz] at hfactor; exact hF0 hfactor
  have hH0 : H ≠ 0 := by intro hz; simp [hz] at hfactor; exact hF0 hfactor
  have hdegrees : G.totalDegree + H.totalDegree = d := by
    rw [← totalDegree_mul_of_isDomain hG0 hH0, ← hfactor]
    exact hF.totalDegree hF0
  refine ⟨homogeneousComponent G.totalDegree G,
    homogeneousComponent H.totalDegree H, G.totalDegree, H.totalDegree,
    totalDegree_pos_of_nonzero_nonunit G hG0 hGunit,
    totalDegree_pos_of_nonzero_nonunit H hH0 hHunit,
    homogeneousComponent_isHomogeneous _ _, homogeneousComponent_isHomogeneous _ _, ?_⟩
  rw [← homogeneousComponent_top_mul, ← hfactor, hdegrees]
  exact (homogeneousComponent_of_mem hF).trans (if_pos rfl) |>.symm

end EvenQuinticConic
