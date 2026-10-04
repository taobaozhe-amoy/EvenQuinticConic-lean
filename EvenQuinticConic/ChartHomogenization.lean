import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Homogenization in an affine projective chart

If a polynomial evaluation sends a chosen projective coordinate to one,
homogenizing in that coordinate preserves its value. A vanishing-ideal
criterion for homogeneous forms therefore determines the entire affine
evaluation kernel, with the additional relation `X i - 1`.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial

variable {σ K A : Type*} [CommRing K] [CommRing A]

/-- Homogenize to the total degree using the chosen chart coordinate. -/
def chartHomogenization (i : σ) (P : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ d ∈ Finset.range (P.totalDegree + 1),
    X i ^ (P.totalDegree - d) * homogeneousComponent d P

/-- The constructed polynomial really is homogeneous of the stated degree. -/
theorem chartHomogenization_isHomogeneous (i : σ) (P : MvPolynomial σ K) :
    (chartHomogenization i P).IsHomogeneous P.totalDegree := by
  classical
  apply IsHomogeneous.sum
  intro d hd
  have hd' : d ≤ P.totalDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
  simpa only [Nat.sub_add_cancel hd'] using
    (isHomogeneous_X_pow i (P.totalDegree - d)).mul
      (homogeneousComponent_isHomogeneous d P)

/-- Setting the homogenizing coordinate equal to one preserves evaluation. -/
theorem map_chartHomogenization (f : MvPolynomial σ K →+* A) (i : σ)
    (hi : f (X i) = 1) (P : MvPolynomial σ K) :
    f (chartHomogenization i P) = f P := by
  classical
  simp only [chartHomogenization, map_sum, map_mul, map_pow, hi, one_pow, one_mul]
  rw [← map_sum, sum_homogeneousComponent]

/-- A homogeneous vanishing-ideal criterion determines the kernel on the
affine chart. No homogeneity assumption on the polynomial in the kernel is
required in the conclusion. -/
theorem ker_eq_span_of_homogeneous_vanishing_on_chart
    (f : MvPolynomial σ K →+* A) (i : σ) (F : MvPolynomial σ K)
    (hi : f (X i) = 1) (hF : f F = 0)
    (hvan : ∀ (P : MvPolynomial σ K) (d : ℕ),
      P.IsHomogeneous d → f P = 0 → P ∈ Ideal.span {F}) :
    RingHom.ker f = Ideal.span {F, X i - 1} := by
  classical
  let J : Ideal (MvPolynomial σ K) := Ideal.span {F, X i - 1}
  have hFJ : Ideal.span {F} ≤ J := Ideal.span_mono (by simp)
  have hiJ : Ideal.Quotient.mk J (X i) = 1 := by
    rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    exact Ideal.subset_span (by simp)
  apply le_antisymm
  · intro P hP
    have hH : chartHomogenization i P ∈ J := hFJ
      (hvan _ _ (chartHomogenization_isHomogeneous i P)
        (by simpa only [map_chartHomogenization f i hi P] using hP))
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    rw [← map_chartHomogenization (Ideal.Quotient.mk J) i hiJ P]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hH
  · apply Ideal.span_le.mpr
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl
    · exact hF
    · change f (X i - 1) = 0
      simp [hi]

end EvenQuinticConic
