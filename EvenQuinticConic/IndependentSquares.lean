import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Ring.Commute

/-!
# Independence of squares over an algebraically closed field

In a domain that is an algebra over an algebraically closed field, two
elements with proportional squares are themselves proportional.  This gives
the nonproportionality hypothesis needed for the conic-factorization lemmas.

The domain and algebra structure are actual hypotheses.  This file does not
construct a section ring or prove that sections of a specified line bundle
embed into such a domain.
-/

namespace EvenQuinticConic

variable {K R : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]

/-- When the proportionality scalar has a square root in the base field,
proportional squares in a domain imply proportional elements. -/
theorem exists_scalar_multiple_of_sq_eq_scalar_sq_of_root
    (s t : R) (c d : K) (hd : d ^ 2 = c)
    (hrel : s ^ 2 = algebraMap K R c * t ^ 2) :
    ∃ e : K, s = algebraMap K R e * t := by
  have hsq : s ^ 2 = (algebraMap K R d * t) ^ 2 := by
    rw [mul_pow, ← map_pow, hd]
    exact hrel
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hpos | hneg
  · exact ⟨d, hpos⟩
  · exact ⟨-d, by simpa only [map_neg, neg_mul] using hneg⟩

/-- Algebraic closure supplies the square root required in the preceding
lemma.  Neither element is required to be nonzero. -/
theorem exists_scalar_multiple_of_sq_eq_scalar_sq [IsAlgClosed K]
    (s t : R) (c : K) (hrel : s ^ 2 = algebraMap K R c * t ^ 2) :
    ∃ d : K, s = algebraMap K R d * t := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (by decide : 0 < 2)
  exact exists_scalar_multiple_of_sq_eq_scalar_sq_of_root s t c d hd hrel

/-- Nonproportional elements have nonproportional squares over an
algebraically closed base field. -/
theorem squares_not_scalar_proportional [IsAlgClosed K]
    (s t : R) (hind : ¬ ∃ d : K, s = algebraMap K R d * t) :
    ¬ ∃ c : K, s ^ 2 = algebraMap K R c * t ^ 2 := by
  rintro ⟨c, hc⟩
  exact hind (exists_scalar_multiple_of_sq_eq_scalar_sq s t c hc)

/-- Actual linear independence of a pair implies the scalar
nonproportionality used in the conic-classification theorem. -/
theorem squares_not_scalar_proportional_of_linearIndependent [IsAlgClosed K]
    (s t : R) (hind : LinearIndependent K ![s, t]) :
    ¬ ∃ c : K, s ^ 2 = algebraMap K R c * t ^ 2 := by
  apply squares_not_scalar_proportional s t
  rintro ⟨d, hd⟩
  have hnot : ∀ e : K, e • t ≠ s := by
    simpa using (linearIndependent_fin2.mp hind).2
  apply hnot d
  simpa only [Algebra.smul_def] using hd.symm

/-- Squaring preserves linear independence of a pair in a domain over an
algebraically closed field. -/
theorem linearIndependent_pair_squares [IsAlgClosed K]
    (s t : R) (hind : LinearIndependent K ![s, t]) :
    LinearIndependent K ![s ^ 2, t ^ 2] := by
  apply linearIndependent_fin2.mpr
  constructor
  · have ht : t ≠ 0 := by simpa using hind.ne_zero 1
    simpa using pow_ne_zero 2 ht
  · intro c hc
    apply squares_not_scalar_proportional_of_linearIndependent s t hind
    refine ⟨c, ?_⟩
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Algebra.smul_def] using hc.symm

end EvenQuinticConic
