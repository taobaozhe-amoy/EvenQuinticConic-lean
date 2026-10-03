import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.Ideal.Span
import Lean.Elab.Tactic.Omega

/-!
# The polynomial-degree step in the theta argument

These are genuine statements about multivariate polynomials and principal ideals.
They do not construct a theta characteristic or identify a curve's vanishing ideal.
In the geometric argument the restriction relation must first be shown to belong
to the principal ideal of the quintic. That bridge is not formalized here.
-/

namespace EvenQuinticConic

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- A multiple of a nonzero polynomial with smaller total degree is zero. -/
theorem eq_zero_of_dvd_of_totalDegree_lt
    (F G : MvPolynomial σ K) (hF : F ≠ 0)
    (hdvd : F ∣ G) (hdeg : G.totalDegree < F.totalDegree) : G = 0 := by
  obtain ⟨H, rfl⟩ := hdvd
  by_contra hFH
  have hH : H ≠ 0 := by
    intro h
    simp [h] at hFH
  rw [MvPolynomial.totalDegree_mul_of_isDomain hF hH] at hdeg
  omega

/-- The degree-four relation between three conics cannot be a nonzero
multiple of a quintic. -/
theorem conic_relation_of_quintic_divisibility
    (F A B D : MvPolynomial σ K)
    (hF : F.totalDegree = 5)
    (hA : A.totalDegree ≤ 2) (hB : B.totalDegree ≤ 2)
    (hD : D.totalDegree ≤ 2) (hdiv : F ∣ A * D - B ^ 2) :
    A * D = B ^ 2 := by
  have hF0 : F ≠ 0 := by
    intro h
    simp [h] at hF
  have hAD : (A * D).totalDegree ≤ 4 := by
    have h := MvPolynomial.totalDegree_mul A D
    omega
  have hBB : (B ^ 2).totalDegree ≤ 4 := by
    have h := MvPolynomial.totalDegree_pow B 2
    omega
  have hrel : (A * D - B ^ 2).totalDegree ≤ 4 :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le hAD hBB)
  have hz := eq_zero_of_dvd_of_totalDegree_lt F (A * D - B ^ 2) hF0 hdiv
    (by omega)
  exact sub_eq_zero.mp hz

/-- The same statement with the restriction relation expressed as membership
in the actual principal ideal `(F)`. -/
theorem conic_relation_of_mem_quintic_ideal
    (F A B D : MvPolynomial σ K)
    (hF : F.totalDegree = 5)
    (hA : A.totalDegree ≤ 2) (hB : B.totalDegree ≤ 2)
    (hD : D.totalDegree ≤ 2)
    (hrel : A * D - B ^ 2 ∈ Ideal.span ({F} : Set (MvPolynomial σ K))) :
    A * D = B ^ 2 := by
  apply conic_relation_of_quintic_divisibility F A B D hF hA hB hD
  exact Ideal.mem_span_singleton.mp hrel

end EvenQuinticConic
