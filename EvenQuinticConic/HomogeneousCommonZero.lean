import EvenQuinticConic.PlaneOriginHeight
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

/-!
# Intersection of two homogeneous plane equations

Two positive-degree homogeneous ternary forms over an algebraically closed
field have a common nonzero zero. The proof applies the Nullstellensatz and
Krull's height theorem to their affine cones.
-/

namespace EvenQuinticConic

open MvPolynomial

variable {K : Type*} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
private theorem pair_spanRank_toENat_le_two (G H : MvPolynomial (Fin 3) K) :
    (Ideal.span ({G, H} : Set (MvPolynomial (Fin 3) K))).spanRank.toENat ≤ 2 := by
  classical
  rw [Submodule.spanRank_toENat_eq_iInf_finset_card]
  refine le_trans (iInf_le _ ⟨{G, H}, by simp⟩) ?_
  by_cases hGH : G = H <;> simp [hGH]

/-- Height-theoretic form of the projective intersection assertion. -/
theorem homogeneous_ternary_common_zero_of_origin_height
    (horigin : (3 : ℕ∞) ≤ (RingHom.ker (eval (0 : Fin 3 → K))).height)
    (G H : MvPolynomial (Fin 3) K) {d e : ℕ}
    (hG : G.IsHomogeneous d) (hH : H.IsHomogeneous e)
    (hd : 0 < d) (he : 0 < e) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ eval v G = 0 ∧ eval v H = 0 := by
  classical
  by_contra h
  push_neg at h
  let I : Ideal (MvPolynomial (Fin 3) K) := Ideal.span {G, H}
  have hG0 : eval (0 : Fin 3 → K) G = 0 := by
    rw [eval_zero]
    exact hG.coeff_eq_zero (by simpa using Nat.ne_of_lt hd)
  have hH0 : eval (0 : Fin 3 → K) H = 0 := by
    rw [eval_zero]
    exact hH.coeff_eq_zero (by simpa using Nat.ne_of_lt he)
  have hzero : zeroLocus K I = {0} := by
    change zeroLocus K (Ideal.span ({G, H} : Set (MvPolynomial (Fin 3) K))) = {0}
    rw [MvPolynomial.zeroLocus_span]
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    constructor
    · intro hv
      by_contra hv0
      exact h v hv0 hv.1 hv.2
    · rintro rfl
      exact ⟨hG0, hH0⟩
  have hrad : I.radical = vanishingIdeal K ({0} : Set (Fin 3 → K)) := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K) I, hzero]
  have hminimal : vanishingIdeal K ({0} : Set (Fin 3 → K)) ∈ I.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hupper : (vanishingIdeal K ({0} : Set (Fin 3 → K))).height ≤ 2 :=
    (Ideal.height_le_spanRank_toENat_of_mem_minimal_primes I _ hminimal).trans
      (pair_spanRank_toENat_le_two G H)
  have hid : vanishingIdeal K ({0} : Set (Fin 3 → K)) =
      RingHom.ker (eval (0 : Fin 3 → K)) := by
    ext p
    simp
  rw [hid] at hupper
  have := horigin.trans hupper
  norm_num at this

/-- Two positive-degree plane forms over an algebraically closed field meet
at a nonzero vector. Zero forms are allowed; no irreducibility or reducedness
assumption is required. -/
theorem homogeneous_ternary_common_zero
    (G H : MvPolynomial (Fin 3) K) {d e : ℕ}
    (hG : G.IsHomogeneous d) (hH : H.IsHomogeneous e)
    (hd : 0 < d) (he : 0 < e) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ eval v G = 0 ∧ eval v H = 0 :=
  homogeneous_ternary_common_zero_of_origin_height
    (planeOriginIdeal_height_ge_three K) G H hG hH hd he

end EvenQuinticConic
