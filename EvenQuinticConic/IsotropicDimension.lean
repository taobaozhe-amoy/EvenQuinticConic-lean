import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Lean.Elab.Tactic.Omega

/-!
# The dimension argument for an isotropic vector

This file proves the elementary linear algebra at the end of the proposed
Pfister-form argument.  It uses actual mathlib quadratic forms and subspaces.
It does not assert that a geometric conic-bundle construction supplies the
quadratic form, subspaces, or dimension hypotheses below.
-/

namespace EvenQuinticConic

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Two subspaces whose dimensions sum to more than the ambient dimension
have a nonzero vector in their intersection. -/
theorem exists_nonzero_mem_intersection_of_finrank_lt
    (U W : Submodule K V)
    (hdim : finrank K V < finrank K U + finrank K W) :
    ∃ v : V, v ∈ U ∧ v ∈ W ∧ v ≠ 0 := by
  have hsum := U.finrank_sup_add_finrank_inf_eq W
  have hle := (U ⊔ W).finrank_le
  have hpos : 0 < finrank K (U ⊓ W : Submodule K V) := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  refine ⟨v, v.property.1, v.property.2, ?_⟩
  intro hzero
  apply hv
  exact Subtype.ext hzero

/-- If a quadratic form vanishes on a sufficiently large subspace, its
restriction to any subspace meeting the dimension bound is isotropic. -/
theorem exists_nonzero_zero_in_subspace_of_finrank_lt
    (q : QuadraticForm K V) (U W : Submodule K V)
    (hW : ∀ w ∈ W, q w = 0)
    (hdim : finrank K V < finrank K U + finrank K W) :
    ∃ v : V, v ∈ U ∧ v ≠ 0 ∧ q v = 0 := by
  obtain ⟨v, hvU, hvW, hv⟩ :=
    exists_nonzero_mem_intersection_of_finrank_lt U W hdim
  exact ⟨v, hvU, hv, hW v hvW⟩

/-- The preceding result stated using mathlib's actual anisotropy predicate
on the restricted quadratic form. -/
theorem restriction_not_anisotropic_of_finrank_lt
    (q : QuadraticForm K V) (U W : Submodule K V)
    (hW : ∀ w ∈ W, q w = 0)
    (hdim : finrank K V < finrank K U + finrank K W) :
    ¬ (q.comp U.subtype).Anisotropic := by
  obtain ⟨v, hvU, hv, hq⟩ :=
    exists_nonzero_zero_in_subspace_of_finrank_lt q U W hW hdim
  apply (QuadraticMap.not_anisotropic_iff_exists _).mpr
  refine ⟨⟨v, hvU⟩, ?_, ?_⟩
  · intro hzero
    apply hv
    exact congrArg Subtype.val hzero
  · exact hq

/-- A five-dimensional subspace of an eight-dimensional quadratic space
with a four-dimensional totally isotropic subspace has isotropic restriction.

Below we construct the required subspace for an explicit split model.
No geometric embedding into that model is inferred by this theorem.
-/
theorem five_dimensional_restriction_of_eight_dimensional_form
    (q : QuadraticForm K V) (U W : Submodule K V)
    (hV : finrank K V = 8) (hU : finrank K U = 5)
    (hWdim : finrank K W = 4) (hW : ∀ w ∈ W, q w = 0) :
    ¬ (q.comp U.subtype).Anisotropic := by
  apply restriction_not_anisotropic_of_finrank_lt q U W hW
  omega

/-! We can also supply the required isotropic subspace for an explicit
hyperbolic form, rather than leave that subspace as a hypothesis. -/

/-- The vector space underlying the standard split form of dimension `2 * n`. -/
abbrev SplitSpace (K : Type*) (n : ℕ) := (Fin n → K) × (Fin n → K)

/-- The standard split quadratic form `q(x,y) = ∑ i, x i * y i`.
This is a sum of `n` hyperbolic planes. -/
noncomputable def splitForm (K : Type*) [Field K] (n : ℕ) :
    QuadraticForm K (SplitSpace K n) :=
  ∑ i : Fin n, QuadraticMap.linMulLin
    ((LinearMap.proj i).comp (LinearMap.fst K (Fin n → K) (Fin n → K)))
    ((LinearMap.proj i).comp (LinearMap.snd K (Fin n → K) (Fin n → K)))

@[simp]
theorem splitForm_apply (n : ℕ) (v : SplitSpace K n) :
    splitForm K n v = ∑ i : Fin n, v.1 i * v.2 i := by
  simp [splitForm, QuadraticMap.linMulLin_apply]

/-- The first factor consists entirely of zeros of the split quadratic form. -/
theorem splitForm_zero_on_first_factor (n : ℕ)
    (v : SplitSpace K n)
    (hv : v ∈ Submodule.fst K (Fin n → K) (Fin n → K)) :
    splitForm K n v = 0 := by
  have hv2 : v.2 = 0 := hv
  simp [splitForm_apply, hv2]

/-- An actual restriction of the explicit split form to a subspace of more
than half its dimension is isotropic. -/
theorem restriction_splitForm_not_anisotropic (n : ℕ)
    (U : Submodule K (SplitSpace K n)) (hU : n < finrank K U) :
    ¬ ((splitForm K n).comp U.subtype).Anisotropic := by
  let W := Submodule.fst K (Fin n → K) (Fin n → K)
  have hWdim : finrank K W = n := by
    exact (Submodule.fstEquiv K (Fin n → K) (Fin n → K)).finrank_eq.trans
      (Module.finrank_fin_fun (R := K))
  have hVdim : finrank K (SplitSpace K n) = n + n := by
    simp [SplitSpace]
  apply restriction_not_anisotropic_of_finrank_lt (splitForm K n) U W
  · exact splitForm_zero_on_first_factor n
  · rw [hVdim, hWdim]
    omega

/-- In particular, every five-dimensional subspace of four hyperbolic planes
contains a nonzero isotropic vector. -/
theorem five_dimensional_restriction_splitForm_four
    (U : Submodule K (SplitSpace K 4)) (hU : finrank K U = 5) :
    ¬ ((splitForm K 4).comp U.subtype).Anisotropic := by
  apply restriction_splitForm_not_anisotropic 4 U
  omega

end EvenQuinticConic
