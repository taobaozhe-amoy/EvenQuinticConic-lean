import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# A genuine good coordinate for a homogeneous plane equation

Over an infinite field a nonzero homogeneous polynomial does not vanish at
all vectors. Explicit invertible linear substitutions can therefore place a
nonvanishing vector on a specified coordinate axis. No good-coordinate
hypothesis is postulated here.
-/

namespace EvenQuinticConic

open MvPolynomial

variable {K : Type*} [Field K]

/-- A nonzero homogeneous polynomial over an infinite field has an actual
vector where it does not vanish. -/
theorem homogeneous_exists_eval_ne_zero [Infinite K]
    {F : MvPolynomial (Fin 3) K} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) :
    ∃ v : Fin 3 → K, eval v F ≠ 0 := by
  by_contra h
  push_neg at h
  exact hF0 (hF.eq_zero_of_forall_eval_eq_zero h)

/-- Positive degree makes every vector at which the polynomial is nonzero a
nonzero vector. -/
theorem homogeneous_eval_ne_zero_vector
    {F : MvPolynomial (Fin 3) K} {d : ℕ} (hF : F.IsHomogeneous d)
    (hd : 0 < d) {v : Fin 3 → K} (hv : eval v F ≠ 0) : v ≠ 0 := by
  rintro rfl
  apply hv
  rw [eval_zero]
  exact hF.coeff_eq_zero (by simpa using Nat.ne_of_lt hd)

/-- The forward linear substitution with pivot `j`. It sends the `j`-axis
unit vector to `v`. -/
noncomputable def pivotCoordinate (j : Fin 3) (v : Fin 3 → K) (i : Fin 3) :
    MvPolynomial (Fin 3) K :=
  if i = j then C (v j) * X j else X i + C (v i) * X j

/-- The explicit inverse linear substitution. -/
noncomputable def pivotCoordinateInverse (j : Fin 3) (v : Fin 3 → K) (i : Fin 3) :
    MvPolynomial (Fin 3) K :=
  if i = j then C ((v j)⁻¹) * X j else X i - C (v i / v j) * X j

/-- Replacing one matrix column by `v` is invertible whenever its pivot is
nonzero. This is an actual polynomial algebra equivalence. -/
noncomputable def pivotCoordinateEquiv (j : Fin 3) (v : Fin 3 → K)
    (hv : v j ≠ 0) : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K :=
  AlgEquiv.ofAlgHom (aeval (pivotCoordinate j v))
    (aeval (pivotCoordinateInverse j v))
    (by
      ext i : 1
      have hc : C ((v j)⁻¹) * C (v j) = (1 : MvPolynomial (Fin 3) K) := by
        rw [← map_mul, inv_mul_cancel₀ hv, map_one]
      by_cases hi : i = j
      · subst i
        simpa [pivotCoordinate, pivotCoordinateInverse, ← mul_assoc] using hc
      · simp only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply,
          pivotCoordinateInverse, pivotCoordinate, if_neg hi, if_true,
          map_sub, map_mul, aeval_C, algebraMap_eq]
        simp only [div_eq_mul_inv, C_mul]
        calc
          _ = X i + C (v i) * X j - C (v i) * (C ((v j)⁻¹) * C (v j)) * X j := by ring
          _ = X i := by rw [hc]; ring)
    (by
      ext i : 1
      have hc : C (v j) * C ((v j)⁻¹) = (1 : MvPolynomial (Fin 3) K) := by
        rw [← map_mul, mul_inv_cancel₀ hv, map_one]
      by_cases hi : i = j
      · subst i
        simpa [pivotCoordinate, pivotCoordinateInverse, ← mul_assoc] using hc
      · simp only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply,
          pivotCoordinateInverse, pivotCoordinate, if_neg hi, if_true,
          map_add, map_mul, aeval_C, algebraMap_eq]
        simp only [div_eq_mul_inv, C_mul]
        ring)

theorem pivotCoordinateEquiv_homogeneous (j : Fin 3) (v : Fin 3 → K)
    (hv : v j ≠ 0) {F : MvPolynomial (Fin 3) K} {d : ℕ}
    (hF : F.IsHomogeneous d) : (pivotCoordinateEquiv j v hv F).IsHomogeneous d := by
  change (aeval (pivotCoordinate j v) F).IsHomogeneous d
  have hc : ∀ i, (pivotCoordinate j v i).IsHomogeneous 1 := by
    intro i
    dsimp [pivotCoordinate]
    split
    · exact isHomogeneous_C_mul_X _ _
    · exact (isHomogeneous_X K i).add (isHomogeneous_C_mul_X _ _)
  have ht := hF.aeval (pivotCoordinate j v) hc
  simpa using ht

/-- The explicit inverse substitution also preserves every homogeneous
degree. This gives actual linear forms in the original coordinates. -/
theorem pivotCoordinateEquiv_symm_homogeneous (j : Fin 3) (v : Fin 3 → K)
    (hv : v j ≠ 0) {F : MvPolynomial (Fin 3) K} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    ((pivotCoordinateEquiv j v hv).symm F).IsHomogeneous d := by
  change (aeval (pivotCoordinateInverse j v) F).IsHomogeneous d
  have hc : ∀ i, (pivotCoordinateInverse j v i).IsHomogeneous 1 := by
    intro i
    dsimp [pivotCoordinateInverse]
    split
    · exact isHomogeneous_C_mul_X _ _
    · exact (isHomogeneous_X K i).sub (isHomogeneous_C_mul_X _ _)
  have ht := hF.aeval (pivotCoordinateInverse j v) hc
  simpa using ht

/-- Evaluation on the pivot axis after the invertible substitution is
exactly evaluation at the chosen vector. -/
theorem pivotCoordinateEquiv_eval_axis (j : Fin 3) (v : Fin 3 → K)
    (hv : v j ≠ 0) (F : MvPolynomial (Fin 3) K) :
    eval (Pi.single j 1) (pivotCoordinateEquiv j v hv F) = eval v F := by
  change eval (Pi.single j 1) (eval₂ C (pivotCoordinate j v) F) = _
  rw [← eval_assoc]
  congr 2
  funext i
  by_cases hi : i = j
  · subst i
    simp [pivotCoordinate]
  · simp [pivotCoordinate, hi]

/-- A homogeneous polynomial whose pure `j`-power coefficient vanishes
vanishes at the unit vector on the `j`-axis. -/
theorem homogeneous_eval_axis_eq_zero_of_coeff_eq_zero
    {F : MvPolynomial (Fin 3) K} {d : ℕ} (hF : F.IsHomogeneous d)
    (j : Fin 3) (hc : coeff (Finsupp.single j d) F = 0) :
    eval (Pi.single j 1) F = 0 := by
  apply eval₂Hom_eq_zero
  intro m hm
  by_contra hn
  push_neg at hn
  have hs : m.support ⊆ {j} := by
    intro i hi
    by_contra hij
    have hne : i ≠ j := by simpa using hij
    exact hn i hi (Pi.single_eq_of_ne hne 1)
  have he : m = Finsupp.single j (m j) := Finsupp.support_subset_singleton.mp hs
  have hdegree : m j = d := by
    have hd := hF hm
    rw [he] at hd
    simpa [Finsupp.weight_apply] using hd
  rw [he, hdegree, hc] at hm
  exact hm rfl

/-- The pure-power coefficient of a homogeneous form equals its value on
the corresponding coordinate-axis unit vector. -/
theorem homogeneous_coeff_single_eq_eval_axis
    {F : MvPolynomial (Fin 3) K} {d : ℕ} (hF : F.IsHomogeneous d)
    (j : Fin 3) : coeff (Finsupp.single j d) F = eval (Pi.single j 1) F := by
  have hh := hF.sub (isHomogeneous_monomial (coeff (Finsupp.single j d) F)
    (Finsupp.degree_single j d))
  have hz : coeff (Finsupp.single j d)
      (F - monomial (Finsupp.single j d) (coeff (Finsupp.single j d) F)) = 0 := by
    simp
  have he := homogeneous_eval_axis_eq_zero_of_coeff_eq_zero hh j hz
  have heq : eval (Pi.single j 1) F - coeff (Finsupp.single j d) F = 0 := by
    simpa [eval_monomial, Finsupp.prod_single_index] using he
  exact (sub_eq_zero.mp heq).symm

/-- There are actual invertible linear polynomial coordinates making the
coefficient of the highest pure power in the prescribed last variable nonzero.
The same algebra equivalence preserves all homogeneous degrees. -/
theorem homogeneous_exists_good_last_coordinate_both [Infinite K]
    {F : MvPolynomial (Fin 3) K} {d : ℕ} (hF : F.IsHomogeneous d)
    (hF0 : F ≠ 0) (hd : 0 < d) :
    ∃ E : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K,
      (∀ {G : MvPolynomial (Fin 3) K} {n : ℕ}, G.IsHomogeneous n →
        (E G).IsHomogeneous n) ∧
      (∀ {G : MvPolynomial (Fin 3) K} {n : ℕ}, G.IsHomogeneous n →
        (E.symm G).IsHomogeneous n) ∧ coeff (Finsupp.single 2 d) (E F) ≠ 0 := by
  obtain ⟨v, hv⟩ := homogeneous_exists_eval_ne_zero hF hF0
  have hv0 := homogeneous_eval_ne_zero_vector hF hd hv
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hv0 (funext hn)
  let S : Equiv.Perm (Fin 3) := Equiv.swap j 2
  let E := (pivotCoordinateEquiv j v hj).trans (renameEquiv K S)
  refine ⟨E, ?_, ?_, ?_⟩
  · intro G n hG
    exact (pivotCoordinateEquiv_homogeneous j v hj hG).rename_isHomogeneous
  · intro G n hG
    change ((pivotCoordinateEquiv j v hj).symm ((renameEquiv K S).symm G)).IsHomogeneous n
    rw [renameEquiv_symm]
    exact pivotCoordinateEquiv_symm_homogeneous j v hj hG.rename_isHomogeneous
  · have hh : (E F).IsHomogeneous d :=
      (pivotCoordinateEquiv_homogeneous j v hj hF).rename_isHomogeneous
    rw [homogeneous_coeff_single_eq_eval_axis hh]
    change eval (Pi.single 2 1) (rename S (pivotCoordinateEquiv j v hj F)) ≠ 0
    rw [eval_rename]
    have he : (Pi.single 2 (1 : K)) ∘ S = Pi.single j 1 := by
      funext i
      simp [S, Pi.single_apply, Equiv.swap_apply_eq_iff]
    rw [he, pivotCoordinateEquiv_eval_axis]
    exact hv

/-- There are actual invertible linear polynomial coordinates making the
coefficient of the highest pure power in the prescribed last variable nonzero.
The same algebra equivalence preserves all homogeneous degrees. -/
theorem homogeneous_exists_good_last_coordinate [Infinite K]
    {F : MvPolynomial (Fin 3) K} {d : ℕ} (hF : F.IsHomogeneous d)
    (hF0 : F ≠ 0) (hd : 0 < d) :
    ∃ E : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K,
      (∀ {G : MvPolynomial (Fin 3) K} {n : ℕ}, G.IsHomogeneous n →
        (E G).IsHomogeneous n) ∧ coeff (Finsupp.single 2 d) (E F) ≠ 0 := by
  obtain ⟨E, hE, _, hc⟩ := homogeneous_exists_good_last_coordinate_both hF hF0 hd
  exact ⟨E, hE, hc⟩

/-- Multiplying by a nonzero scalar does not change the actual principal
ideal of the equation. -/
theorem homogeneous_scalar_normalization_ideal (c : K) (hc : c ≠ 0)
    (F : MvPolynomial (Fin 3) K) :
    Ideal.span ({C c * F} : Set (MvPolynomial (Fin 3) K)) = Ideal.span {F} := by
  exact Ideal.span_singleton_mul_left_unit ((isUnit_iff_ne_zero.mpr hc).map C) F

/-- Coordinate choice followed by multiplication by an actual nonzero
scalar makes the last pure-power coefficient exactly one. -/
theorem homogeneous_exists_normalized_last_coordinate_both [Infinite K]
    {F : MvPolynomial (Fin 3) K} {d : ℕ} (hF : F.IsHomogeneous d)
    (hF0 : F ≠ 0) (hd : 0 < d) :
    ∃ (E : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K) (c : K),
      c ≠ 0 ∧
      (∀ {G : MvPolynomial (Fin 3) K} {n : ℕ}, G.IsHomogeneous n →
        (E G).IsHomogeneous n) ∧
      (∀ {G : MvPolynomial (Fin 3) K} {n : ℕ}, G.IsHomogeneous n →
        (E.symm G).IsHomogeneous n) ∧
      (C c * E F).IsHomogeneous d ∧
      coeff (Finsupp.single 2 d) (C c * E F) = 1 ∧
      Ideal.span ({C c * E F} : Set (MvPolynomial (Fin 3) K)) = Ideal.span {E F} := by
  obtain ⟨E, hE, hEsymm, hcoeff⟩ := homogeneous_exists_good_last_coordinate_both hF hF0 hd
  let c : K := (coeff (Finsupp.single 2 d) (E F))⁻¹
  have hc : c ≠ 0 := inv_ne_zero hcoeff
  refine ⟨E, c, hc, hE, hEsymm, (hE hF).C_mul c, ?_,
    homogeneous_scalar_normalization_ideal c hc (E F)⟩
  rw [coeff_C_mul]
  exact inv_mul_cancel₀ hcoeff

/-- Coordinate choice followed by multiplication by an actual nonzero
scalar makes the last pure-power coefficient exactly one. -/
theorem homogeneous_exists_normalized_last_coordinate [Infinite K]
    {F : MvPolynomial (Fin 3) K} {d : ℕ} (hF : F.IsHomogeneous d)
    (hF0 : F ≠ 0) (hd : 0 < d) :
    ∃ (E : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K) (c : K),
      c ≠ 0 ∧
      (∀ {G : MvPolynomial (Fin 3) K} {n : ℕ}, G.IsHomogeneous n →
        (E G).IsHomogeneous n) ∧
      (C c * E F).IsHomogeneous d ∧
      coeff (Finsupp.single 2 d) (C c * E F) = 1 ∧
      Ideal.span ({C c * E F} : Set (MvPolynomial (Fin 3) K)) = Ideal.span {E F} := by
  obtain ⟨E, c, hc, hE, _, hhom, hcoeff, hideal⟩ :=
    homogeneous_exists_normalized_last_coordinate_both hF hF0 hd
  exact ⟨E, c, hc, hE, hhom, hcoeff, hideal⟩

end EvenQuinticConic
