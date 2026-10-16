import EvenQuinticConic.AdjugateRankOne
import EvenQuinticConic.RealKummer

/-!
# Real cofactor equations and their signed Kummer parameter

For an actual symmetric singular real matrix on a nonzero cofactor pivot,
the cofactor-root equations have a real solution exactly when the signed
pivot parameter is positive. Their fiber has two elements in the positive
case and no elements in the negative case. The rank-three and rank-five
sign conventions are separate explicit corollaries.

The cofactor equations have not yet been identified with the global
geometric discriminant double cover. These are field-valued matrix and
algebra statements, not a claim that the total real conic bundle is connected.
-/

namespace EvenQuinticConic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Changing nonzero diagonal cofactor pivots constructs an actual isomorphism
of the local quadratic algebras. The rescaling coefficient and its square
relation are derived from the original matrix. -/
noncomputable def cofactorPivotKummerEquiv
    {K : Type*} [Field K] (M : Matrix n n K) (hM : M.IsSymm) (k j : n)
    (hdet : M.det = 0) (hk : M.adjugate k k ≠ 0) (hj : M.adjugate j j ≠ 0)
    (twist : K) :
    KummerAlgebra (twist * M.adjugate j j) ≃ₐ[K]
      KummerAlgebra (twist * M.adjugate k k) :=
  kummerRescaleEquiv _ _ (M.adjugate j k / M.adjugate k k)
    (adjugate_transition_ne_zero M hM k j hdet hk hj) (by
      calc
        twist * M.adjugate j j =
            twist * (M.adjugate k k * (M.adjugate j j / M.adjugate k k)) := by
          rw [mul_div_cancel₀ _ hk]
        _ = twist * (M.adjugate k k *
            ((M.adjugate j k / M.adjugate k k) *
              (M.adjugate j k / M.adjugate k k))) := by
          rw [adjugate_diagonal_ratio_eq_square M hM k j hdet hk]
        _ = _ := by ring)

/-- The pivot-coordinate equivalence identifies actual real vector solutions
with actual scalar-valued algebra maps, not just their existence. -/
noncomputable def realCofactorRootEquivKummerPoints
    (M : Matrix n n ℝ) (hM : M.IsSymm) (k : n) {twist : ℝ}
    (hdet : M.det = 0) (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0) :
    {v : n → ℝ // IsCofactorRoot M v twist} ≃
      (KummerAlgebra (twist * M.adjugate k k) →ₐ[ℝ] ℝ) :=
  (cofactorRootFiberEquivScalarRoots_of_symmetric M hM k hdet htwist hpivot).trans
    (kummerAlgHomEquivRoots (twist * M.adjugate k k)).symm

/-- Actual real algebra points of the signed local Kummer algebra are
equivalent to solvability of the cofactor equations. -/
theorem real_cofactorRoot_iff_kummer_point
    (M : Matrix n n ℝ) (hM : M.IsSymm) (k : n) {twist : ℝ}
    (hdet : M.det = 0) (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0) :
    (∃ v : n → ℝ, IsCofactorRoot M v twist) ↔
      Nonempty (KummerAlgebra (twist * M.adjugate k k) →ₐ[ℝ] ℝ) := by
  rw [exists_cofactorRoot_iff_pivot_square_of_symmetric M hM k hdet htwist hpivot,
    nonempty_kummerAlgHom_iff]

/-- The nonzero signed cofactor must be strictly positive, not merely
nonnegative, for a real solution to exist. -/
theorem real_cofactorRoot_iff_positive
    (M : Matrix n n ℝ) (hM : M.IsSymm) (k : n) {twist : ℝ}
    (hdet : M.det = 0) (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0) :
    (∃ v : n → ℝ, IsCofactorRoot M v twist) ↔ 0 < twist * M.adjugate k k := by
  rw [real_cofactorRoot_iff_kummer_point M hM k hdet htwist hpivot,
    real_kummer_point_iff_pos _ (mul_ne_zero htwist hpivot)]

/-- Positive signed pivot gives exactly two actual real vector solutions. -/
theorem real_cofactorRoot_card_two_of_positive
    (M : Matrix n n ℝ) (hM : M.IsSymm) (k : n) {twist : ℝ}
    (hdet : M.det = 0) (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0)
    (hpos : 0 < twist * M.adjugate k k) :
    Nat.card {v : n → ℝ // IsCofactorRoot M v twist} = 2 := by
  obtain ⟨v, hv⟩ :=
    (real_cofactorRoot_iff_positive M hM k hdet htwist hpivot).mpr hpos
  exact cofactorRootFiber_card_eq_two M v hv
    ⟨k, cofactorRoot_pivot_ne_zero M v k hv htwist hpivot⟩

/-- Negative signed pivot gives an empty fiber. -/
theorem real_cofactorRoot_card_zero_of_negative
    (M : Matrix n n ℝ) (hM : M.IsSymm) (k : n) {twist : ℝ}
    (hdet : M.det = 0) (htwist : twist ≠ 0) (hpivot : M.adjugate k k ≠ 0)
    (hneg : twist * M.adjugate k k < 0) :
    Nat.card {v : n → ℝ // IsCofactorRoot M v twist} = 0 := by
  letI : IsEmpty {v : n → ℝ // IsCofactorRoot M v twist} := ⟨fun v => by
    have hpos := (real_cofactorRoot_iff_positive M hM k hdet htwist hpivot).mp
      ⟨v.val, v.property⟩
    exact (not_lt_of_ge hneg.le) hpos⟩
  exact Nat.card_of_isEmpty

/-- Rank-three convention: the cofactor equations use the negative twist. -/
theorem real_ternary_cofactorRoot_iff_negative_pivot
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.IsSymm) (k : Fin 3)
    (hdet : M.det = 0) (hpivot : M.adjugate k k ≠ 0) :
    (∃ v : Fin 3 → ℝ, IsCofactorRoot M v (-1)) ↔ M.adjugate k k < 0 := by
  simpa using real_cofactorRoot_iff_positive M hM k hdet (by norm_num : (-1 : ℝ) ≠ 0)
    hpivot

/-- Rank-five convention: the cofactor equations use the positive twist. -/
theorem real_quinary_cofactorRoot_iff_positive_pivot
    (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : M.IsSymm) (k : Fin 5)
    (hdet : M.det = 0) (hpivot : M.adjugate k k ≠ 0) :
    (∃ v : Fin 5 → ℝ, IsCofactorRoot M v 1) ↔ 0 < M.adjugate k k := by
  simpa using real_cofactorRoot_iff_positive M hM k hdet (by norm_num : (1 : ℝ) ≠ 0)
    hpivot

end EvenQuinticConic
