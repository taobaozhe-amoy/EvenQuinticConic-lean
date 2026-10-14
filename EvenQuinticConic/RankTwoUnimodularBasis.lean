import EvenQuinticConic.RankTwoUnitBasis

/-! # A rank-two algebra basis beginning with one over any commutative base -/
noncomputable section
namespace EvenQuinticConic
variable {R : Type*} [CommRing R]

/-- A unimodular column can be completed to an invertible two by two matrix. -/
def rankTwoUnimodularEquiv (a b c d : R) (h : a * c + b * d = 1) :
    (Fin 2 → R) ≃ₗ[R] (Fin 2 → R) where
  toFun x := ![a * x 0 - d * x 1, b * x 0 + c * x 1]
  invFun y := ![c * y 0 + d * y 1, -b * y 0 + a * y 1]
  left_inv x := by
    ext i
    fin_cases i <;> dsimp
    · linear_combination x 0 * h
    · linear_combination x 1 * h
  right_inv x := by
    ext i
    fin_cases i <;> dsimp
    · linear_combination x 0 * h
    · linear_combination x 1 * h
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

variable {A : Type*} [CommRing A] [Algebra R A]

/-- The normalized trace supplies a unimodularity relation for the coordinates of one. -/
theorem rankTwo_one_trace_unimodular [Invertible (2 : R)]
    (v : Module.Basis (Fin 2) R A) :
    v.repr (1 : A) 0 * (⅟ (2 : R) * Algebra.trace R A (v 0)) +
      v.repr (1 : A) 1 * (⅟ (2 : R) * Algebra.trace R A (v 1)) = 1 := by
  have h := congrArg (Algebra.trace R A) (v.sum_repr (1 : A))
  have hs : v.repr (1 : A) 0 * Algebra.trace R A (v 0) +
      v.repr (1 : A) 1 * Algebra.trace R A (v 1) = 2 := by
    simpa only [Fin.sum_univ_two, map_add, map_smul, smul_eq_mul, rankTwo_trace_one v] using h
  calc
    _ = ⅟ (2 : R) * (v.repr (1 : A) 0 * Algebra.trace R A (v 0) +
      v.repr (1 : A) 1 * Algebra.trace R A (v 1)) := by ring
    _ = 1 := by rw [hs, invOf_mul_self]

/-- No local-ring hypothesis is needed to adapt a rank-two algebra basis. -/
theorem exists_rankTwo_basis_one_of_invertible_two [Invertible (2 : R)]
    (v : Module.Basis (Fin 2) R A) :
    ∃ w : Module.Basis (Fin 2) R A, w 0 = 1 := by
  let t := rankTwoUnimodularEquiv (v.repr (1 : A) 0) (v.repr (1 : A) 1)
    (⅟ (2 : R) * Algebra.trace R A (v 0))
    (⅟ (2 : R) * Algebra.trace R A (v 1)) (rankTwo_one_trace_unimodular v)
  refine ⟨Module.Basis.ofEquivFun (v.equivFun.trans t.symm), ?_⟩
  rw [Module.Basis.coe_ofEquivFun]
  apply v.equivFun.injective
  change v.equivFun (v.equivFun.symm (t (Pi.single 0 1))) = v.equivFun 1
  rw [LinearEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> simp [t, rankTwoUnimodularEquiv]

/-- A free rank-two formally unramified algebra has a unit Kummer model. -/
theorem exists_unit_kummer_model_of_rankTwo_basis [Invertible (2 : R)]
    [Algebra.FormallyUnramified R A] (v : Module.Basis (Fin 2) R A) :
    ∃ u : Rˣ, Nonempty (A ≃ₐ[R] KummerAlgebra (u : R)) := by
  obtain ⟨w, hw⟩ := exists_rankTwo_basis_one_of_invertible_two v
  exact exists_unit_kummer_model_of_basis w hw

end EvenQuinticConic
