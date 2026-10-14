import EvenQuinticConic.QuadraticBasisTraceZero
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-! # A basis beginning with one over a local base ring -/
noncomputable section
namespace EvenQuinticConic
variable {R : Type*} [CommRing R]

/-- An invertible triangular coordinate change with prescribed first column. -/
def rankTwoColumnEquiv (u : Rˣ) (c : R) : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R) where
  toFun x := ![(u : R) * x 0, c * x 0 + x 1]
  invFun y := ![(↑u⁻¹ : R) * y 0, y 1 - c * ((↑u⁻¹ : R) * y 0)]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv y := by
    ext i
    fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

variable {A : Type*} [CommRing A] [Algebra R A]

/-- A unit coordinate of one supplies an actual basis beginning with one. -/
theorem exists_basis_one_of_unit_coordinate
    (v : Module.Basis (Fin 2) R A) (h : IsUnit (v.repr (1 : A) 0)) :
    ∃ w : Module.Basis (Fin 2) R A, w 0 = 1 := by
  obtain ⟨u, hu⟩ := h
  let e := v.equivFun.trans (rankTwoColumnEquiv u (v.repr (1 : A) 1)).symm
  refine ⟨Module.Basis.ofEquivFun e, ?_⟩
  rw [Module.Basis.coe_ofEquivFun]
  apply v.equivFun.injective
  change v.equivFun (v.equivFun.symm
    (rankTwoColumnEquiv u (v.repr (1 : A) 1) (Pi.single 0 1))) = v.equivFun 1
  rw [LinearEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> simp [rankTwoColumnEquiv, hu]

/-- The trace of one is two for an arbitrary rank-two basis. -/
theorem rankTwo_trace_one (v : Module.Basis (Fin 2) R A) :
    Algebra.trace R A 1 = 2 := by
  simpa using Algebra.trace_algebraMap_of_basis v (1 : R)

/-- In a local ring, one has a unit coordinate in every rank-two basis.
Invertibility of two is used through the actual trace of one. -/
theorem rankTwo_one_unit_coordinate [IsLocalRing R] [Invertible (2 : R)]
    (v : Module.Basis (Fin 2) R A) :
    IsUnit (v.repr (1 : A) 0) ∨ IsUnit (v.repr (1 : A) 1) := by
  have h := congrArg (Algebra.trace R A) (v.sum_repr (1 : A))
  have hs : v.repr (1 : A) 0 * Algebra.trace R A (v 0) +
      v.repr (1 : A) 1 * Algebra.trace R A (v 1) = 2 := by
    simpa only [Fin.sum_univ_two, map_add, map_smul, smul_eq_mul, rankTwo_trace_one v] using h
  have hu : IsUnit (v.repr (1 : A) 0 * Algebra.trace R A (v 0) +
      v.repr (1 : A) 1 * Algebra.trace R A (v 1)) := hs.symm ▸ isUnit_of_invertible (2 : R)
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h0 | h1
  · exact Or.inl (isUnit_of_mul_isUnit_left h0)
  · exact Or.inr (isUnit_of_mul_isUnit_left h1)

/-- An arbitrary rank-two basis can be replaced by one beginning with one. -/
theorem exists_rankTwo_basis_one [IsLocalRing R] [Invertible (2 : R)]
    (v : Module.Basis (Fin 2) R A) :
    ∃ w : Module.Basis (Fin 2) R A, w 0 = 1 := by
  rcases rankTwo_one_unit_coordinate v with h0 | h1
  · exact exists_basis_one_of_unit_coordinate v h0
  · let w := v.reindex (Equiv.swap (0 : Fin 2) 1)
    apply exists_basis_one_of_unit_coordinate w
    simpa [w] using h1

end EvenQuinticConic
