import EvenQuinticConic.IncidenceMinorFromDeterminant
import EvenQuinticConic.ProjectiveCoordinateSections

/-!
# The actual projective gradient of a nondegenerate ternary quadratic

The derivatives of `xᵀ R x` are the coordinates of `2 R x`.  In every
homogeneous prime, an invertible matrix and an invertible scalar preserve
the nonzero coordinate vector.  This proves gradient nonvanishing at all
actual projective points, over an arbitrary field of characteristic not two.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open MvPolynomial TopologicalSpace

variable {K : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The formal partial derivatives of a symmetric matrix quadratic. -/
theorem pderiv_matrixQuadraticPolynomial {n : Type*} [Fintype n]
    (R : Matrix n n K) (hR : R.IsSymm) (i : n) :
    pderiv i (matrixQuadraticPolynomial R) =
      C (2 : K) * ∑ j, C (R i j) * X j := by
  classical
  simp only [matrixQuadraticPolynomial, map_sum, pderiv_mul, pderiv_C,
    pderiv_X, Pi.single_apply, zero_mul, zero_add, mul_ite, mul_one,
    mul_zero, ite_mul, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true,
    show ∀ j, R j i = R i j from fun j => hR.apply i j]
  simp only [map_ofNat]
  ring

/-- If all partial derivatives vanish in an ideal, every coordinate belongs
to that ideal. No primality or algebraic closedness is needed. -/
theorem X_mem_ideal_of_matrixQuadraticPolynomial_gradient
    (h2 : (2 : K) ≠ 0) (R : Matrix (Fin 3) (Fin 3) K)
    (hR : R.IsSymm) (hdet : R.det ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) K))
    (hgrad : ∀ j, pderiv j (matrixQuadraticPolynomial R) ∈ I) :
    ∀ i : Fin 3, X i ∈ I := by
  classical
  let f : K →+* MvPolynomial (Fin 3) K ⧸ I := (Ideal.Quotient.mk I).comp C
  let v : Fin 3 → MvPolynomial (Fin 3) K ⧸ I :=
    fun i => Ideal.Quotient.mk I (X i)
  have hunit : IsUnit (f.mapMatrix R) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [← f.map_det]
    exact (isUnit_iff_ne_zero.mpr hdet).map f
  have hrows : (f.mapMatrix R).mulVec v = 0 := by
    funext i
    have hi := Ideal.Quotient.eq_zero_iff_mem.mpr (hgrad i)
    rw [pderiv_matrixQuadraticPolynomial R hR i, map_mul, map_sum] at hi
    have htwo : IsUnit (f (2 : K)) := (isUnit_iff_ne_zero.mpr h2).map f
    apply htwo.mul_right_eq_zero.mp
    simpa only [f, v, RingHom.comp_apply, Matrix.mulVec, dotProduct,
      RingHom.mapMatrix_apply, Matrix.map_apply, map_mul] using hi
  have hv : v = 0 := Matrix.mulVec_injective_of_isUnit hunit
    (hrows.trans (Matrix.mulVec_zero _).symm)
  intro i
  exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hv i)

/-- A nondegenerate symmetric ternary quadratic has no projective zero of
its gradient over any field in which two is nonzero. -/
theorem matrixQuadraticPolynomial_projective_gradient
    (h2 : (2 : K) ≠ 0) (R : Matrix (Fin 3) (Fin 3) K)
    (hR : R.IsSymm) (hdet : R.det ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Fin 3) K)) :
    ∃ j : Fin 3, pderiv j (matrixQuadraticPolynomial R) ∉
      p.asHomogeneousIdeal.toIdeal := by
  classical
  by_contra! hgrad
  have hX := X_mem_ideal_of_matrixQuadraticPolynomial_gradient
    h2 R hR hdet p.asHomogeneousIdeal.toIdeal hgrad
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show p ∈ iSup (planeCoordinateOpen K) by
      rw [planeCoordinateOpen_cover]; trivial)
  exact hi (hX i)

end EvenQuinticConic.Incidence
