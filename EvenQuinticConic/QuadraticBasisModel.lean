import EvenQuinticConic.KummerUnramified
import Mathlib.Tactic.LinearCombination

/-!
# Constructing a unit Kummer model from an actual algebra basis

A basis (1,e), invertibility of two, and actual formal unramifiedness suffice.
No quadratic multiplication coefficients or unit discriminant are inputs.
The existence of such bases on a cover is still a separate geometric step.
-/
noncomputable section
namespace EvenQuinticConic
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (v : Module.Basis (Fin 2) R A)

/-- The multiplication coefficients are read from the actual product e*e. -/
def quadraticBasisConstant : R := v.repr (v 1 * v 1) 0

def quadraticBasisLinear : R := v.repr (v 1 * v 1) 1

/-- Basis coordinates construct the underlying linear equivalence. -/
def quadraticBasisLinearEquiv :
    QuadraticAlgebra R (quadraticBasisConstant v) (quadraticBasisLinear v) ≃ₗ[R] A :=
  (QuadraticAlgebra.linearEquivTuple _ _).trans v.equivFun.symm

theorem quadraticBasisLinearEquiv_apply (h0 : v 0 = 1)
    (x : QuadraticAlgebra R (quadraticBasisConstant v) (quadraticBasisLinear v)) :
    quadraticBasisLinearEquiv v x = algebraMap R A x.re + algebraMap R A x.im * v 1 := by
  simp [quadraticBasisLinearEquiv, Fin.sum_univ_two, h0, Algebra.smul_def]

theorem quadraticBasis_generator_square (h0 : v 0 = 1) :
    v 1 * v 1 = algebraMap R A (quadraticBasisConstant v) +
      algebraMap R A (quadraticBasisLinear v) * v 1 := by
  simpa [Fin.sum_univ_two, h0, Algebra.smul_def, quadraticBasisConstant,
    quadraticBasisLinear] using (v.sum_repr (v 1 * v 1)).symm

/-- The quadratic model is an actual algebra isomorphism, not only a linear one. -/
def quadraticBasisAlgEquiv (h0 : v 0 = 1) :
    QuadraticAlgebra R (quadraticBasisConstant v) (quadraticBasisLinear v) ≃ₐ[R] A :=
  AlgEquiv.ofLinearEquiv (quadraticBasisLinearEquiv v)
    (by
      rw [quadraticBasisLinearEquiv_apply v h0]
      change algebraMap R A 1 + algebraMap R A 0 * v 1 = 1
      simp)
    (by
      intro x y
      simp only [quadraticBasisLinearEquiv_apply v h0, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, map_add, map_mul]
      linear_combination -algebraMap R A x.im * algebraMap R A y.im *
        quadraticBasis_generator_square v h0)

/-- Formal unramifiedness derives the unit parameter of the constructed model. -/
theorem quadraticBasis_centered_isUnit (h0 : v 0 = 1) [Invertible (2 : R)]
    [Algebra.FormallyUnramified R A] :
    IsUnit (quadraticCenteredParameter (quadraticBasisConstant v) (quadraticBasisLinear v)) := by
  letI := Algebra.FormallyUnramified.of_equiv (quadraticBasisAlgEquiv v h0).symm
  exact quadraticCenteredParameter_isUnit _ _

/-- A rank-two algebra with the displayed basis has a unit Kummer model.
The hypothesis is actual formal unramifiedness, hence is available for étale algebras. -/
theorem exists_unit_kummer_model_of_basis (h0 : v 0 = 1) [Invertible (2 : R)]
    [Algebra.FormallyUnramified R A] :
    ∃ u : Rˣ, Nonempty (A ≃ₐ[R] KummerAlgebra (u : R)) := by
  obtain ⟨u, hu⟩ := quadraticBasis_centered_isUnit v h0
  refine ⟨u, ⟨?_⟩⟩
  rw [hu]
  exact (quadraticBasisAlgEquiv v h0).symm.trans
    (quadraticNormalForm (quadraticBasisConstant v) (quadraticBasisLinear v))

end EvenQuinticConic
