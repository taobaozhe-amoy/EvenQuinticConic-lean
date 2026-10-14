import EvenQuinticConic.QuadraticTraceZero
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Actual base change of Kummer algebras

The tensor product of a Kummer algebra with a commutative base algebra is
identified with the Kummer algebra of the image parameter. The equivalence
preserves the actual multiplication and has explicit coefficient formulas.
-/
noncomputable section
open scoped TensorProduct
namespace EvenQuinticConic

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]

/-- Base change of the basis `(1,t)`, expressed in the target quadratic coordinates. -/
def kummerBaseChangeLinearEquiv (u : R) :
    S ⊗[R] KummerAlgebra u ≃ₗ[S] KummerAlgebra (algebraMap R S u) :=
  ((QuadraticAlgebra.basis u 0).baseChange S).equivFun.trans
    (QuadraticAlgebra.linearEquivTuple (algebraMap R S u) 0).symm

@[simp] theorem kummerBaseChangeLinearEquiv_tmul (u : R) (s : S) (x : KummerAlgebra u) :
    kummerBaseChangeLinearEquiv S u (s ⊗ₜ[R] x) =
      ⟨s * algebraMap R S x.re, s * algebraMap R S x.im⟩ := by
  ext <;> simp [kummerBaseChangeLinearEquiv, Module.Basis.equivFun_apply,
    Algebra.smul_def, mul_comm]

/-- The actual algebra equivalence after extension of scalars. -/
def kummerBaseChangeEquiv (u : R) :
    S ⊗[R] KummerAlgebra u ≃ₐ[S] KummerAlgebra (algebraMap R S u) :=
  AlgEquiv.ofLinearEquiv (kummerBaseChangeLinearEquiv S u)
    (by
      rw [Algebra.TensorProduct.one_def, kummerBaseChangeLinearEquiv_tmul]
      change (⟨1 * algebraMap R S 1, 1 * algebraMap R S 0⟩ :
        KummerAlgebra (algebraMap R S u)) = ⟨1, 0⟩
      ext <;> simp)
    (by
      intro x y
      induction x with
      | zero => simp
      | tmul s a =>
        induction y with
        | zero => simp
        | tmul t b =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp only [kummerBaseChangeLinearEquiv_tmul]
          ext <;> simp <;> ring
        | add y z hy hz => simp [mul_add, hy, hz]
      | add x z hx hz => simp [add_mul, hx, hz])

@[simp] theorem kummerBaseChangeEquiv_tmul_re (u : R) (s : S) (x : KummerAlgebra u) :
    (kummerBaseChangeEquiv S u (s ⊗ₜ[R] x)).re = s * algebraMap R S x.re := by
  change (kummerBaseChangeLinearEquiv S u (s ⊗ₜ[R] x)).re = _
  rw [kummerBaseChangeLinearEquiv_tmul]

@[simp] theorem kummerBaseChangeEquiv_tmul_im (u : R) (s : S) (x : KummerAlgebra u) :
    (kummerBaseChangeEquiv S u (s ⊗ₜ[R] x)).im = s * algebraMap R S x.im := by
  change (kummerBaseChangeLinearEquiv S u (s ⊗ₜ[R] x)).im = _
  rw [kummerBaseChangeLinearEquiv_tmul]

@[simp] theorem kummerBaseChangeEquiv_generator (u : R) :
    kummerBaseChangeEquiv S u (1 ⊗ₜ[R] kummerGenerator u) =
      kummerGenerator (algebraMap R S u) := by
  ext <;> simp [kummerGenerator]

variable {A : Type*} [CommRing A] [Algebra R A] {u : R}

/-- Any actual Kummer model induces a model of the scalar extension. -/
def kummerModelBaseChange (e : A ≃ₐ[R] KummerAlgebra u) :
    S ⊗[R] A ≃ₐ[S] KummerAlgebra (algebraMap R S u) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e).trans
    (kummerBaseChangeEquiv S u)

@[simp] theorem kummerModelBaseChange_tmul_re (e : A ≃ₐ[R] KummerAlgebra u)
    (s : S) (x : A) :
    (kummerModelBaseChange S e (s ⊗ₜ[R] x)).re = s * algebraMap R S (e x).re := by
  simp [kummerModelBaseChange]

@[simp] theorem kummerModelBaseChange_tmul_im (e : A ≃ₐ[R] KummerAlgebra u)
    (s : S) (x : A) :
    (kummerModelBaseChange S e (s ⊗ₜ[R] x)).im = s * algebraMap R S (e x).im := by
  simp [kummerModelBaseChange]

end EvenQuinticConic
