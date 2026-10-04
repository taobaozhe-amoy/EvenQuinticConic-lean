import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Ring

/-!
# Coefficients of genuine pairings of rank-one modules

Frames are actual linear equivalences and the pairing is an actual bilinear
map.  Its coefficient is a unit when its induced tensor-product map is
bijective.  No geometric existence of a frame or pairing is asserted here.
-/

open scoped TensorProduct

namespace EvenQuinticConic

universe u v w

variable {A : Type u} [CommRing A]
  {M : Type v} [AddCommGroup M] [Module A M]
  {P : Type w} [AddCommGroup P] [Module A P]

/-- A bilinear pairing in rank-one frames is multiplication by its value on
the two frame generators. -/
theorem rankOnePairing_apply (e : M ≃ₗ[A] A) (f : P ≃ₗ[A] A)
    (β : M →ₗ[A] M →ₗ[A] P) (s t : M) :
    f (β s t) = f (β (e.symm 1) (e.symm 1)) * e s * e t := by
  have hs : s = e s • e.symm 1 := by
    apply e.injective
    simp
  have ht : t = e t • e.symm 1 := by
    apply e.injective
    simp
  calc
    f (β s t) = f (β (e s • e.symm 1) (e t • e.symm 1)) := by rw [← hs, ← ht]
    _ = f (β (e.symm 1) (e.symm 1)) * e s * e t := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring

/-- The square case of the frame formula. -/
theorem rankOnePairing_square (e : M ≃ₗ[A] A) (f : P ≃ₗ[A] A)
    (β : M →ₗ[A] M →ₗ[A] P) (s : M) :
    f (β s s) = f (β (e.symm 1) (e.symm 1)) * (e s) ^ 2 := by
  rw [rankOnePairing_apply e f β s s, pow_two, mul_assoc]

/-- An actual linear automorphism of a ring, viewed as a module over itself,
sends `1` to a unit. -/
theorem linearEquiv_self_apply_one_isUnit (g : A ≃ₗ[A] A) : IsUnit (g 1) := by
  apply IsUnit.isUnit_iff_mulRight_bijective.mpr
  have h : (fun a : A ↦ a * g 1) = g := by
    funext a
    simpa only [smul_eq_mul, mul_one] using (g.map_smul a (1 : A)).symm
  rw [h]
  exact g.bijective

/-- A perfect bilinear pairing of rank-one modules has a unit coefficient
in any pair of frames.  Perfection is the bijectivity of the actual induced
map on the tensor product. -/
theorem rankOnePairing_coefficient_isUnit (e : M ≃ₗ[A] A) (f : P ≃ₗ[A] A)
    (β : M →ₗ[A] M →ₗ[A] P) (hβ : Function.Bijective (TensorProduct.lift β)) :
    IsUnit (f (β (e.symm 1) (e.symm 1))) := by
  let tensorFrame : M ⊗[A] M ≃ₗ[A] A :=
    (TensorProduct.congr e e).trans (TensorProduct.lid A A)
  let g : A ≃ₗ[A] A :=
    (tensorFrame.symm.trans (LinearEquiv.ofBijective (TensorProduct.lift β) hβ)).trans f
  have hg := linearEquiv_self_apply_one_isUnit g
  simpa [g, tensorFrame] using hg

end EvenQuinticConic
