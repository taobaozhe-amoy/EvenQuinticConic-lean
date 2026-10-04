import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.Ring

/-!
# A field extension and a common square-root twist

If a generic trivialization identifies products of sections with
`u * α * β`, a square root of `u` need not belong to the function field.
This file constructs an injective linear map into a polynomial ring over
a field extension.  Its products reproduce precisely that common twist.
The polynomial variable retains the degree of the corresponding sections.

These are algebraic constructions for arbitrary fields and coefficient
families.  The geometric generic trivialization and its restriction kernel
are not constructed here.
-/

namespace EvenQuinticConic

open Polynomial

section Extension

variable (K L E : Type*) [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

/-- Embed coefficients after multiplying by a common square-root twist and
by a polynomial variable.  The map is linear over the original base field. -/
noncomputable def squareTwistedLinearMap (v : E) : L →ₗ[K] E[X] :=
  (LinearMap.mulRight K (C v * X)).comp
    ((CAlgHom : E →ₐ[K] E[X]).comp (IsScalarTower.toAlgHom K L E)).toLinearMap

@[simp]
theorem squareTwistedLinearMap_apply (v : E) (α : L) :
    squareTwistedLinearMap K L E v α = C (algebraMap L E α * v) * X := by
  simp [squareTwistedLinearMap, map_mul, mul_assoc]

/-- Nonzero twisting cannot destroy independence over the original field. -/
theorem squareTwistedLinearMap_injective (v : E) (hv : v ≠ 0) :
    Function.Injective (squareTwistedLinearMap K L E v) := by
  intro α β h
  simp only [squareTwistedLinearMap_apply] at h
  have hcoeff := C_injective (mul_right_cancel₀ X_ne_zero h)
  exact (algebraMap L E).injective (mul_right_cancel₀ hv hcoeff)

/-- This statement preserves independence over `K`, not over the extension
field `E`, where the images would all lie in the one-dimensional span of `X`. -/
theorem squareTwistedLinearMap_linearIndependent {ι : Type*}
    (v : E) (hv : v ≠ 0) (α : ι → L) (hα : LinearIndependent K α) :
    LinearIndependent K (fun i => squareTwistedLinearMap K L E v (α i)) := by
  exact hα.map' (squareTwistedLinearMap K L E v)
    (LinearMap.ker_eq_bot.mpr (squareTwistedLinearMap_injective K L E v hv))

/-- The product of two embedded coefficients has exactly the prescribed
common twist `u`, including the polynomial degree two. -/
theorem squareTwistedLinearMap_mul (u : L) (v : E)
    (hv : v ^ 2 = algebraMap L E u) (α β : L) :
    squareTwistedLinearMap K L E v α * squareTwistedLinearMap K L E v β =
      C (algebraMap L E (u * α * β)) * X ^ 2 := by
  simp only [squareTwistedLinearMap_apply, map_mul]
  calc
    C (algebraMap L E α) * C v * X * (C (algebraMap L E β) * C v * X) =
        C (v ^ 2) * C (algebraMap L E α) * C (algebraMap L E β) * X ^ 2 := by
      rw [map_pow]
      ring
    _ = _ := by rw [hv]

/-- The square identity is a special case of the product identity. -/
theorem squareTwistedLinearMap_sq (u : L) (v : E)
    (hv : v ^ 2 = algebraMap L E u) (α : L) :
    (squareTwistedLinearMap K L E v α) ^ 2 =
      C (algebraMap L E (u * α ^ 2)) * X ^ 2 := by
  simpa only [pow_two, mul_assoc] using squareTwistedLinearMap_mul K L E u v hv α α

end Extension

section AlgebraicClosure

variable (L : Type*) [Field L]

/-- A nonzero scalar has a nonzero square root in a genuine field extension.
No assertion that this root lies in the original field is made. -/
theorem exists_nonzero_square_root_in_algebraicClosure (u : L) (hu : u ≠ 0) :
    ∃ v : AlgebraicClosure L,
      v ≠ 0 ∧ v ^ 2 = algebraMap L (AlgebraicClosure L) u := by
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap L (AlgebraicClosure L) u) (by decide : 0 < 2)
  refine ⟨v, ?_, hv⟩
  intro hv0
  have hmap : algebraMap L (AlgebraicClosure L) u = 0 := by
    simpa [hv0] using hv.symm
  exact hu ((algebraMap L (AlgebraicClosure L)).injective (by simpa using hmap))

end AlgebraicClosure

section BaseFieldIndependence

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- Recording degree with a polynomial variable preserves every independent
coefficient family over the original base field. -/
theorem linearIndependent_C_mul_X {ι : Type*} (α : ι → L)
    (hα : LinearIndependent K α) :
    LinearIndependent K (fun i => (C (α i) * X : L[X])) := by
  simpa using squareTwistedLinearMap_linearIndependent K L L 1 one_ne_zero α hα

/-- An explicit actual domain model realizes twisted products after extending
the coefficient field.  The map is injective and `K`-linear; its codomain is
the polynomial ring over the genuine field `AlgebraicClosure L`. -/
theorem exists_injective_linearMap_with_twisted_products (u : L) (hu : u ≠ 0) :
    ∃ f : L →ₗ[K] (AlgebraicClosure L)[X],
      Function.Injective f ∧
      ∀ α β : L, f α * f β =
        C (algebraMap L (AlgebraicClosure L) (u * α * β)) * X ^ 2 := by
  obtain ⟨v, hv0, hv⟩ := exists_nonzero_square_root_in_algebraicClosure L u hu
  exact ⟨squareTwistedLinearMap K L (AlgebraicClosure L) v,
    squareTwistedLinearMap_injective K L (AlgebraicClosure L) v hv0,
    squareTwistedLinearMap_mul K L (AlgebraicClosure L) u v hv⟩

end BaseFieldIndependence

end EvenQuinticConic
