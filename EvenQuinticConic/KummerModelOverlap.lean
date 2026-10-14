import EvenQuinticConic.KummerBaseChange
import EvenQuinticConic.QuadraticTraceZeroTransition

/-!
# Overlaps of actual Kummer models

Two models of one algebra determine their coordinate comparison without an
additional overlap hypothesis. Their transition units satisfy the square
and cocycle identities, and commute with extension of scalars.
-/
noncomputable section
open scoped TensorProduct
namespace EvenQuinticConic

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {u v w : R}

/-- Coordinate change from model `j` to model `i`, through their common algebra. -/
def kummerModelOverlap (ei : A ≃ₐ[R] KummerAlgebra u)
    (ej : A ≃ₐ[R] KummerAlgebra v) : KummerAlgebra v ≃ₐ[R] KummerAlgebra u :=
  ej.symm.trans ei

@[simp] theorem kummerModelOverlap_apply (ei : A ≃ₐ[R] KummerAlgebra u)
    (ej : A ≃ₐ[R] KummerAlgebra v) (x : A) :
    kummerModelOverlap ei ej (ej x) = ei x := by
  simp [kummerModelOverlap]

/-- Three coordinate comparisons compose through the actual common algebra. -/
theorem kummerModelOverlap_cocycle (ei : A ≃ₐ[R] KummerAlgebra u)
    (ej : A ≃ₐ[R] KummerAlgebra v) (ek : A ≃ₐ[R] KummerAlgebra w) :
    (kummerModelOverlap ej ek).trans (kummerModelOverlap ei ej) =
      kummerModelOverlap ei ek := by
  apply AlgEquiv.ext
  intro x
  simp [kummerModelOverlap]

variable [Invertible (2 : R)]

/-- The imaginary coefficient changes by the transition unit for every element. -/
theorem kummer_equiv_im {u v : R} (e : KummerAlgebra u ≃ₐ[R] KummerAlgebra v)
    (x : KummerAlgebra u) :
    (e x).im = (kummerChangeUnit e : R) * x.im := by
  have hx : x = algebraMap R (KummerAlgebra u) x.re + x.im • kummerGenerator u := by
    ext <;> simp [QuadraticAlgebra.algebraMap_eq, kummerGenerator]
  conv_lhs => rw [hx, map_add, e.commutes, map_smul, kummer_map_generator]
  simp [QuadraticAlgebra.algebraMap_eq, kummerGenerator, kummerChangeUnit, mul_comm]

/-- The unit extracted from the overlap is the actual change of coefficients. -/
theorem kummerModelOverlap_coordinate (ei : A ≃ₐ[R] KummerAlgebra u)
    (ej : A ≃ₐ[R] KummerAlgebra v) (x : A) :
    (ei x).im = (kummerChangeUnit (kummerModelOverlap ei ej) : R) * (ej x).im := by
  simpa using kummer_equiv_im (kummerModelOverlap ei ej) (ej x)

/-- Parameter compatibility follows from multiplication in the common algebra. -/
theorem kummerModelOverlap_changeUnit_square (ei : A ≃ₐ[R] KummerAlgebra u)
    (ej : A ≃ₐ[R] KummerAlgebra v) :
    v = u * ((kummerChangeUnit (kummerModelOverlap ei ej) : R) *
      (kummerChangeUnit (kummerModelOverlap ei ej) : R)) :=
  kummerChangeUnit_square (kummerModelOverlap ei ej)

/-- The units are a cocycle, rather than additional input data. -/
theorem kummerModelOverlap_changeUnit_cocycle (ei : A ≃ₐ[R] KummerAlgebra u)
    (ej : A ≃ₐ[R] KummerAlgebra v) (ek : A ≃ₐ[R] KummerAlgebra w) :
    kummerChangeUnit (kummerModelOverlap ei ek) =
      kummerChangeUnit (kummerModelOverlap ei ej) *
        kummerChangeUnit (kummerModelOverlap ej ek) := by
  rw [← kummerModelOverlap_cocycle ei ej ek, kummerChangeUnit_trans, mul_comm]

variable (S : Type*) [CommRing S] [Algebra R S] [Invertible (2 : S)]

/-- The overlap unit is preserved by extension of scalars. -/
theorem kummerModelOverlap_changeUnit_baseChange (ei : A ≃ₐ[R] KummerAlgebra u)
    (ej : A ≃ₐ[R] KummerAlgebra v) :
    kummerChangeUnit
      (kummerModelOverlap (kummerModelBaseChange S ei) (kummerModelBaseChange S ej)) =
      Units.map (algebraMap R S) (kummerChangeUnit (kummerModelOverlap ei ej)) := by
  have hg : (kummerModelBaseChange S ej).symm (kummerGenerator (algebraMap R S v)) =
      1 ⊗ₜ[R] ej.symm (kummerGenerator v) := by
    apply (kummerModelBaseChange S ej).injective
    rw [AlgEquiv.apply_symm_apply]
    ext <;> simp [kummerGenerator]
  apply Units.ext
  change ((kummerModelBaseChange S ei)
    ((kummerModelBaseChange S ej).symm (kummerGenerator (algebraMap R S v)))).im =
      algebraMap R S (ei (ej.symm (kummerGenerator v))).im
  rw [hg]
  simp

end EvenQuinticConic
