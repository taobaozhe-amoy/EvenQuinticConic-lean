import EvenQuinticConic.KummerBaseChange
import EvenQuinticConic.KummerScalarMap
import EvenQuinticConic.KummerModelOverlap

/-! # Restricting actual Kummer models along a scalar tower -/
noncomputable section
open scoped TensorProduct
namespace EvenQuinticConic
variable (R S T A : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra R A]

/-- The canonical map between two base changes along a scalar tower. -/
def tensorBaseChangeRestriction : S ⊗[R] A →ₐ[R] T ⊗[R] A :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R A)

/-- The canonical tensor restriction is the unit tensor followed by cancellation. -/
theorem tensorBaseChangeRestriction_eq (x : S ⊗[R] A) :
    tensorBaseChangeRestriction R S T A x =
      Algebra.TensorProduct.cancelBaseChange R S T T A (1 ⊗ₜ[S] x) := by
  induction x with
  | zero => simp
  | tmul s a => simp [tensorBaseChangeRestriction, Algebra.smul_def]
  | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]

/-- The canonical restriction is the identity for an unchanged coefficient ring. -/
theorem tensorBaseChangeRestriction_self :
    tensorBaseChangeRestriction R S S A = AlgHom.id R (S ⊗[R] A) := by
  apply AlgHom.ext
  intro x
  induction x with
  | zero => simp
  | tmul s a => simp [tensorBaseChangeRestriction]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Canonical restrictions compose along a compatible tower of coefficient rings. -/
theorem tensorBaseChangeRestriction_comp
    (U : Type*) [CommRing U] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower R S U] [IsScalarTower R T U] [IsScalarTower S T U] :
    (tensorBaseChangeRestriction R T U A).comp (tensorBaseChangeRestriction R S T A) =
      tensorBaseChangeRestriction R S U A := by
  apply AlgHom.ext
  intro x
  induction x with
  | zero => simp
  | tmul s a =>
    simp [tensorBaseChangeRestriction, ← IsScalarTower.algebraMap_apply S T U]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

variable {R S T A}

/-- A model over S gives a model over T of the original algebra's base change. -/
def kummerModelRestrict {u : S} (e : S ⊗[R] A ≃ₐ[S] KummerAlgebra u) :
    T ⊗[R] A ≃ₐ[T] KummerAlgebra (algebraMap S T u) :=
  (Algebra.TensorProduct.cancelBaseChange R S T T A).symm.trans
    (kummerModelBaseChange T e)

/-- Restriction of model coordinates is exactly the scalar ring map. -/
theorem kummerModelRestrict_naturality {u : S}
    (e : S ⊗[R] A ≃ₐ[S] KummerAlgebra u) (x : S ⊗[R] A) :
    kummerModelRestrict (T := T) e (tensorBaseChangeRestriction R S T A x) =
      kummerScalarMap (algebraMap S T) u (e x) := by
  rw [tensorBaseChangeRestriction_eq]
  change kummerModelBaseChange T e
    ((Algebra.TensorProduct.cancelBaseChange R S T T A).symm
      (Algebra.TensorProduct.cancelBaseChange R S T T A (1 ⊗ₜ[S] x))) = _
  rw [AlgEquiv.symm_apply_apply]
  ext <;> simp

/-- The actual algebra trace commutes with restriction under a Kummer model. -/
theorem kummerModelRestrict_trace {u : S}
    (e : S ⊗[R] A ≃ₐ[S] KummerAlgebra u) (x : S ⊗[R] A) :
    Algebra.trace T (T ⊗[R] A) (tensorBaseChangeRestriction R S T A x) =
      algebraMap S T (Algebra.trace S (S ⊗[R] A) x) := by
  rw [← Algebra.trace_eq_of_algEquiv (kummerModelRestrict (T := T) e),
    kummerModelRestrict_naturality, kummerScalarMap_trace,
    Algebra.trace_eq_of_algEquiv e]

/-- The common cancellation equivalence cancels from overlap comparisons. -/
theorem kummerModelRestrict_overlap {u v : S}
    (ei : S ⊗[R] A ≃ₐ[S] KummerAlgebra u)
    (ej : S ⊗[R] A ≃ₐ[S] KummerAlgebra v) :
    kummerModelOverlap (kummerModelRestrict (T := T) ei) (kummerModelRestrict (T := T) ej) =
      kummerModelOverlap (R := T) (A := T ⊗[S] (S ⊗[R] A))
        (kummerModelBaseChange T ei) (kummerModelBaseChange T ej) := by
  apply AlgEquiv.ext
  intro x
  simp [kummerModelOverlap, kummerModelRestrict]

/-- Restricting the two models restricts their extracted overlap unit. -/
theorem kummerModelRestrict_changeUnit [Invertible (2 : S)] [Invertible (2 : T)]
    {u v : S} (ei : S ⊗[R] A ≃ₐ[S] KummerAlgebra u)
    (ej : S ⊗[R] A ≃ₐ[S] KummerAlgebra v) :
    kummerChangeUnit
      (kummerModelOverlap (kummerModelRestrict (T := T) ei) (kummerModelRestrict (T := T) ej)) =
      Units.map (algebraMap S T) (kummerChangeUnit (kummerModelOverlap ei ej)) := by
  rw [kummerModelRestrict_overlap, kummerModelOverlap_changeUnit_baseChange]

end EvenQuinticConic
