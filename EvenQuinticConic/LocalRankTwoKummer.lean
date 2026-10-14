import EvenQuinticConic.RankTwoUnitBasis
import Mathlib.RingTheory.LocalRing.Module

/-!
# Kummer models for finite flat rank-two algebras over local rings

The algebra, finite-module property, flatness, rank two, formal unramifiedness,
and invertibility of two are the inputs. No algebra basis is supplied.
-/
noncomputable section
open scoped TensorProduct
namespace EvenQuinticConic
variable {R A : Type*} [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Invertible (2 : R)]
    [Module.Finite R A] [Module.Flat R A]

/-- Finite flatness over the actual local ring constructs an adapted rank-two basis. -/
theorem exists_local_rankTwo_basis_one (hrank : Module.finrank R A = 2) :
    ∃ v : Module.Basis (Fin 2) R A, v 0 = 1 := by
  letI : Module.Free R A := Module.free_of_flat_of_isLocalRing
  exact exists_rankTwo_basis_one (Module.finBasisOfFinrankEq R A hrank)

/-- A unit Kummer model with no basis or multiplication presentation as an input. -/
theorem exists_unit_kummer_model_of_local_finite_flat
    [Algebra.FormallyUnramified R A] (hrank : Module.finrank R A = 2) :
    ∃ u : Rˣ, Nonempty (A ≃ₐ[R] KummerAlgebra (u : R)) := by
  obtain ⟨v, h0⟩ := exists_local_rankTwo_basis_one hrank
  exact exists_unit_kummer_model_of_basis v h0

/-- The actual trace kernel is a free rank-one module, derived without a basis input. -/
theorem nonempty_trace_kernel_coordinate_of_local_finite_flat
    [Algebra.FormallyUnramified R A] (hrank : Module.finrank R A = 2) :
    Nonempty (LinearMap.ker (Algebra.trace R A) ≃ₗ[R] R) := by
  obtain ⟨u, ⟨e⟩⟩ := exists_unit_kummer_model_of_local_finite_flat hrank
  exact ⟨(algebraTraceKernelKummerEquiv e).trans (kummerTraceZeroCoordinate (u : R))⟩

/-- Actual algebra multiplication trivializes the trace-kernel tensor square.
Neither a basis nor a square pairing is an input. -/
theorem exists_trace_kernel_tensor_equiv_of_local_finite_flat
    [Algebra.FormallyUnramified R A] (hrank : Module.finrank R A = 2) :
    ∃ m : LinearMap.ker (Algebra.trace R A) ⊗[R] LinearMap.ker (Algebra.trace R A) ≃ₗ[R] R,
      ∀ x y : LinearMap.ker (Algebra.trace R A),
        x.val * y.val = algebraMap R A (m (x ⊗ₜ[R] y)) := by
  obtain ⟨v, h0⟩ := exists_local_rankTwo_basis_one hrank
  exact exists_trace_kernel_tensor_equiv_of_basis v h0

end EvenQuinticConic
