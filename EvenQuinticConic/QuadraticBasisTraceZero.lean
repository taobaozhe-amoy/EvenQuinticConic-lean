import EvenQuinticConic.QuadraticBasisModel
import EvenQuinticConic.QuadraticTraceZeroTransition

/-! # The actual trace kernel of a based unramified quadratic algebra -/
noncomputable section
open scoped TensorProduct
namespace EvenQuinticConic
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Any actual Kummer-model isomorphism identifies the actual algebra trace kernels. -/
def algebraTraceKernelKummerEquiv {u : R} (e : A ≃ₐ[R] KummerAlgebra u) :
    LinearMap.ker (Algebra.trace R A) ≃ₗ[R] KummerTraceZero u where
  toFun x := ⟨e x.val, by
    change Algebra.trace R (KummerAlgebra u) (e x.val) = 0
    rw [Algebra.trace_eq_of_algEquiv e]
    exact x.property⟩
  invFun y := ⟨e.symm y.val, by
    change Algebra.trace R A (e.symm y.val) = 0
    rw [Algebra.trace_eq_of_algEquiv e.symm]
    exact y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val
  map_add' x y := by apply Subtype.ext; exact map_add e x.val y.val
  map_smul' r x := by apply Subtype.ext; exact map_smul e r x.val

variable [Invertible (2 : R)]

/-- The square of the actual trace kernel is identified with the base ring. -/
def algebraTraceKernelTensorEquiv {u : Rˣ} (e : A ≃ₐ[R] KummerAlgebra (u : R)) :
    LinearMap.ker (Algebra.trace R A) ⊗[R] LinearMap.ker (Algebra.trace R A) ≃ₗ[R] R :=
  (TensorProduct.congr (algebraTraceKernelKummerEquiv e)
    (algebraTraceKernelKummerEquiv e)).trans (kummerTraceZeroTensorEquiv u)

/-- The constructed tensor isomorphism agrees with multiplication in the original algebra. -/
theorem algebraTraceKernelTensorEquiv_mul {u : Rˣ}
    (e : A ≃ₐ[R] KummerAlgebra (u : R))
    (x y : LinearMap.ker (Algebra.trace R A)) :
    x.val * y.val = algebraMap R A (algebraTraceKernelTensorEquiv e (x ⊗ₜ[R] y)) := by
  apply e.injective
  rw [map_mul, e.commutes]
  exact kummerTraceZeroTensorEquiv_mul u (algebraTraceKernelKummerEquiv e x)
    (algebraTraceKernelKummerEquiv e y)

/-- Starting with the actual basis and unramifiedness, multiplication induces
an isomorphism from the actual trace-kernel tensor square to R. -/
theorem exists_trace_kernel_tensor_equiv_of_basis
    (v : Module.Basis (Fin 2) R A) (h0 : v 0 = 1)
    [Algebra.FormallyUnramified R A] :
    ∃ m : LinearMap.ker (Algebra.trace R A) ⊗[R] LinearMap.ker (Algebra.trace R A) ≃ₗ[R] R,
      ∀ x y : LinearMap.ker (Algebra.trace R A),
        x.val * y.val = algebraMap R A (m (x ⊗ₜ[R] y)) := by
  obtain ⟨u, ⟨e⟩⟩ := exists_unit_kummer_model_of_basis v h0
  exact ⟨algebraTraceKernelTensorEquiv e, algebraTraceKernelTensorEquiv_mul e⟩

end EvenQuinticConic
