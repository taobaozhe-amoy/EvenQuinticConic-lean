import EvenQuinticConic.QuadraticTraceZero
import Mathlib.RingTheory.Trace.Basic

/-! # Actual algebra changes of coordinates and trace-zero generators -/
noncomputable section
namespace EvenQuinticConic
variable {R : Type*} [CommRing R]

/-- The local coefficient identity follows from preservation of actual multiplication. -/
theorem kummer_parameter_change {u v : R}
    (f : KummerAlgebra u →ₐ[R] KummerAlgebra v) (c : R)
    (hf : f (kummerGenerator u) = c • kummerGenerator v) :
    u = v * (c * c) := by
  have h := congrArg f (kummerGenerator_sq u)
  rw [map_mul, hf, f.commutes] at h
  have hr := congrArg QuadraticAlgebra.re h
  simpa [kummerGenerator, QuadraticAlgebra.algebraMap_eq, mul_assoc, mul_comm,
    mul_left_comm] using hr.symm

/-- Trace is preserved by actual isomorphisms of the local quadratic algebras. -/
theorem kummer_trace_map {u v : R} (e : KummerAlgebra u ≃ₐ[R] KummerAlgebra v)
    (x : KummerAlgebra u) :
    Algebra.trace R (KummerAlgebra v) (e x) = Algebra.trace R (KummerAlgebra u) x :=
  Algebra.trace_eq_of_algEquiv e x

variable [Invertible (2 : R)]

/-- No scalar summand can occur in the image of a trace-zero generator. -/
theorem kummer_map_generator {u v : R}
    (e : KummerAlgebra u ≃ₐ[R] KummerAlgebra v) :
    e (kummerGenerator u) = (e (kummerGenerator u)).im • kummerGenerator v := by
  have hz : (e (kummerGenerator u)).re = 0 := by
    apply (kummer_trace_zero_iff v _).mp
    rw [kummer_trace_map, kummer_trace]
    simp [kummerGenerator]
  apply QuadraticAlgebra.ext
  · simpa only [QuadraticAlgebra.re_smul, kummerGenerator, smul_eq_mul, mul_zero] using hz
  · simp [kummerGenerator]

/-- The inverse algebra map gives the actual inverse of the generator coefficient. -/
theorem kummer_generator_coeff_inv {u v : R}
    (e : KummerAlgebra u ≃ₐ[R] KummerAlgebra v) :
    (e (kummerGenerator u)).im * (e.symm (kummerGenerator v)).im = 1 := by
  have h := congrArg QuadraticAlgebra.im (e.apply_symm_apply (kummerGenerator v))
  rw [kummer_map_generator e.symm, map_smul, kummer_map_generator e] at h
  simpa [kummerGenerator, mul_comm] using h

/-- A genuine algebra isomorphism constructs its trace-zero transition unit. -/
def kummerChangeUnit {u v : R} (e : KummerAlgebra u ≃ₐ[R] KummerAlgebra v) : Rˣ where
  val := (e (kummerGenerator u)).im
  inv := (e.symm (kummerGenerator v)).im
  val_inv := kummer_generator_coeff_inv e
  inv_val := by rw [mul_comm]; exact kummer_generator_coeff_inv e

/-- The square coefficient transformation is derived from the algebra isomorphism. -/
theorem kummerChangeUnit_square {u v : R}
    (e : KummerAlgebra u ≃ₐ[R] KummerAlgebra v) :
    u = v * ((kummerChangeUnit e : R) * (kummerChangeUnit e : R)) :=
  kummer_parameter_change e.toAlgHom _ (kummer_map_generator e)

/-- Composition of actual chart isomorphisms gives the expected unit cocycle law. -/
theorem kummerChangeUnit_trans {u v w : R}
    (e : KummerAlgebra u ≃ₐ[R] KummerAlgebra v)
    (f : KummerAlgebra v ≃ₐ[R] KummerAlgebra w) :
    kummerChangeUnit (e.trans f) = kummerChangeUnit e * kummerChangeUnit f := by
  apply Units.ext
  change (f (e (kummerGenerator u))).im =
    (e (kummerGenerator u)).im * (f (kummerGenerator v)).im
  rw [kummer_map_generator e, map_smul]
  simp [kummerGenerator]

/-- The actual algebra isomorphism restricts to an isomorphism of trace kernels. -/
def kummerTraceZeroMapEquiv {u v : R}
    (e : KummerAlgebra u ≃ₐ[R] KummerAlgebra v) :
    KummerTraceZero u ≃ₗ[R] KummerTraceZero v where
  toFun x := ⟨e x.val, by
    change Algebra.trace R (KummerAlgebra v) (e x.val) = 0
    rw [kummer_trace_map]
    exact x.property⟩
  invFun y := ⟨e.symm y.val, by
    change Algebra.trace R (KummerAlgebra u) (e.symm y.val) = 0
    rw [kummer_trace_map]
    exact y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val
  map_add' x y := by apply Subtype.ext; exact map_add e x.val y.val
  map_smul' r x := by apply Subtype.ext; exact map_smul e r x.val

/-- Its actual trace-zero coordinate transformation is the constructed unit. -/
theorem kummerTraceZeroMapEquiv_coordinate {u v : R}
    (e : KummerAlgebra u ≃ₐ[R] KummerAlgebra v) (x : KummerTraceZero u) :
    kummerTraceZeroCoordinate v (kummerTraceZeroMapEquiv e x) =
      (kummerChangeUnit e : R) * kummerTraceZeroCoordinate u x := by
  have hx : x.val = x.val.im • kummerGenerator u := by
    apply QuadraticAlgebra.ext
    · simpa only [QuadraticAlgebra.re_smul, kummerGenerator, smul_eq_mul, mul_zero] using
        (kummer_trace_zero_iff u x.val).mp x.property
    · simp [kummerGenerator]
  change (e x.val).im = (e (kummerGenerator u)).im * x.val.im
  calc
    (e x.val).im = (e (x.val.im • kummerGenerator u)).im := congrArg _ (congrArg e hx)
    _ = _ := by simp [mul_comm]

end EvenQuinticConic
