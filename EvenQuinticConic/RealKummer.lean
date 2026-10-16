import EvenQuinticConic.QuadraticTraceZeroTransition
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Real points and real twists of quadratic Kummer algebras

These are statements about actual quadratic algebras and algebra morphisms.
A real point is represented by an actual `ℝ`-algebra map to `ℝ`.
For a nonzero real parameter, such a map exists precisely for a positive
parameter. Two real quadratic algebras with nonzero parameters are isomorphic
precisely when the parameter ratio is positive. The forward implication uses
the actual trace-zero generator of the isomorphism, and the reverse implication
constructs both inverse algebra maps by rescaling that generator.

This supplies the local algebra and sign calculation in the comparison of
real discriminant covers. It does not construct the global discriminant covers
or identify their trace-zero line bundles or global square trivializations.
-/

noncomputable section
namespace EvenQuinticConic

section Ring
variable {R : Type*} [CommRing R]

/-- A root of the parameter gives an actual scalar-valued algebra map. -/
def kummerEvaluation (u r : R) (hr : r * r = u) : KummerAlgebra u →ₐ[R] R where
  toFun x := x.re + r * x.im
  map_zero' := by simp
  map_one' := by change (1 : R) + r * 0 = 1; simp
  map_add' x y := by simp; ring
  map_mul' x y := by simp [← hr]; ring
  commutes' x := by simp [QuadraticAlgebra.algebraMap_eq]

@[simp] theorem kummerEvaluation_generator (u r : R) (hr : r * r = u) :
    kummerEvaluation u r hr (kummerGenerator u) = r := by
  simp [kummerEvaluation, kummerGenerator]

/-- Every actual scalar-valued algebra map sends the generator to a root. -/
theorem kummerAlgHom_generator_sq {u : R} (f : KummerAlgebra u →ₐ[R] R) :
    f (kummerGenerator u) * f (kummerGenerator u) = u := by
  rw [← map_mul, kummerGenerator_sq, f.commutes]
  rfl

/-- Existence of a scalar-valued point is exactly the square-root condition. -/
theorem nonempty_kummerAlgHom_iff (u : R) :
    Nonempty (KummerAlgebra u →ₐ[R] R) ↔ ∃ r : R, r * r = u := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f (kummerGenerator u), kummerAlgHom_generator_sq f⟩
  · rintro ⟨r, hr⟩
    exact ⟨kummerEvaluation u r hr⟩

/-- A scalar-valued algebra map is determined by the image of the generator. -/
theorem kummerAlgHom_apply {u : R} (f : KummerAlgebra u →ₐ[R] R)
    (x : KummerAlgebra u) : f x = x.re + f (kummerGenerator u) * x.im := by
  have hx : x = algebraMap R (KummerAlgebra u) x.re +
      algebraMap R (KummerAlgebra u) x.im * kummerGenerator u := by
    ext <;> simp [QuadraticAlgebra.algebraMap_eq, kummerGenerator]
  calc
    f x = f (algebraMap R (KummerAlgebra u) x.re +
        algebraMap R (KummerAlgebra u) x.im * kummerGenerator u) := congrArg f hx
    _ = _ := by
      rw [map_add, map_mul, f.commutes, f.commutes]
      change x.re + x.im * f (kummerGenerator u) = x.re + f (kummerGenerator u) * x.im
      ring

/-- Scalar-valued points and scalar roots are equivalent as actual types. -/
def kummerAlgHomEquivRoots (u : R) :
    (KummerAlgebra u →ₐ[R] R) ≃ {r : R // r * r = u} where
  toFun f := ⟨f (kummerGenerator u), kummerAlgHom_generator_sq f⟩
  invFun r := kummerEvaluation u r.val r.property
  left_inv f := by
    ext x
    exact (kummerAlgHom_apply f x).symm
  right_inv r := by
    apply Subtype.ext
    exact kummerEvaluation_generator u r.val r.property

end Ring

section Field
variable {K : Type*} [Field K]

/-- The explicit change of generator `t ↦ c t`, with its explicit inverse. -/
def kummerRescaleEquiv (u v c : K) (hc : c ≠ 0) (h : u = v * (c * c)) :
    KummerAlgebra u ≃ₐ[K] KummerAlgebra v where
  toFun x := ⟨x.re, c * x.im⟩
  invFun x := ⟨x.re, x.im / c⟩
  left_inv x := by ext <;> simp [hc]
  right_inv x := by
    apply QuadraticAlgebra.ext
    · rfl
    · exact mul_div_cancel₀ x.im hc
  map_add' x y := by ext <;> simp [mul_add]
  map_mul' x y := by ext <;> simp [h] <;> ring
  commutes' r := by ext <;> simp [QuadraticAlgebra.algebraMap_eq]

@[simp] theorem kummerRescaleEquiv_generator (u v c : K) (hc : c ≠ 0)
    (h : u = v * (c * c)) :
    kummerRescaleEquiv u v c hc h (kummerGenerator u) = c • kummerGenerator v := by
  ext <;> simp [kummerRescaleEquiv, kummerGenerator]

end Field

/-- No nonzero-parameter assumption is needed for this nonnegative version. -/
theorem real_kummer_point_iff_nonneg (u : ℝ) :
    Nonempty (KummerAlgebra u →ₐ[ℝ] ℝ) ↔ 0 ≤ u := by
  rw [nonempty_kummerAlgHom_iff]
  constructor
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact mul_self_nonneg r
  · intro hu
    exact ⟨Real.sqrt u, Real.mul_self_sqrt hu⟩

/-- For an étale Kummer parameter, a real point forces strict positivity. -/
theorem real_kummer_point_iff_pos (u : ℝ) (hu : u ≠ 0) :
    Nonempty (KummerAlgebra u →ₐ[ℝ] ℝ) ↔ 0 < u := by
  rw [real_kummer_point_iff_nonneg]
  exact le_iff_lt_or_eq.trans (or_iff_left (Ne.symm hu))

/-- Algebra isomorphisms force a positive ratio of nonzero real parameters. -/
theorem real_kummer_ratio_pos_of_equiv {u v : ℝ} (hv : v ≠ 0)
    (e : KummerAlgebra u ≃ₐ[ℝ] KummerAlgebra v) : 0 < u / v := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let c := kummerChangeUnit e
  have hc : (c : ℝ) ≠ 0 := Units.ne_zero c
  have hs : u = v * ((c : ℝ) * (c : ℝ)) := kummerChangeUnit_square e
  rw [hs, mul_div_cancel_left₀ _ hv]
  exact mul_self_pos.mpr hc

/-- Positive ratio constructs an actual algebra isomorphism over the reals. -/
def realKummerEquivOfRatioPos (u v : ℝ) (hv : v ≠ 0) (h : 0 < u / v) :
    KummerAlgebra u ≃ₐ[ℝ] KummerAlgebra v :=
  kummerRescaleEquiv u v (Real.sqrt (u / v)) (ne_of_gt (Real.sqrt_pos.2 h)) (by
    rw [Real.mul_self_sqrt h.le]
    exact (mul_div_cancel₀ u hv).symm)

/-- The actual real-algebra isomorphism classification, with no chosen roots. -/
theorem real_kummer_equiv_iff_ratio_pos (u v : ℝ) (hv : v ≠ 0) :
    Nonempty (KummerAlgebra u ≃ₐ[ℝ] KummerAlgebra v) ↔ 0 < u / v := by
  constructor
  · rintro ⟨e⟩
    exact real_kummer_ratio_pos_of_equiv hv e
  · intro h
    exact ⟨realKummerEquivOfRatioPos u v hv h⟩

/-- Two split real fibers with nonzero parameters have positive parameter ratio. -/
theorem real_kummer_ratio_pos_of_points {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (pu : KummerAlgebra u →ₐ[ℝ] ℝ) (pv : KummerAlgebra v →ₐ[ℝ] ℝ) :
    0 < u / v :=
  div_pos ((real_kummer_point_iff_pos u hu).mp ⟨pu⟩)
    ((real_kummer_point_iff_pos v hv).mp ⟨pv⟩)

/-- In particular, the two local real algebras are actually isomorphic. -/
def realKummerEquivOfPoints {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (pu : KummerAlgebra u →ₐ[ℝ] ℝ) (pv : KummerAlgebra v →ₐ[ℝ] ℝ) :
    KummerAlgebra u ≃ₐ[ℝ] KummerAlgebra v :=
  realKummerEquivOfRatioPos u v hv (real_kummer_ratio_pos_of_points hu hv pu pv)

end EvenQuinticConic
