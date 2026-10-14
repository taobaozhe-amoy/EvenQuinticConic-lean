import EvenQuinticConic.QuadraticTraceZero

/-! # Completing the square as an actual algebra isomorphism -/
noncomputable section
namespace EvenQuinticConic
variable {R : Type*} [CommRing R]

/-- Translating the generator removes the linear coefficient. -/
def quadraticShiftEquiv (a c : R) :
    QuadraticAlgebra R a (c + c) ≃ₐ[R] KummerAlgebra (a + c * c) where
  toFun x := ⟨x.re + c * x.im, x.im⟩
  invFun x := ⟨x.re - c * x.im, x.im⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_add' x y := by ext <;> simp; ring
  commutes' r := by ext <;> simp [QuadraticAlgebra.algebraMap_eq]

variable [Invertible (2 : R)]

/-- The centered parameter of a general quadratic algebra. -/
def quadraticCenteredParameter (a b : R) : R := a + (⅟(2 : R) * b) * (⅟(2 : R) * b)

/-- No Kummer coordinates are assumed: completing the square constructs them. -/
def quadraticNormalForm (a b : R) :
    QuadraticAlgebra R a b ≃ₐ[R] KummerAlgebra (quadraticCenteredParameter a b) := by
  have hb : b = ⅟(2 : R) * b + ⅟(2 : R) * b := by
    calc
      b = ((2 : R) * ⅟(2 : R)) * b := by rw [mul_invOf_self, one_mul]
      _ = _ := by ring
  exact Eq.mp (congrArg (fun d : R ↦
    QuadraticAlgebra R a d ≃ₐ[R] KummerAlgebra (quadraticCenteredParameter a b)) hb.symm)
      (quadraticShiftEquiv a (⅟(2 : R) * b))

/-- The centered generator has square equal to the centered parameter. -/
theorem quadraticCenteredParameter_discriminant (a b : R) :
    4 * quadraticCenteredParameter a b = b * b + 4 * a := by
  have h : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self _
  unfold quadraticCenteredParameter
  calc
    _ = (2 * ⅟(2 : R)) * (2 * ⅟(2 : R)) * (b * b) + 4 * a := by ring
    _ = _ := by rw [h]; ring

end EvenQuinticConic
