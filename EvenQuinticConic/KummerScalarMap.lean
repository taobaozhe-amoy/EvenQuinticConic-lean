import EvenQuinticConic.QuadraticTraceZeroTransition

/-! # Scalar restriction maps of explicit Kummer algebras -/
noncomputable section
namespace EvenQuinticConic
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The actual coefficientwise ring map induced by a change of scalars. -/
def kummerScalarMap (f : R →+* S) (u : R) :
    KummerAlgebra u →+* KummerAlgebra (f u) where
  toFun x := ⟨f x.re, f x.im⟩
  map_one' := by
    change (⟨f 1, f 0⟩ : KummerAlgebra (f u)) = ⟨1, 0⟩
    ext <;> simp
  map_mul' x y := by ext <;> simp [map_add, map_mul]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] theorem kummerScalarMap_re (f : R →+* S) (u : R) (x : KummerAlgebra u) :
    (kummerScalarMap f u x).re = f x.re := rfl

@[simp] theorem kummerScalarMap_im (f : R →+* S) (u : R) (x : KummerAlgebra u) :
    (kummerScalarMap f u x).im = f x.im := rfl

@[simp] theorem kummerScalarMap_generator (f : R →+* S) (u : R) :
    kummerScalarMap f u (kummerGenerator u) = kummerGenerator (f u) := by
  ext <;> simp [kummerGenerator]

/-- Coefficientwise maps compose as the scalar maps do. -/
theorem kummerScalarMap_comp (f : R →+* S) (g : S →+* T) (u : R) :
    (kummerScalarMap g (f u)).comp (kummerScalarMap f u) =
      kummerScalarMap (g.comp f) u := by
  ext x <;> rfl

/-- Actual algebra traces commute with the coefficientwise scalar map. -/
theorem kummerScalarMap_trace (f : R →+* S) (u : R) (x : KummerAlgebra u) :
    Algebra.trace S (KummerAlgebra (f u)) (kummerScalarMap f u x) =
      f (Algebra.trace R (KummerAlgebra u) x) := by
  simp only [kummer_trace, kummerScalarMap_re, map_mul, map_ofNat]

end EvenQuinticConic
