import EvenQuinticConic.KummerScalarMap

/-! # Transport of Kummer algebras along coefficient-ring isomorphisms -/
noncomputable section
namespace EvenQuinticConic
variable {R S : Type*} [CommRing R] [CommRing S]

/-- A coefficient-ring isomorphism transports a Kummer algebra when the
parameters correspond. Both directions act on the two actual coefficients. -/
def kummerScalarEquivOfEq (e : R ≃+* S) {u : R} {v : S} (h : e u = v) :
    KummerAlgebra u ≃+* KummerAlgebra v where
  toFun x := ⟨e x.re, e x.im⟩
  invFun x := ⟨e.symm x.re, e.symm x.im⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp [map_add, map_mul, h]

@[simp] theorem kummerScalarEquivOfEq_re (e : R ≃+* S) {u : R} {v : S}
    (h : e u = v) (x : KummerAlgebra u) :
    (kummerScalarEquivOfEq e h x).re = e x.re := rfl

@[simp] theorem kummerScalarEquivOfEq_im (e : R ≃+* S) {u : R} {v : S}
    (h : e u = v) (x : KummerAlgebra u) :
    (kummerScalarEquivOfEq e h x).im = e x.im := rfl

@[simp] theorem kummerScalarEquivOfEq_symm_re (e : R ≃+* S) {u : R} {v : S}
    (h : e u = v) (x : KummerAlgebra v) :
    ((kummerScalarEquivOfEq e h).symm x).re = e.symm x.re := rfl

@[simp] theorem kummerScalarEquivOfEq_symm_im (e : R ≃+* S) {u : R} {v : S}
    (h : e u = v) (x : KummerAlgebra v) :
    ((kummerScalarEquivOfEq e h).symm x).im = e.symm x.im := rfl

@[simp] theorem kummerScalarEquivOfEq_algebraMap (e : R ≃+* S) {u : R} {v : S}
    (h : e u = v) (r : R) :
    kummerScalarEquivOfEq e h (algebraMap R (KummerAlgebra u) r) =
      algebraMap S (KummerAlgebra v) (e r) := by
  ext <;> simp [QuadraticAlgebra.algebraMap_eq]

@[simp] theorem kummerScalarEquivOfEq_symm_algebraMap (e : R ≃+* S)
    {u : R} {v : S} (h : e u = v) (s : S) :
    (kummerScalarEquivOfEq e h).symm (algebraMap S (KummerAlgebra v) s) =
      algebraMap R (KummerAlgebra u) (e.symm s) := by
  ext <;> simp [QuadraticAlgebra.algebraMap_eq]

/-- The coefficientwise equivalence is semilinear for the scalar-ring equivalence. -/
theorem kummerScalarEquivOfEq_smul (e : R ≃+* S) {u : R} {v : S}
    (h : e u = v) (r : R) (x : KummerAlgebra u) :
    kummerScalarEquivOfEq e h (r • x) = e r • kummerScalarEquivOfEq e h x := by
  simp only [Algebra.smul_def, map_mul, kummerScalarEquivOfEq_algebraMap]

/-- Scalar transport with the target parameter given by its actual image. -/
def kummerScalarEquiv (e : R ≃+* S) (u : R) :
    KummerAlgebra u ≃+* KummerAlgebra (e u) :=
  kummerScalarEquivOfEq e rfl

@[simp] theorem kummerScalarEquiv_re (e : R ≃+* S) (u : R) (x : KummerAlgebra u) :
    (kummerScalarEquiv e u x).re = e x.re := rfl

@[simp] theorem kummerScalarEquiv_im (e : R ≃+* S) (u : R) (x : KummerAlgebra u) :
    (kummerScalarEquiv e u x).im = e x.im := rfl

@[simp] theorem kummerScalarEquiv_symm_re (e : R ≃+* S) (u : R)
    (x : KummerAlgebra (e u)) :
    ((kummerScalarEquiv e u).symm x).re = e.symm x.re := rfl

@[simp] theorem kummerScalarEquiv_symm_im (e : R ≃+* S) (u : R)
    (x : KummerAlgebra (e u)) :
    ((kummerScalarEquiv e u).symm x).im = e.symm x.im := rfl

@[simp] theorem kummerScalarEquiv_algebraMap (e : R ≃+* S) (u r : R) :
    kummerScalarEquiv e u (algebraMap R (KummerAlgebra u) r) =
      algebraMap S (KummerAlgebra (e u)) (e r) :=
  kummerScalarEquivOfEq_algebraMap e rfl r

/-- The ring equivalence extends the previously defined scalar map. -/
theorem kummerScalarEquiv_toRingHom (e : R ≃+* S) (u : R) :
    (kummerScalarEquiv e u).toRingHom = kummerScalarMap e.toRingHom u := rfl

end EvenQuinticConic
