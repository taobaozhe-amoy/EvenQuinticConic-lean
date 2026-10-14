import EvenQuinticConic.QuadraticNormalForm
import Mathlib.RingTheory.Unramified.Basic

/-!
# Formal unramifiedness forces the Kummer parameter to be a unit

The proof uses a derivation into R/(u). Thus invertibility is derived from
actual formal unramifiedness, rather than imposed as a discriminant hypothesis.
-/
noncomputable section
namespace EvenQuinticConic
variable {R : Type*} [CommRing R]

/-- Specializing the generator to zero after killing its square. -/
def kummerZeroSpecialization (u : R) :
    KummerAlgebra u →ₐ[R] R ⧸ Ideal.span {u} where
  toFun x := Ideal.Quotient.mk _ x.re
  map_zero' := map_zero _
  map_one' := map_one _
  map_add' x y := map_add _ _ _
  map_mul' x y := by
    change Ideal.Quotient.mk _ (x.re * y.re + u * x.im * y.im) = _
    have hu : Ideal.Quotient.mk (Ideal.span {u}) u = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simp [map_add, map_mul, hu]
  commutes' r := rfl

/-- A nonunit parameter would give a nonzero derivation into its quotient. -/
theorem kummer_isUnit_of_formallyUnramified (u : R)
    [Algebra.FormallyUnramified R (KummerAlgebra u)] : IsUnit u := by
  let Q := R ⧸ Ideal.span {u}
  letI : Algebra (KummerAlgebra u) Q := (kummerZeroSpecialization u).toRingHom.toAlgebra
  letI : IsScalarTower R (KummerAlgebra u) Q :=
    IsScalarTower.of_algebraMap_eq' (kummerZeroSpecialization u).comp_algebraMap.symm
  let d : Derivation R (KummerAlgebra u) Q :=
    { toFun := fun x ↦ Ideal.Quotient.mk _ x.im
      map_add' := fun x y ↦ map_add _ _ _
      map_smul' := fun r x ↦ by
        change Ideal.Quotient.mk _ (r * x.im) = _
        exact map_mul _ _ _
      map_one_eq_zero' := by
        change Ideal.Quotient.mk _ (0 : R) = 0
        exact map_zero _
      leibniz' := fun x y ↦ by
        change Ideal.Quotient.mk _ (x.re * y.im + x.im * y.re + 0 * x.im * y.im) =
          Ideal.Quotient.mk _ x.re * Ideal.Quotient.mk _ y.im +
            Ideal.Quotient.mk _ y.re * Ideal.Quotient.mk _ x.im
        simp [map_add, map_mul, mul_comm] }
  have hd : d = 0 := by
    haveI : Subsingleton (Derivation R (KummerAlgebra u) Q) :=
      (KaehlerDifferential.linearMapEquivDerivation R (KummerAlgebra u)).toEquiv.surjective.subsingleton
    exact Subsingleton.elim _ _
  have hq : Ideal.Quotient.mk (Ideal.span {u}) 1 = 0 :=
    congrArg (fun e : Derivation R (KummerAlgebra u) Q ↦ e (kummerGenerator u)) hd
  have hmem : (1 : R) ∈ Ideal.span {u} := Ideal.Quotient.eq_zero_iff_mem.mp hq
  exact isUnit_of_dvd_one (Ideal.mem_span_singleton.mp hmem)

/-- A general unramified quadratic algebra acquires a unit Kummer parameter. -/
theorem quadraticCenteredParameter_isUnit (a b : R) [Invertible (2 : R)]
    [Algebra.FormallyUnramified R (QuadraticAlgebra R a b)] :
    IsUnit (quadraticCenteredParameter a b) := by
  letI := Algebra.FormallyUnramified.of_equiv (quadraticNormalForm a b)
  exact kummer_isUnit_of_formallyUnramified _

end EvenQuinticConic
