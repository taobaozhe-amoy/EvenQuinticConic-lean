import EvenQuinticConic.IncidenceAffineChart
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The fraction field of the actual open-minor incidence algebra

For rows over an integral domain, a nonzero minor makes the actual localized
incidence quotient an integral domain. Its fraction field is the fraction
field of the original coefficient ring. The embedding and fraction-field
property are constructed from the equations and the already proved
elimination isomorphism; they are not hypotheses.

In particular, when the coefficient ring is the polynomial ring in three
variables, this identifies the chart's function field with the rational
function field in three variables. This statement concerns the actual affine
chart, not an unconstructed global projective incidence scheme.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open AlgebraicGeometry

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The actual incidence quotient over the localization at the chosen minor. -/
abbrev LocalizedIncidenceAlgebra (a b : Vec3 R) :=
  AffineIncidenceAlgebra (localizedRow a b a) (localizedRow a b b)

/-- The canonical localization map into the coefficient ring's fraction field. -/
def minorLocalizationToFractionField (a b : Vec3 R) (h : (cross a b).z ≠ 0) :
    Localization.Away (cross a b).z →ₐ[R] FractionRing R :=
  Localization.mapToFractionRing (FractionRing R) (Submonoid.powers (cross a b).z)
    (Localization.Away (cross a b).z)
    (powers_le_nonZeroDivisors_of_noZeroDivisors h)

/-- Elimination gives the canonical embedding of the incidence coordinate ring. -/
def localizedIncidenceToFractionField (a b : Vec3 R) (h : (cross a b).z ≠ 0) :
    LocalizedIncidenceAlgebra a b →+* FractionRing R :=
  (minorLocalizationToFractionField a b h).toRingHom.comp
    (localizedIncidenceAlgEquiv a b).toRingHom

/-- The embedding preserves the original coefficients, before localization. -/
@[simp]
theorem localizedIncidenceToFractionField_algebraMap (a b : Vec3 R)
    (h : (cross a b).z ≠ 0) (r : R) :
    localizedIncidenceToFractionField a b h
      (algebraMap R (LocalizedIncidenceAlgebra a b) r) =
      algebraMap R (FractionRing R) r := by
  change minorLocalizationToFractionField a b h
    ((localizedIncidenceAlgEquiv a b).toAlgHom
      (algebraMap R (LocalizedIncidenceAlgebra a b) r)) = _
  rw [AlgHom.map_algebraMap, AlgHom.commutes]

theorem minorLocalizationToFractionField_injective (a b : Vec3 R)
    (h : (cross a b).z ≠ 0) :
    Function.Injective (minorLocalizationToFractionField a b h) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (cross a b).z)
    (minorLocalizationToFractionField a b h).toRingHom).mpr
  intro x y
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  exact ⟨fun he => congrArg (algebraMap R (FractionRing R))
    (IsLocalization.injective (Localization.Away (cross a b).z)
      (powers_le_nonZeroDivisors_of_noZeroDivisors h) he),
    fun he => congrArg (algebraMap R (Localization.Away (cross a b).z))
      (IsFractionRing.injective R (FractionRing R) he)⟩

theorem localizedIncidenceToFractionField_injective (a b : Vec3 R)
    (h : (cross a b).z ≠ 0) :
    Function.Injective (localizedIncidenceToFractionField a b h) :=
  (minorLocalizationToFractionField_injective a b h).comp
    (localizedIncidenceAlgEquiv a b).injective

/-- Nonvanishing of the minor proves integrality of the actual quotient ring. -/
theorem localizedIncidence_isDomain (a b : Vec3 R) (h : (cross a b).z ≠ 0) :
    IsDomain (LocalizedIncidenceAlgebra a b) :=
  Function.Injective.isDomain (localizedIncidenceToFractionField a b h)
    (localizedIncidenceToFractionField_injective a b h)

/-- The constructed embedding makes the coefficient fraction field a fraction
field of the actual incidence quotient. -/
theorem localizedIncidence_isFractionRing (a b : Vec3 R)
    (h : (cross a b).z ≠ 0) :
    @IsFractionRing (LocalizedIncidenceAlgebra a b) _ (FractionRing R) _
      (localizedIncidenceToFractionField a b h).toAlgebra := by
  letI : Algebra (Localization.Away (cross a b).z) (FractionRing R) :=
    (minorLocalizationToFractionField a b h).toRingHom.toAlgebra
  letI : IsScalarTower R (Localization.Away (cross a b).z) (FractionRing R) :=
    IsScalarTower.of_algHom (minorLocalizationToFractionField a b h)
  have hf : IsFractionRing (Localization.Away (cross a b).z) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers (cross a b).z)
      (Localization.Away (cross a b).z) (FractionRing R)
      (powers_le_nonZeroDivisors_of_noZeroDivisors h)
  exact (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (FractionRing R)
    (localizedIncidenceAlgEquiv a b).symm.toRingEquiv).mp hf

/-- An actual equivalence between the two fraction rings, with the incidence
side formed from the quotient by the two equations. -/
def localizedIncidenceFractionRingEquiv (a b : Vec3 R) (h : (cross a b).z ≠ 0) :
    FractionRing (LocalizedIncidenceAlgebra a b) ≃+* FractionRing R := by
  letI : Algebra (LocalizedIncidenceAlgebra a b) (FractionRing R) :=
    (localizedIncidenceToFractionField a b h).toAlgebra
  letI : IsFractionRing (LocalizedIncidenceAlgebra a b) (FractionRing R) :=
    localizedIncidence_isFractionRing a b h
  exact (IsLocalization.algEquiv (nonZeroDivisors (LocalizedIncidenceAlgebra a b))
    (FractionRing (LocalizedIncidenceAlgebra a b)) (FractionRing R)).toRingEquiv

/-- The equivalence extends the explicit embedding of the coordinate algebra. -/
@[simp]
theorem localizedIncidenceFractionRingEquiv_algebraMap (a b : Vec3 R)
    (h : (cross a b).z ≠ 0) (x : LocalizedIncidenceAlgebra a b) :
    localizedIncidenceFractionRingEquiv a b h
      (algebraMap (LocalizedIncidenceAlgebra a b)
        (FractionRing (LocalizedIncidenceAlgebra a b)) x) =
      localizedIncidenceToFractionField a b h x := by
  letI : Algebra (LocalizedIncidenceAlgebra a b) (FractionRing R) :=
    (localizedIncidenceToFractionField a b h).toAlgebra
  letI : IsFractionRing (LocalizedIncidenceAlgebra a b) (FractionRing R) :=
    localizedIncidence_isFractionRing a b h
  exact (IsLocalization.algEquiv (nonZeroDivisors (LocalizedIncidenceAlgebra a b))
    (FractionRing (LocalizedIncidenceAlgebra a b)) (FractionRing R)).commutes x

/-- The fraction-ring equivalence preserves the original coefficient ring. -/
def localizedIncidenceFractionRingAlgEquiv (a b : Vec3 R)
    (h : (cross a b).z ≠ 0) :
    FractionRing (LocalizedIncidenceAlgebra a b) ≃ₐ[R] FractionRing R where
  __ := localizedIncidenceFractionRingEquiv a b h
  commutes' r := by
    change localizedIncidenceFractionRingEquiv a b h
      (algebraMap R (FractionRing (LocalizedIncidenceAlgebra a b)) r) = _
    rw [IsScalarTower.algebraMap_apply R (LocalizedIncidenceAlgebra a b)
      (FractionRing (LocalizedIncidenceAlgebra a b)),
      localizedIncidenceFractionRingEquiv_algebraMap,
      localizedIncidenceToFractionField_algebraMap]

/-- For a chart in three affine base coordinates, the fraction field is the
rational function field in exactly those three variables. -/
def threeVariableIncidenceFractionRingEquiv {K : Type*} [Field K]
    (a b : Vec3 (MvPolynomial (Fin 3) K)) (h : (cross a b).z ≠ 0) :
    FractionRing (LocalizedIncidenceAlgebra a b) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 3) K) :=
  (localizedIncidenceFractionRingAlgEquiv a b h).restrictScalars K

/-- The structural scalar action on the actual generic stalk is the composite
of the scalar map to the coordinate algebra and the canonical stalk map. -/
def localizedIncidenceGenericStalkAlgebra {k : Type*} [CommRing k] [Algebra k R]
    (a b : Vec3 R) (h : (cross a b).z ≠ 0) :
    letI := localizedIncidence_isDomain a b h
    Algebra k (Spec (CommRingCat.of (LocalizedIncidenceAlgebra a b))).functionField := by
  letI := localizedIncidence_isDomain a b h
  letI : Algebra (LocalizedIncidenceAlgebra a b)
      (Spec (CommRingCat.of (LocalizedIncidenceAlgebra a b))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
      (CommRingCat.of (LocalizedIncidenceAlgebra a b))
  exact ((algebraMap (LocalizedIncidenceAlgebra a b)
    (Spec (CommRingCat.of (LocalizedIncidenceAlgebra a b))).functionField).comp
      (algebraMap k (LocalizedIncidenceAlgebra a b))).toAlgebra

/-- The function field defined as the actual scheme's generic stalk is the
coefficient ring's fraction field, compatibly with the structural scalars. -/
def localizedIncidenceGenericStalkAlgEquiv {k : Type*} [CommRing k] [Algebra k R]
    (a b : Vec3 R) (h : (cross a b).z ≠ 0) :
    letI := localizedIncidence_isDomain a b h
    letI := localizedIncidenceGenericStalkAlgebra (k := k) a b h
    (Spec (CommRingCat.of (LocalizedIncidenceAlgebra a b))).functionField
      ≃ₐ[k] FractionRing R := by
  letI := localizedIncidence_isDomain a b h
  letI : Algebra (LocalizedIncidenceAlgebra a b)
      (Spec (CommRingCat.of (LocalizedIncidenceAlgebra a b))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
      (CommRingCat.of (LocalizedIncidenceAlgebra a b))
  letI : IsFractionRing (LocalizedIncidenceAlgebra a b)
      (Spec (CommRingCat.of (LocalizedIncidenceAlgebra a b))).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of (LocalizedIncidenceAlgebra a b))
  letI := localizedIncidenceGenericStalkAlgebra (k := k) a b h
  letI : IsScalarTower k (LocalizedIncidenceAlgebra a b)
      (Spec (CommRingCat.of (LocalizedIncidenceAlgebra a b))).functionField :=
    ⟨fun r x z => by
      simp only [Algebra.smul_def, map_mul, mul_assoc]
      rfl⟩
  exact ((IsLocalization.algEquiv (nonZeroDivisors (LocalizedIncidenceAlgebra a b))
    (Spec (CommRingCat.of (LocalizedIncidenceAlgebra a b))).functionField
    (FractionRing (LocalizedIncidenceAlgebra a b))).restrictScalars k).trans
      ((localizedIncidenceFractionRingAlgEquiv a b h).restrictScalars k)

end EvenQuinticConic.Incidence
