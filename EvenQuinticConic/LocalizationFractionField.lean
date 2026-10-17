import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Parameter localization preserves the total fraction field

For an injective algebra map of domains `A → B`, invert exactly the images
of nonzero elements of `A`.  The resulting ring is a domain and its fraction
field is the fraction field of `B`.  All embeddings and scalar actions below
are induced by the original algebra map and the localization maps.
-/

noncomputable section
namespace EvenQuinticConic

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B]

def parameterDenominators : Submonoid B :=
  (nonZeroDivisors A).map (algebraMap A B)

abbrev ParameterLocalization := Localization (parameterDenominators A B)

theorem parameterDenominators_le_nonZeroDivisors
    (h : Function.Injective (algebraMap A B)) :
    parameterDenominators A B ≤ nonZeroDivisors B := by
  rintro b ⟨a, ha, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro hz
  exact (mem_nonZeroDivisors_iff_ne_zero.mp ha)
    (h (by simpa only [map_zero] using hz))

theorem parameterLocalization_isDomain
    (h : Function.Injective (algebraMap A B)) : IsDomain (ParameterLocalization A B) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (parameterDenominators_le_nonZeroDivisors A B h)

theorem parameterLocalization_algebraMap_injective
    (h : Function.Injective (algebraMap A B)) :
    Function.Injective (algebraMap B (ParameterLocalization A B)) :=
  IsLocalization.injective _ (parameterDenominators_le_nonZeroDivisors A B h)

theorem parameterLocalization_parameter_isUnit (a : nonZeroDivisors A) :
    IsUnit (algebraMap B (ParameterLocalization A B) (algebraMap A B a)) :=
  IsLocalization.map_units (ParameterLocalization A B)
    (⟨algebraMap A B a, ⟨a, a.property, rfl⟩⟩ : parameterDenominators A B)

def parameterLocalizationBaseMap : FractionRing A →+* ParameterLocalization A B :=
  IsLocalization.lift (g := (algebraMap B (ParameterLocalization A B)).comp (algebraMap A B))
    (parameterLocalization_parameter_isUnit A B)

@[simp] theorem parameterLocalizationBaseMap_algebraMap (a : A) :
    parameterLocalizationBaseMap A B (algebraMap A (FractionRing A) a) =
      algebraMap B (ParameterLocalization A B) (algebraMap A B a) :=
  IsLocalization.lift_eq _ _

abbrev parameterLocalizationBaseAlgebra : Algebra (FractionRing A) (ParameterLocalization A B) :=
  (parameterLocalizationBaseMap A B).toAlgebra

theorem parameterLocalizationBaseMap_injective
    (h : Function.Injective (algebraMap A B)) :
    Function.Injective (parameterLocalizationBaseMap A B) := by
  letI := parameterLocalization_isDomain A B h
  exact (parameterLocalizationBaseMap A B).injective

def parameterLocalizationToFractionField (h : Function.Injective (algebraMap A B)) :
    ParameterLocalization A B →ₐ[B] FractionRing B :=
  Localization.mapToFractionRing (FractionRing B) (parameterDenominators A B)
    (ParameterLocalization A B) (parameterDenominators_le_nonZeroDivisors A B h)

@[simp] theorem parameterLocalizationToFractionField_algebraMap
    (h : Function.Injective (algebraMap A B)) (b : B) :
    parameterLocalizationToFractionField A B h
        (algebraMap B (ParameterLocalization A B) b) = algebraMap B (FractionRing B) b :=
  (parameterLocalizationToFractionField A B h).commutes b

theorem parameterLocalization_isFractionRing (h : Function.Injective (algebraMap A B)) :
    @IsFractionRing (ParameterLocalization A B) _ (FractionRing B) _
      (parameterLocalizationToFractionField A B h).toRingHom.toAlgebra := by
  letI : Algebra (ParameterLocalization A B) (FractionRing B) :=
    (parameterLocalizationToFractionField A B h).toRingHom.toAlgebra
  letI : IsScalarTower B (ParameterLocalization A B) (FractionRing B) :=
    IsScalarTower.of_algHom (parameterLocalizationToFractionField A B h)
  exact IsFractionRing.isFractionRing_of_isLocalization (parameterDenominators A B)
    (ParameterLocalization A B) (FractionRing B)
    (parameterDenominators_le_nonZeroDivisors A B h)

theorem parameterLocalizationToFractionField_injective
    (h : Function.Injective (algebraMap A B)) :
    Function.Injective (parameterLocalizationToFractionField A B h) := by
  letI : Algebra (ParameterLocalization A B) (FractionRing B) :=
    (parameterLocalizationToFractionField A B h).toRingHom.toAlgebra
  letI := parameterLocalization_isFractionRing A B h
  exact IsFractionRing.injective (ParameterLocalization A B) (FractionRing B)

def parameterLocalizationFractionFieldEquiv (h : Function.Injective (algebraMap A B)) :
    FractionRing (ParameterLocalization A B) ≃+* FractionRing B := by
  letI : Algebra (ParameterLocalization A B) (FractionRing B) :=
    (parameterLocalizationToFractionField A B h).toRingHom.toAlgebra
  letI := parameterLocalization_isFractionRing A B h
  exact (IsLocalization.algEquiv (nonZeroDivisors (ParameterLocalization A B))
    (FractionRing (ParameterLocalization A B)) (FractionRing B)).toRingEquiv

@[simp] theorem parameterLocalizationFractionFieldEquiv_algebraMap
    (h : Function.Injective (algebraMap A B)) (x : ParameterLocalization A B) :
    parameterLocalizationFractionFieldEquiv A B h
        (algebraMap (ParameterLocalization A B) (FractionRing (ParameterLocalization A B)) x) =
      parameterLocalizationToFractionField A B h x := by
  letI : Algebra (ParameterLocalization A B) (FractionRing B) :=
    (parameterLocalizationToFractionField A B h).toRingHom.toAlgebra
  letI := parameterLocalization_isFractionRing A B h
  exact (IsLocalization.algEquiv (nonZeroDivisors (ParameterLocalization A B))
    (FractionRing (ParameterLocalization A B)) (FractionRing B)).commutes x

@[simp] theorem parameterLocalizationFractionFieldEquiv_coordinate
    (h : Function.Injective (algebraMap A B)) (b : B) :
    parameterLocalizationFractionFieldEquiv A B h
        (algebraMap (ParameterLocalization A B) (FractionRing (ParameterLocalization A B))
          (algebraMap B (ParameterLocalization A B) b)) = algebraMap B (FractionRing B) b := by
  rw [parameterLocalizationFractionFieldEquiv_algebraMap,
    parameterLocalizationToFractionField_algebraMap]

def parameterFractionFieldMap (h : Function.Injective (algebraMap A B)) :
    FractionRing A →+* FractionRing B :=
  IsFractionRing.lift (g := (algebraMap B (FractionRing B)).comp (algebraMap A B))
    ((IsFractionRing.injective B (FractionRing B)).comp h)

@[simp] theorem parameterFractionFieldMap_algebraMap
    (h : Function.Injective (algebraMap A B)) (a : A) :
    parameterFractionFieldMap A B h (algebraMap A (FractionRing A) a) =
      algebraMap B (FractionRing B) (algebraMap A B a) :=
  IsFractionRing.lift_algebraMap _ _

def parameterLocalizedFractionFieldMap (h : Function.Injective (algebraMap A B)) :
    FractionRing A →+* FractionRing (ParameterLocalization A B) := by
  letI := parameterLocalization_isDomain A B h
  exact IsFractionRing.lift
    (g := ((algebraMap (ParameterLocalization A B) (FractionRing (ParameterLocalization A B))).comp
      (algebraMap B (ParameterLocalization A B))).comp (algebraMap A B))
    (((IsFractionRing.injective (ParameterLocalization A B)
      (FractionRing (ParameterLocalization A B))).comp
      (parameterLocalization_algebraMap_injective A B h)).comp h)

@[simp] theorem parameterLocalizedFractionFieldMap_algebraMap
    (h : Function.Injective (algebraMap A B)) (a : A) :
    parameterLocalizedFractionFieldMap A B h (algebraMap A (FractionRing A) a) =
      algebraMap (ParameterLocalization A B) (FractionRing (ParameterLocalization A B))
        (algebraMap B (ParameterLocalization A B) (algebraMap A B a)) := by
  letI := parameterLocalization_isDomain A B h
  exact IsFractionRing.lift_algebraMap _ _

theorem parameterLocalizationFractionFieldEquiv_comp_parameter
    (h : Function.Injective (algebraMap A B)) :
    (parameterLocalizationFractionFieldEquiv A B h).toRingHom.comp
      (parameterLocalizedFractionFieldMap A B h) = parameterFractionFieldMap A B h := by
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  simp only [RingHom.comp_apply, parameterLocalizedFractionFieldMap_algebraMap,
    parameterLocalizationFractionFieldEquiv_coordinate, parameterFractionFieldMap_algebraMap]

theorem parameterLocalizedFractionFieldMap_eq_comp_baseMap
    (h : Function.Injective (algebraMap A B)) :
    parameterLocalizedFractionFieldMap A B h =
      (algebraMap (ParameterLocalization A B) (FractionRing (ParameterLocalization A B))).comp
        (parameterLocalizationBaseMap A B) := by
  letI := parameterLocalization_isDomain A B h
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  simp only [RingHom.comp_apply, parameterLocalizedFractionFieldMap_algebraMap,
    parameterLocalizationBaseMap_algebraMap]

abbrev parameterFractionFieldAlgebra (h : Function.Injective (algebraMap A B)) :
    Algebra (FractionRing A) (FractionRing B) := (parameterFractionFieldMap A B h).toAlgebra

abbrev parameterLocalizedFractionFieldAlgebra (h : Function.Injective (algebraMap A B)) :
    Algebra (FractionRing A) (FractionRing (ParameterLocalization A B)) :=
  (parameterLocalizedFractionFieldMap A B h).toAlgebra

def parameterLocalizationFractionFieldAlgEquiv (h : Function.Injective (algebraMap A B)) :
    letI := parameterFractionFieldAlgebra A B h
    letI := parameterLocalizedFractionFieldAlgebra A B h
    FractionRing (ParameterLocalization A B) ≃ₐ[FractionRing A] FractionRing B := by
  letI := parameterFractionFieldAlgebra A B h
  letI := parameterLocalizedFractionFieldAlgebra A B h
  refine { parameterLocalizationFractionFieldEquiv A B h with commutes' := ?_ }
  intro a
  exact RingHom.congr_fun (parameterLocalizationFractionFieldEquiv_comp_parameter A B h) a

def parameterLocalizationFractionFieldAlgEquiv_overBase
    (h : Function.Injective (algebraMap A B)) :
    letI := parameterLocalizationBaseAlgebra A B
    letI := parameterFractionFieldAlgebra A B h
    FractionRing (ParameterLocalization A B) ≃ₐ[FractionRing A] FractionRing B := by
  letI := parameterLocalizationBaseAlgebra A B
  letI := parameterFractionFieldAlgebra A B h
  refine { parameterLocalizationFractionFieldEquiv A B h with commutes' := ?_ }
  intro a
  have he := RingHom.congr_fun (parameterLocalizationFractionFieldEquiv_comp_parameter A B h) a
  rw [parameterLocalizedFractionFieldMap_eq_comp_baseMap] at he
  exact he

end EvenQuinticConic
