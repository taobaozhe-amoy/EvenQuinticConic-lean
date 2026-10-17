import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Quotients on actual localized affine charts

Taking a principal open and imposing equations commute. The comparisons
below retain the original quotient and localization maps; the last version
also accounts for the pivot relation of a projective standard chart.
-/

noncomputable section
namespace EvenQuinticConic

variable {R : Type*} [CommRing R]

/-- The equation ideal in a principal localization. -/
def localizedEquationIdeal (I : Ideal R) (d : R) : Ideal (Localization.Away d) :=
  I.map (algebraMap R (Localization.Away d))

/-- The canonical action of the original quotient on the localized quotient. -/
def quotientLocalizationAlgebra (I : Ideal R) (d : R) :
    Algebra (R ⧸ I) (Localization.Away d ⧸ localizedEquationIdeal I d) :=
  (Ideal.quotientMap (localizedEquationIdeal I d)
    (algebraMap R (Localization.Away d)) Ideal.le_comap_map).toAlgebra

theorem quotientLocalization_isLocalization (I : Ideal R) (d : R) :
    letI := quotientLocalizationAlgebra I d
    IsLocalization.Away (Ideal.Quotient.mk I d)
      (Localization.Away d ⧸ localizedEquationIdeal I d) := by
  letI := quotientLocalizationAlgebra I d
  have h : IsLocalization ((Submonoid.powers d).map (Ideal.Quotient.mk I))
      (Localization.Away d ⧸ localizedEquationIdeal I d) := by
    apply IsLocalization.of_surjective (Localization.Away d) (M := Submonoid.powers d)
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (localizedEquationIdeal I d)) Ideal.Quotient.mk_surjective
    · ext r
      rfl
    · rw [Ideal.mk_ker, Ideal.mk_ker]
      rfl
  simpa only [Submonoid.map_powers] using h

/-- The actual quotient of a principal localization is the principal
localization of the actual quotient. -/
def quotientLocalizationRingEquiv (I : Ideal R) (d : R) :
    (Localization.Away d ⧸ localizedEquationIdeal I d) ≃+*
      Localization.Away (Ideal.Quotient.mk I d) := by
  letI := quotientLocalizationAlgebra I d
  letI := quotientLocalization_isLocalization I d
  exact (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I d))
    (Localization.Away d ⧸ localizedEquationIdeal I d)
    (Localization.Away (Ideal.Quotient.mk I d))).toRingEquiv

@[simp] theorem quotientLocalizationRingEquiv_mk (I : Ideal R) (d r : R) :
    quotientLocalizationRingEquiv I d
        (Ideal.Quotient.mk _ (algebraMap R (Localization.Away d) r)) =
      algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I d))
        (Ideal.Quotient.mk I r) := by
  letI := quotientLocalizationAlgebra I d
  letI := quotientLocalization_isLocalization I d
  exact (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I d))
    (Localization.Away d ⧸ localizedEquationIdeal I d)
    (Localization.Away (Ideal.Quotient.mk I d))).commutes (Ideal.Quotient.mk I r)

/-- Equations after first imposing a pivot relation and then localizing. -/
def normalizedLocalizedEquationIdeal (I H : Ideal R) (d : R) :
    Ideal (Localization.Away (Ideal.Quotient.mk H d)) :=
  I.map ((algebraMap (R ⧸ H) (Localization.Away (Ideal.Quotient.mk H d))).comp
    (Ideal.Quotient.mk H))

theorem normalizedLocalizedEquationIdeal_eq (I H : Ideal R) (d : R) :
    normalizedLocalizedEquationIdeal I H d =
      localizedEquationIdeal (I.map (Ideal.Quotient.mk H)) (Ideal.Quotient.mk H d) := by
  exact (Ideal.map_map _ _).symm

/-- Combining the two equations uses an equality of ideals, without
passing to radicals. -/
def normalizedEquationQuotientEquiv (I H : Ideal R) :
    ((R ⧸ H) ⧸ I.map (Ideal.Quotient.mk H)) ≃+* R ⧸ (I ⊔ H) :=
  (DoubleQuot.quotQuotEquivQuotSup H I).trans (Ideal.quotEquivOfEq (sup_comm H I))

@[simp] theorem normalizedEquationQuotientEquiv_mk (I H : Ideal R) (r : R) :
    normalizedEquationQuotientEquiv I H
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk H r)) = Ideal.Quotient.mk (I ⊔ H) r := by
  change Ideal.quotEquivOfEq (sup_comm H I)
      (DoubleQuot.quotQuotEquivQuotSup H I (DoubleQuot.quotQuotMk H I r)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk]
  rfl

/-- The exact normalized affine equations, localized at the selected
polynomial, equal the localization of the simultaneous quotient. -/
def normalizedQuotientLocalizationRingEquiv (I H : Ideal R) (d : R) :
    (Localization.Away (Ideal.Quotient.mk H d) ⧸
      normalizedLocalizedEquationIdeal I H d) ≃+*
      Localization.Away (Ideal.Quotient.mk (I ⊔ H) d) :=
  ((Ideal.quotEquivOfEq (normalizedLocalizedEquationIdeal_eq I H d)).trans
    (quotientLocalizationRingEquiv (I.map (Ideal.Quotient.mk H))
      (Ideal.Quotient.mk H d))).trans
    (IsLocalization.ringEquivOfRingEquiv _ _
      (M := Submonoid.powers (Ideal.Quotient.mk (I.map (Ideal.Quotient.mk H))
        (Ideal.Quotient.mk H d)))
      (T := Submonoid.powers (Ideal.Quotient.mk (I ⊔ H) d))
      (normalizedEquationQuotientEquiv I H)
      (by
        rw [Submonoid.map_powers]
        exact congrArg Submonoid.powers (normalizedEquationQuotientEquiv_mk I H d)))

@[simp] theorem normalizedQuotientLocalizationRingEquiv_mk
    (I H : Ideal R) (d r : R) :
    normalizedQuotientLocalizationRingEquiv I H d
      (Ideal.Quotient.mk _
        (algebraMap (R ⧸ H) (Localization.Away (Ideal.Quotient.mk H d))
          (Ideal.Quotient.mk H r))) =
      algebraMap (R ⧸ (I ⊔ H)) (Localization.Away (Ideal.Quotient.mk (I ⊔ H) d))
        (Ideal.Quotient.mk (I ⊔ H) r) := by
  simp only [normalizedQuotientLocalizationRingEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, quotientLocalizationRingEquiv_mk,
    IsLocalization.ringEquivOfRingEquiv_eq, normalizedEquationQuotientEquiv_mk]

/-- The comparison preserves the original coefficient field or ring. -/
def normalizedQuotientLocalizationAlgEquiv
    (K : Type*) [CommRing K] [Algebra K R] (I H : Ideal R) (d : R) :
    (Localization.Away (Ideal.Quotient.mk H d) ⧸
      normalizedLocalizedEquationIdeal I H d) ≃ₐ[K]
      Localization.Away (Ideal.Quotient.mk (I ⊔ H) d) :=
  { normalizedQuotientLocalizationRingEquiv I H d with
    commutes' := fun c => normalizedQuotientLocalizationRingEquiv_mk I H d
      (algebraMap K R c) }

end EvenQuinticConic
