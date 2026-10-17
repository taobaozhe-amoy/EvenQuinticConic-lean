import EvenQuinticConic.IncidenceAffineChart
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

/-!
# Localizing the actual incidence equations

Localizing the coefficient ring and then imposing the two incidence equations
is the localization of the original incidence quotient. This comparison uses
the actual coefficient map and actual defining ideals, rather than assuming a
base-change isomorphism as part of the chart data.
-/

noncomputable section
namespace EvenQuinticConic.Incidence
open MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp]
theorem map_rowPolynomial (f : R →+* S) (a : Vec3 R) :
    MvPolynomial.map f (rowPolynomial a) = rowPolynomial (mapRow f a) := by
  simp [rowPolynomial, mapRow]

/-- The actual defining ideal is carried to the defining ideal of the mapped rows. -/
theorem map_affineIncidenceIdeal (f : R →+* S) (a b : Vec3 R) :
    Ideal.map (MvPolynomial.map f) (affineIncidenceIdeal a b) =
      affineIncidenceIdeal (mapRow f a) (mapRow f b) := by
  rw [affineIncidenceIdeal, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, map_rowPolynomial]
  rfl

/-- Canonical coefficient change on the quotient by the two actual equations. -/
def affineIncidenceCoefficientMap (f : R →+* S) (a b : Vec3 R) :
    AffineIncidenceAlgebra a b →+* AffineIncidenceAlgebra (mapRow f a) (mapRow f b) :=
  Ideal.quotientMap _ (MvPolynomial.map f) (by
    rw [← Ideal.map_le_iff_le_comap, map_affineIncidenceIdeal])

@[simp]
theorem affineIncidenceCoefficientMap_mk (f : R →+* S) (a b : Vec3 R)
    (F : MvPolynomial (Fin 2) R) :
    affineIncidenceCoefficientMap f a b (Ideal.Quotient.mk _ F) =
      Ideal.Quotient.mk _ (MvPolynomial.map f F) := rfl

section Localization

variable [Algebra R S]
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Scalar action of the original incidence quotient on the coefficient-localized quotient. -/
def affineIncidenceCoefficientAlgebra (a b : Vec3 R) :
    Algebra (AffineIncidenceAlgebra a b)
      (AffineIncidenceAlgebra (mapRow (algebraMap R S) a) (mapRow (algebraMap R S) b)) :=
  (affineIncidenceCoefficientMap (algebraMap R S) a b).toAlgebra

/-- Localization commutes with the actual incidence quotient, with the
specified canonical coefficient map. No nonzero-minor assumption is needed. -/
theorem affineIncidence_isLocalization (a b : Vec3 R) (d : R)
    [IsLocalization.Away d S] :
    letI := affineIncidenceCoefficientAlgebra (S := S) a b
    IsLocalization.Away (algebraMap R (AffineIncidenceAlgebra a b) d)
      (AffineIncidenceAlgebra (mapRow (algebraMap R S) a) (mapRow (algebraMap R S) b)) := by
  letI := affineIncidenceCoefficientAlgebra (S := S) a b
  let f := Ideal.Quotient.mk (affineIncidenceIdeal a b)
  let g := Ideal.Quotient.mk
    (affineIncidenceIdeal (mapRow (algebraMap R S) a) (mapRow (algebraMap R S) b))
  have h : IsLocalization (((Submonoid.powers d).map (C (σ := Fin 2))).map f)
      (AffineIncidenceAlgebra (mapRow (algebraMap R S) a) (mapRow (algebraMap R S) b)) := by
    apply IsLocalization.of_surjective (MvPolynomial (Fin 2) S)
      (M := (Submonoid.powers d).map (C (σ := Fin 2))) f (Ideal.Quotient.mk_surjective)
      g (Ideal.Quotient.mk_surjective)
    · ext F <;> rfl
    · change RingHom.ker g ≤ (RingHom.ker f).map (MvPolynomial.map (algebraMap R S))
      rw [Ideal.mk_ker, Ideal.mk_ker, map_affineIncidenceIdeal]
  simpa only [Submonoid.map_map, Submonoid.map_powers,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq] using h

/-- The original quotient acts on the actual localized-row quotient by its
canonical coefficient map. -/
def localizedIncidenceCoefficientAlgebra (a b : Vec3 R) :
    Algebra (AffineIncidenceAlgebra a b)
      (AffineIncidenceAlgebra (localizedRow a b a) (localizedRow a b b)) :=
  affineIncidenceCoefficientAlgebra (S := Localization.Away (cross a b).z) a b

/-- The localized incidence scheme is obtained by taking the corresponding
principal open of the unlocalized incidence quotient. -/
def affineIncidenceLocalizationEquiv (a b : Vec3 R) :
    letI := localizedIncidenceCoefficientAlgebra a b
    Localization.Away (algebraMap R (AffineIncidenceAlgebra a b) (cross a b).z)
      ≃ₐ[AffineIncidenceAlgebra a b]
        AffineIncidenceAlgebra (localizedRow a b a) (localizedRow a b b) := by
  letI := localizedIncidenceCoefficientAlgebra a b
  letI : IsLocalization.Away (algebraMap R (AffineIncidenceAlgebra a b) (cross a b).z)
      (AffineIncidenceAlgebra (localizedRow a b a) (localizedRow a b b)) :=
    affineIncidence_isLocalization
      (S := Localization.Away (cross a b).z) a b (cross a b).z
  exact IsLocalization.algEquiv
    (Submonoid.powers (algebraMap R (AffineIncidenceAlgebra a b) (cross a b).z)) _ _

end Localization
end EvenQuinticConic.Incidence
