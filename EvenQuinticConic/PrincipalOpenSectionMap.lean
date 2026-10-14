import Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# Principal-localization scalars on genuine structure-sheaf sections

For every open `V` contained in `D(f)`, the localization `R_f` acts on
the actual ring of regular functions on `V`. The scalar map is obtained
by restricting the canonical section on `D(f)`, and commutes with every
further restriction. No affine hypothesis on `V` is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace EvenQuinticConic

variable {R : Type*} [CommRing R]

/-- Interpret a principal-localization element as an actual section on
any open contained in the corresponding principal open. -/
def principalOpenSectionMap (f : R) (V : Opens (PrimeSpectrum.Top R))
    (hV : V ≤ PrimeSpectrum.basicOpen f) :
    Localization.Away f →+* (Spec.structureSheaf R).val.obj (op V) :=
  ((Spec.structureSheaf R).val.map (homOfLE hV).op).hom.comp
    (StructureSheaf.toBasicOpen R f)

/-- The localized scalar map extends the usual map from the affine ring. -/
theorem principalOpenSectionMap_algebraMap (f : R)
    (V : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f) (r : R) :
    principalOpenSectionMap f V hV (algebraMap R (Localization.Away f) r) =
      StructureSheaf.toOpen R V r := by
  have h := RingHom.congr_fun (StructureSheaf.localization_toBasicOpen R f) r
  simp only [RingHom.comp_apply] at h
  change (Spec.structureSheaf R).val.map (homOfLE hV).op
    (StructureSheaf.toBasicOpen R f (algebraMap R (Localization.Away f) r)) = _
  rw [h]
  exact ConcreteCategory.congr_hom
    (StructureSheaf.toOpen_res R (PrimeSpectrum.basicOpen f) V (homOfLE hV)) r

/-- The principal-localization scalar maps commute with actual sheaf restrictions. -/
theorem principalOpenSectionMap_restrict (f : R)
    (V W : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f)
    (hW : W ≤ PrimeSpectrum.basicOpen f) (hWV : W ≤ V)
    (s : Localization.Away f) :
    (Spec.structureSheaf R).val.map (homOfLE hWV).op
      (principalOpenSectionMap f V hV s) = principalOpenSectionMap f W hW s := by
  change (Spec.structureSheaf R).val.map (homOfLE hWV).op
    ((Spec.structureSheaf R).val.map (homOfLE hV).op
      (StructureSheaf.toBasicOpen R f s)) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The local scalar algebra structure, kept explicit to avoid conflicting
instances for opens lying in more than one principal neighborhood. -/
def principalOpenSectionAlgebra (f : R) (V : Opens (PrimeSpectrum.Top R))
    (hV : V ≤ PrimeSpectrum.basicOpen f) :
    Algebra (Localization.Away f) ((Spec.structureSheaf R).val.obj (op V)) :=
  (principalOpenSectionMap f V hV).toAlgebra

/-- These localized scalars extend the canonical affine-ring scalars. -/
theorem principalOpenSectionAlgebra_isScalarTower (f : R)
    (V : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f) :
    letI := principalOpenSectionAlgebra f V hV
    IsScalarTower R (Localization.Away f) ((Spec.structureSheaf R).val.obj (op V)) := by
  letI := principalOpenSectionAlgebra f V hV
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (principalOpenSectionMap_algebraMap f V hV r).symm

end EvenQuinticConic
