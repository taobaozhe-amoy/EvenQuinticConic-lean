import EvenQuinticConic.PrincipalOpenSectionMap
import EvenQuinticConic.KummerModelRestriction

/-!
# Kummer coordinates over genuine structure-sheaf coefficient rings

A principal-localization model extends to the coefficient ring of every
smaller open, and these tensor-product coordinates commute with actual
structure-sheaf restrictions. The domain is still the tensor product of
sections with the affine algebra; its identification with sections of an
associated or pushforward module sheaf is not asserted here.
-/

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace EvenQuinticConic

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Extend a principal-localization Kummer model to the actual ring of
regular functions on any smaller open. -/
def principalOpenKummerSectionModel {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f) :
    ((Spec.structureSheaf R).val.obj (op V) ⊗[R] A) ≃ₐ[(Spec.structureSheaf R).val.obj (op V)]
      KummerAlgebra (principalOpenSectionMap f V hV u) := by
  letI := principalOpenSectionAlgebra f V hV
  letI := principalOpenSectionAlgebra_isScalarTower f V hV
  exact kummerModelRestrict e

@[simp] theorem principalOpenKummerSectionModel_tmul_re {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f)
    (s : (Spec.structureSheaf R).val.obj (op V)) (a : A) :
    (principalOpenKummerSectionModel e V hV (s ⊗ₜ[R] a)).re =
      s * principalOpenSectionMap f V hV (e (1 ⊗ₜ[R] a)).re := by
  letI := principalOpenSectionAlgebra f V hV
  letI := principalOpenSectionAlgebra_isScalarTower f V hV
  change (kummerModelBaseChange ((Spec.structureSheaf R).val.obj (op V)) e
    ((Algebra.TensorProduct.cancelBaseChange R (Localization.Away f)
      ((Spec.structureSheaf R).val.obj (op V))
      ((Spec.structureSheaf R).val.obj (op V)) A).symm (s ⊗ₜ[R] a))).re = _
  rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, kummerModelBaseChange_tmul_re]
  rfl

@[simp] theorem principalOpenKummerSectionModel_tmul_im {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f)
    (s : (Spec.structureSheaf R).val.obj (op V)) (a : A) :
    (principalOpenKummerSectionModel e V hV (s ⊗ₜ[R] a)).im =
      s * principalOpenSectionMap f V hV (e (1 ⊗ₜ[R] a)).im := by
  letI := principalOpenSectionAlgebra f V hV
  letI := principalOpenSectionAlgebra_isScalarTower f V hV
  change (kummerModelBaseChange ((Spec.structureSheaf R).val.obj (op V)) e
    ((Algebra.TensorProduct.cancelBaseChange R (Localization.Away f)
      ((Spec.structureSheaf R).val.obj (op V))
      ((Spec.structureSheaf R).val.obj (op V)) A).symm (s ⊗ₜ[R] a))).im = _
  rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, kummerModelBaseChange_tmul_im]
  rfl

/-- Actual restriction of structure-sheaf sections is an algebra map over
the affine coordinate ring. -/
def affineStructureSectionRestriction (V W : Opens (PrimeSpectrum.Top R)) (hWV : W ≤ V) :
    (Spec.structureSheaf R).val.obj (op V) →ₐ[R] (Spec.structureSheaf R).val.obj (op W) where
  __ := ((Spec.structureSheaf R).val.map (homOfLE hWV).op).hom
  commutes' r := ConcreteCategory.congr_hom (StructureSheaf.toOpen_res R V W (homOfLE hWV)) r

/-- Restrict the actual coefficient sections in the tensor-product algebra. -/
def principalOpenKummerSectionRestriction (V W : Opens (PrimeSpectrum.Top R)) (hWV : W ≤ V) :
    ((Spec.structureSheaf R).val.obj (op V) ⊗[R] A) →ₐ[R]
      ((Spec.structureSheaf R).val.obj (op W) ⊗[R] A) :=
  Algebra.TensorProduct.map (affineStructureSectionRestriction V W hWV) (AlgHom.id R A)

/-- The first Kummer coordinate commutes with every genuine coefficient restriction. -/
theorem principalOpenKummerSectionModel_re_restrict {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V W : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f)
    (hW : W ≤ PrimeSpectrum.basicOpen f) (hWV : W ≤ V)
    (x : (Spec.structureSheaf R).val.obj (op V) ⊗[R] A) :
    (principalOpenKummerSectionModel e W hW (principalOpenKummerSectionRestriction V W hWV x)).re =
      (Spec.structureSheaf R).val.map (homOfLE hWV).op
        (principalOpenKummerSectionModel e V hV x).re := by
  induction x with
  | zero => simp
  | tmul s a =>
    simp only [principalOpenKummerSectionRestriction, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, principalOpenKummerSectionModel_tmul_re, map_mul]
    rw [principalOpenSectionMap_restrict]
    rfl
  | add x y hx hy => simpa only [map_add, QuadraticAlgebra.re_add] using congrArg₂ (· + ·) hx hy

/-- The second Kummer coordinate commutes with every genuine coefficient restriction. -/
theorem principalOpenKummerSectionModel_im_restrict {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V W : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f)
    (hW : W ≤ PrimeSpectrum.basicOpen f) (hWV : W ≤ V)
    (x : (Spec.structureSheaf R).val.obj (op V) ⊗[R] A) :
    (principalOpenKummerSectionModel e W hW (principalOpenKummerSectionRestriction V W hWV x)).im =
      (Spec.structureSheaf R).val.map (homOfLE hWV).op
        (principalOpenKummerSectionModel e V hV x).im := by
  induction x with
  | zero => simp
  | tmul s a =>
    simp only [principalOpenKummerSectionRestriction, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, principalOpenKummerSectionModel_tmul_im, map_mul]
    rw [principalOpenSectionMap_restrict]
    rfl
  | add x y hx hy => simpa only [map_add, QuadraticAlgebra.im_add] using congrArg₂ (· + ·) hx hy

end EvenQuinticConic
