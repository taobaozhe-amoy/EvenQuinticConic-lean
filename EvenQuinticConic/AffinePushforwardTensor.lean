import EvenQuinticConic.PrincipalOpenKummerSections

/-!
# The canonical map to actual affine pushforward sections

For `Spec A → Spec R`, the tensor product of `O(V)` with `A` maps to
the genuine structure-sheaf sections over the inverse image of `V`.
This construction and its restriction law require no finiteness or
flatness assumptions. Bijectivity is a separate assertion.
-/

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace EvenQuinticConic

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The inverse image of a base open under the actual affine spectral map. -/
def affinePushforwardOpen (V : Opens (PrimeSpectrum.Top R)) : Opens (PrimeSpectrum.Top A) :=
  Opens.comap (PrimeSpectrum.comap (algebraMap R A)) V

/-- The structure-sheaf map on an open of the base. -/
def affinePushforwardCoefficientMap (V : Opens (PrimeSpectrum.Top R)) :
    (Spec.structureSheaf R).val.obj (op V) →+*
      (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V)) :=
  StructureSheaf.comap (algebraMap R A) V (affinePushforwardOpen (A := A) V) (fun _ => id)

/-- The coefficient map respects the constants from the base ring. -/
theorem affinePushforwardCoefficientMap_algebraMap (V : Opens (PrimeSpectrum.Top R)) (r : R) :
    affinePushforwardCoefficientMap (A := A) V (algebraMap R _ r) =
      StructureSheaf.toOpen A (affinePushforwardOpen (A := A) V) (algebraMap R A r) := by
  exact ConcreteCategory.congr_hom (StructureSheaf.toOpen_comp_comap (algebraMap R A) V) r

/-- Restriction on the actual pushforward structure-sheaf sections. -/
def affinePushforwardSectionRestriction (V W : Opens (PrimeSpectrum.Top R)) (hWV : W ≤ V) :
    (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V)) →+*
      (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) W)) :=
  ((Spec.structureSheaf A).val.map
    (homOfLE (show affinePushforwardOpen (A := A) W ≤ affinePushforwardOpen (A := A) V
      from fun _ hx => hWV hx)).op).hom

/-- Pullback of coefficients commutes with genuine section restriction. -/
theorem affinePushforwardCoefficientMap_restrict
    (V W : Opens (PrimeSpectrum.Top R)) (hWV : W ≤ V)
    (s : (Spec.structureSheaf R).val.obj (op V)) :
    affinePushforwardSectionRestriction (A := A) V W hWV
      (affinePushforwardCoefficientMap (A := A) V s) =
    affinePushforwardCoefficientMap (A := A) W (affineStructureSectionRestriction V W hWV s) := by
  rfl

/-- Affine constants commute with genuine section restriction. -/
theorem affinePushforwardSectionRestriction_toOpen
    (V W : Opens (PrimeSpectrum.Top R)) (hWV : W ≤ V) (a : A) :
    affinePushforwardSectionRestriction (A := A) V W hWV
      (StructureSheaf.toOpen A (affinePushforwardOpen (A := A) V) a) =
      StructureSheaf.toOpen A (affinePushforwardOpen (A := A) W) a := by
  rfl

/-- The canonical tensor-to-pushforward map. Its codomain consists of actual
regular sections on the inverse image open, not an abstract tensor model. -/
def affinePushforwardTensorMap (V : Opens (PrimeSpectrum.Top R)) :
    ((Spec.structureSheaf R).val.obj (op V) ⊗[R] A) →+*
      (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V)) := by
  let c := (StructureSheaf.toOpen A (affinePushforwardOpen (A := A) V)).hom
  letI := (c.comp (algebraMap R A)).toAlgebra
  let f : (Spec.structureSheaf R).val.obj (op V) →ₐ[R]
      (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V)) :=
    { __ := affinePushforwardCoefficientMap (A := A) V
      commutes' := affinePushforwardCoefficientMap_algebraMap V }
  let g : A →ₐ[R] (Spec.structureSheaf A).val.obj
      (op (affinePushforwardOpen (A := A) V)) :=
    { __ := c
      commutes' := fun _ => rfl }
  exact (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom

/-- The canonical map sends a pure tensor to the product of the pulled-back
coefficient and the affine constant section. -/
@[simp] theorem affinePushforwardTensorMap_tmul (V : Opens (PrimeSpectrum.Top R))
    (s : (Spec.structureSheaf R).val.obj (op V)) (a : A) :
    affinePushforwardTensorMap (A := A) V (s ⊗ₜ[R] a) =
      affinePushforwardCoefficientMap (A := A) V s *
        StructureSheaf.toOpen A (affinePushforwardOpen (A := A) V) a := by
  rfl

/-- The canonical tensor comparison commutes with all open restrictions. -/
theorem affinePushforwardTensorMap_restrict
    (V W : Opens (PrimeSpectrum.Top R)) (hWV : W ≤ V)
    (x : (Spec.structureSheaf R).val.obj (op V) ⊗[R] A) :
    affinePushforwardSectionRestriction (A := A) V W hWV
      (affinePushforwardTensorMap (A := A) V x) =
    affinePushforwardTensorMap (A := A) W
      (principalOpenKummerSectionRestriction V W hWV x) := by
  induction x with
  | zero => simp
  | tmul s a =>
    simp only [principalOpenKummerSectionRestriction, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, affinePushforwardTensorMap_tmul, map_mul,
      affinePushforwardCoefficientMap_restrict]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end EvenQuinticConic
