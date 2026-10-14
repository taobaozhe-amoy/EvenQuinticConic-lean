import EvenQuinticConic.AffinePushforwardTensor
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Actual affine pushforward sections on principal opens

The canonical tensor-to-section map is an isomorphism over every principal
open. Both its domain and codomain are localizations of the affine algebra
at the same element. This requires neither finiteness nor flatness.
-/

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace EvenQuinticConic

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The actual tensor comparison on a principal open is bijective. -/
theorem affinePushforwardTensorMap_basicOpen_bijective (f : R) :
    Function.Bijective
      (affinePushforwardTensorMap (A := A) (PrimeSpectrum.basicOpen f)) := by
  letI : Algebra A ((Spec.structureSheaf R).val.obj
      (op (PrimeSpectrum.basicOpen f)) ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization.Away (algebraMap R A f)
      ((Spec.structureSheaf R).val.obj (op (PrimeSpectrum.basicOpen f)) ⊗[R] A) :=
    IsLocalization.Away.tensorRight f _
  haveI : IsLocalization.Away (algebraMap R A f)
      ((Spec.structureSheaf A).val.obj
        (op (affinePushforwardOpen (A := A) (PrimeSpectrum.basicOpen f)))) := by
    change IsLocalization.Away (algebraMap R A f)
      ((Spec.structureSheaf A).val.obj (op (PrimeSpectrum.basicOpen (algebraMap R A f))))
    infer_instance
  apply IsLocalization.bijective (Submonoid.powers (algebraMap R A f))
    (affinePushforwardTensorMap (A := A) (PrimeSpectrum.basicOpen f))
  ext a
  change affinePushforwardTensorMap (A := A) (PrimeSpectrum.basicOpen f)
    (1 ⊗ₜ[R] a) = StructureSheaf.toOpen A _ a
  simp

/-- Identify tensor sections with genuine sections over the inverse image
of a principal open using the canonical comparison itself. -/
def affinePushforwardPrincipalEquiv (f : R) :
    ((Spec.structureSheaf R).val.obj (op (PrimeSpectrum.basicOpen f)) ⊗[R] A) ≃+*
      (Spec.structureSheaf A).val.obj
        (op (affinePushforwardOpen (A := A) (PrimeSpectrum.basicOpen f))) :=
  RingEquiv.ofBijective _ (affinePushforwardTensorMap_basicOpen_bijective (A := A) f)

@[simp] theorem affinePushforwardPrincipalEquiv_apply (f : R)
    (x : (Spec.structureSheaf R).val.obj (op (PrimeSpectrum.basicOpen f)) ⊗[R] A) :
    affinePushforwardPrincipalEquiv (A := A) f x =
      affinePushforwardTensorMap (A := A) (PrimeSpectrum.basicOpen f) x := rfl

/-- The inverse sends a pulled-back coefficient times a constant to its
pure tensor. -/
@[simp] theorem affinePushforwardPrincipalEquiv_symm_mul (f : R)
    (s : (Spec.structureSheaf R).val.obj (op (PrimeSpectrum.basicOpen f))) (a : A) :
    (affinePushforwardPrincipalEquiv (A := A) f).symm
      (affinePushforwardCoefficientMap (A := A) (PrimeSpectrum.basicOpen f) s *
        StructureSheaf.toOpen A
          (affinePushforwardOpen (A := A) (PrimeSpectrum.basicOpen f)) a) = s ⊗ₜ[R] a := by
  rw [← affinePushforwardTensorMap_tmul]
  simpa only [affinePushforwardPrincipalEquiv_apply] using
    (affinePushforwardPrincipalEquiv (A := A) f).symm_apply_apply (s ⊗ₜ[R] a)

/-- Principal-open identifications commute with actual restrictions. -/
theorem affinePushforwardPrincipalEquiv_restrict (f g : R)
    (hgf : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (x : (Spec.structureSheaf R).val.obj (op (PrimeSpectrum.basicOpen f)) ⊗[R] A) :
    affinePushforwardSectionRestriction (A := A)
      (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) hgf
      (affinePushforwardPrincipalEquiv (A := A) f x) =
    affinePushforwardPrincipalEquiv (A := A) g
      (principalOpenKummerSectionRestriction
        (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) hgf x) :=
  affinePushforwardTensorMap_restrict _ _ hgf x

/-- The inverses also commute with actual principal-open restrictions. -/
theorem affinePushforwardPrincipalEquiv_symm_restrict (f g : R)
    (hgf : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (s : (Spec.structureSheaf A).val.obj
      (op (affinePushforwardOpen (A := A) (PrimeSpectrum.basicOpen f)))) :
    (affinePushforwardPrincipalEquiv (A := A) g).symm
      (affinePushforwardSectionRestriction (A := A)
        (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) hgf s) =
    principalOpenKummerSectionRestriction
      (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) hgf
      ((affinePushforwardPrincipalEquiv (A := A) f).symm s) := by
  apply (affinePushforwardPrincipalEquiv (A := A) g).injective
  simp only [RingEquiv.apply_symm_apply]
  rw [← affinePushforwardPrincipalEquiv_restrict, RingEquiv.apply_symm_apply]

end EvenQuinticConic
