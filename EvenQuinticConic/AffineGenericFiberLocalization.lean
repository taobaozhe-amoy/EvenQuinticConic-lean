import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The actual affine generic fibre as a localization

For an algebra `A → B`, localizing `B` at the images of the nonzero elements
of the domain `A` gives the actual base change of `Spec B` to `Spec (Frac A)`.
The tensor-product equivalence and both scheme projection identities are
constructed from the localization universal property; none is a hypothesis.
The construction also allows an empty generic fibre.
The algebraic constructions hold more generally for the total quotient ring
of any commutative base ring; the generic-point interpretation assumes a domain.
-/

noncomputable section
namespace EvenQuinticConic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Precisely the images of the nonzero denominators of the base domain. -/
def affineGenericFiberDenominators : Submonoid B :=
  Algebra.algebraMapSubmonoid B A⁰

/-- The actual affine coordinate algebra obtained by passing to the generic
point of the base. No injectivity of `A → B` is required for the definition. -/
abbrev AffineGenericFiberLocalization :=
  Localization (affineGenericFiberDenominators A B)

/-- The canonical fraction-field map to the localization of `B`. -/
def affineGenericFiberFractionMap : FractionRing A →+* AffineGenericFiberLocalization A B :=
  IsLocalization.map (M := A⁰) (T := affineGenericFiberDenominators A B)
    (AffineGenericFiberLocalization A B) (algebraMap A B)
    (by
      intro a ha
      change algebraMap A B a ∈ Algebra.algebraMapSubmonoid B A⁰
      exact ⟨a, ha, rfl⟩)

@[simp] theorem affineGenericFiberFractionMap_algebraMap (a : A) :
    affineGenericFiberFractionMap A B (algebraMap A (FractionRing A) a) =
      algebraMap B (AffineGenericFiberLocalization A B) (algebraMap A B a) := by
  exact IsLocalization.map_eq (M := A⁰)
    (T := affineGenericFiberDenominators A B) _ a

/-- Localizing the base commutes with tensoring by the actual algebra `B`. -/
def affineGenericFiberTensorAlgEquiv :
    B ⊗[A] FractionRing A ≃ₐ[B] AffineGenericFiberLocalization A B := by
  letI : IsLocalization (affineGenericFiberDenominators A B) (B ⊗[A] FractionRing A) :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (B ⊗[A] FractionRing A))
  exact IsLocalization.algEquiv (affineGenericFiberDenominators A B) _ _

/-- The tensor/localization isomorphism preserves the actual `B` pullback. -/
@[simp] theorem affineGenericFiberTensorAlgEquiv_includeLeft (b : B) :
    affineGenericFiberTensorAlgEquiv A B
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (B := FractionRing A) b) =
        algebraMap B (AffineGenericFiberLocalization A B) b :=
  (affineGenericFiberTensorAlgEquiv A B).commutes b

/-- The other structural map under the same isomorphism is the canonical
fraction-field localization map, not a separately chosen field action. -/
theorem affineGenericFiberTensorAlgEquiv_comp_includeRight :
    (affineGenericFiberTensorAlgEquiv A B).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := FractionRing A)).toRingHom =
      affineGenericFiberFractionMap A B := by
  apply IsLocalization.ringHom_ext A⁰
  ext a
  change affineGenericFiberTensorAlgEquiv A B
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := FractionRing A)
        (algebraMap A (FractionRing A) a)) = _
  rw [AlgHom.commutes]
  change affineGenericFiberTensorAlgEquiv A B
    (algebraMap B (B ⊗[A] FractionRing A) (algebraMap A B a)) = _
  rw [AlgEquiv.commutes]
  exact (affineGenericFiberFractionMap_algebraMap A B a).symm

@[simp] theorem affineGenericFiberTensorAlgEquiv_includeRight (a : FractionRing A) :
    affineGenericFiberTensorAlgEquiv A B
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := FractionRing A) a) =
        affineGenericFiberFractionMap A B a :=
  RingHom.congr_fun (affineGenericFiberTensorAlgEquiv_comp_includeRight A B) a

/-- The genuine categorical base change of the affine morphism to the
fraction field of its base. -/
abbrev AffineGenericFiber :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))))

/-- The actual generic fibre is the spectrum of the actual localization.
This isomorphism is obtained from the affine pullback theorem and the
proved tensor/localization algebra equivalence. -/
def affineGenericFiberLocalizationIso :
    AffineGenericFiber A B ≅ Spec (CommRingCat.of (AffineGenericFiberLocalization A B)) :=
  pullbackSpecIso A B (FractionRing A) ≪≫
    Scheme.Spec.mapIso
      (affineGenericFiberTensorAlgEquiv A B).toRingEquiv.symm.toCommRingCatIso.op

/-- The first projection of the actual base change is the original
localization morphism to `Spec B`. -/
@[reassoc (attr := simp)] theorem affineGenericFiberLocalizationIso_inv_fst :
    (affineGenericFiberLocalizationIso A B).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap B (AffineGenericFiberLocalization A B))) := by
  change Spec.map (CommRingCat.ofHom (affineGenericFiberTensorAlgEquiv A B).toRingHom) ≫
    (pullbackSpecIso A B (FractionRing A)).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  ext b
  exact affineGenericFiberTensorAlgEquiv_includeLeft A B b

/-- The second projection is precisely the canonical fraction-field
structure supplied by the localization universal property. -/
@[reassoc (attr := simp)] theorem affineGenericFiberLocalizationIso_inv_snd :
    (affineGenericFiberLocalizationIso A B).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (affineGenericFiberFractionMap A B)) := by
  change Spec.map (CommRingCat.ofHom (affineGenericFiberTensorAlgEquiv A B).toRingHom) ≫
    (pullbackSpecIso A B (FractionRing A)).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (affineGenericFiberTensorAlgEquiv_comp_includeRight A B)

/-- The forward isomorphism also preserves the morphism to the original
coordinate spectrum. -/
@[reassoc (attr := simp)] theorem affineGenericFiberLocalizationIso_hom_fst :
    (affineGenericFiberLocalizationIso A B).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (AffineGenericFiberLocalization A B))) =
        pullback.fst _ _ := by
  rw [← affineGenericFiberLocalizationIso_inv_fst, Iso.hom_inv_id_assoc]

/-- The forward isomorphism is over the actual fraction field. -/
@[reassoc (attr := simp)] theorem affineGenericFiberLocalizationIso_hom_snd :
    (affineGenericFiberLocalizationIso A B).hom ≫
      Spec.map (CommRingCat.ofHom (affineGenericFiberFractionMap A B)) =
        pullback.snd _ _ := by
  rw [← affineGenericFiberLocalizationIso_inv_snd, Iso.hom_inv_id_assoc]

/-- The localization spectrum, with its canonical structure maps, is the
actual pullback square. This version can be pasted with further base maps. -/
theorem affineGenericFiberLocalization_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap B (AffineGenericFiberLocalization A B))))
      (Spec.map (CommRingCat.ofHom (affineGenericFiberFractionMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) := by
  exact (IsPullback.of_hasPullback _ _).of_iso
    (affineGenericFiberLocalizationIso A B) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

end EvenQuinticConic
