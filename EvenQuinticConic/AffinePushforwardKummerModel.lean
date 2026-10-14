import EvenQuinticConic.AffinePushforwardComparison

/-! # Kummer models of actual affine pushforward sections -/
noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EvenQuinticConic
universe v
variable {R A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f)

/-- Kummer coordinates on actual sections of the affine pushforward. -/
def affinePushforwardKummerRingModel :
    (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V)) ≃+*
      KummerAlgebra (principalOpenSectionMap f V hV u) :=
  (affinePushforwardTensorEquiv e V hV).symm.trans
    (principalOpenKummerSectionModel e V hV).toRingEquiv

/-- The inverse tensor comparison takes pulled-back scalars to tensor scalars. -/
theorem affinePushforwardTensorEquiv_symm_coefficient
    (r : (Spec.structureSheaf R).val.obj (op V)) :
    (affinePushforwardTensorEquiv e V hV).symm
      (affinePushforwardCoefficientMap (A := A) V r) = r ⊗ₜ[R] (1 : A) := by
  apply (affinePushforwardTensorEquiv e V hV).injective
  rw [RingEquiv.apply_symm_apply]
  change affinePushforwardCoefficientMap (A := A) V r =
    affinePushforwardTensorMap (A := A) V (r ⊗ₜ[R] (1 : A))
  simp

/-- The actual section coordinates respect the base structure-sheaf scalars. -/
theorem affinePushforwardKummerRingModel_coefficient
    (r : (Spec.structureSheaf R).val.obj (op V)) :
    affinePushforwardKummerRingModel e V hV (affinePushforwardCoefficientMap (A := A) V r) =
      algebraMap ((Spec.structureSheaf R).val.obj (op V)) _ r := by
  change principalOpenKummerSectionModel e V hV
    ((affinePushforwardTensorEquiv e V hV).symm _) = _
  rw [affinePushforwardTensorEquiv_symm_coefficient]
  exact (principalOpenKummerSectionModel e V hV).commutes r

/-- The first coordinate of actual pushforward sections commutes with restriction. -/
theorem affinePushforwardKummerRingModel_re_restrict
    (W : Opens (PrimeSpectrum.Top R)) (hW : W ≤ PrimeSpectrum.basicOpen f) (hWV : W ≤ V)
    (s : (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V))) :
    (affinePushforwardKummerRingModel e W hW
      (affinePushforwardSectionRestriction (A := A) V W hWV s)).re =
    (Spec.structureSheaf R).val.map (homOfLE hWV).op
      (affinePushforwardKummerRingModel e V hV s).re := by
  change (principalOpenKummerSectionModel e W hW
    ((affinePushforwardTensorEquiv e W hW).symm _)).re = _
  rw [affinePushforwardTensorEquiv_symm_restrict]
  exact principalOpenKummerSectionModel_re_restrict e V W hV hW hWV _

/-- The second coordinate of actual pushforward sections commutes with restriction. -/
theorem affinePushforwardKummerRingModel_im_restrict
    (W : Opens (PrimeSpectrum.Top R)) (hW : W ≤ PrimeSpectrum.basicOpen f) (hWV : W ≤ V)
    (s : (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V))) :
    (affinePushforwardKummerRingModel e W hW
      (affinePushforwardSectionRestriction (A := A) V W hWV s)).im =
    (Spec.structureSheaf R).val.map (homOfLE hWV).op
      (affinePushforwardKummerRingModel e V hV s).im := by
  change (principalOpenKummerSectionModel e W hW
    ((affinePushforwardTensorEquiv e W hW).symm _)).im = _
  rw [affinePushforwardTensorEquiv_symm_restrict]
  exact principalOpenKummerSectionModel_im_restrict e V W hV hW hWV _

end EvenQuinticConic
