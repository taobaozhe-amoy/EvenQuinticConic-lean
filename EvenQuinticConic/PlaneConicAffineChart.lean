import EvenQuinticConic.ProjectiveClosedChart
import EvenQuinticConic.IncidenceParameterFieldIdentification
import EvenQuinticConic.QuotientLocalization

/-!
# Actual localized affine charts of a plane equation

The ambient chart is the actual standard open of the projective plane.
After localizing a two-variable polynomial chart, reducedness of the
localized equation quotient suffices to construct its open immersion into
the actual reduced projective plane locus. No assertion about radicality
of the unlocalized equation is made.
-/

noncomputable section
namespace EvenQuinticConic

open AlgebraicGeometry CategoryTheory MvPolynomial
open Incidence

variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual homogeneous chart fractions in the two retained coordinates. -/
def planePolynomialChartRingEquiv (p : Fin 3) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) K) (X p) ≃+*
      MvPolynomial (Fin 2) K :=
  (projectiveCoordinateQuotientRingEquiv p).trans
    (incidenceParameterPolynomialChartAlgEquiv p).symm.toRingEquiv

@[simp] theorem planePolynomialChartRingEquiv_fraction (p : Fin 3)
    (d : ℕ) (Q : MvPolynomial (Fin 3) K) (hQ : Q.IsHomogeneous d) :
    planePolynomialChartRingEquiv p
      (HomogeneousLocalization.Away.isLocalizationElem (isHomogeneous_X K p) hQ) =
      dehomogenizeAt p Q := by
  simp only [planePolynomialChartRingEquiv, RingEquiv.trans_apply,
    projectiveCoordinateQuotientRingEquiv_isLocalizationElem]
  exact incidenceParameterPolynomialChartAlgEquiv_symm_mk p Q

/-- The genuine polynomial affine chart immersion into the projective plane. -/
def planePolynomialChartMap (p : Fin 3) :
    Spec (CommRingCat.of (MvPolynomial (Fin 2) K)) ⟶ ProjectivePlaneScheme K :=
  (Scheme.Spec.mapIso
    (incidenceParameterPolynomialChartAlgEquiv (K := K) p).toRingEquiv.toCommRingCatIso.op).inv ≫
      projectiveCoordinateQuotientChartMap p

instance planePolynomialChartMap_isOpenImmersion (p : Fin 3) :
    IsOpenImmersion (planePolynomialChartMap (K := K) p) := by
  unfold planePolynomialChartMap
  infer_instance

theorem planePolynomialChartMap_eq (p : Fin 3) :
    planePolynomialChartMap (K := K) p =
      Spec.map (CommRingCat.ofHom (planePolynomialChartRingEquiv p).toRingHom) ≫
        Proj.awayι (homogeneousSubmodule (Fin 3) K) (X p)
          (isHomogeneous_X K p) (by decide) := by
  change (Spec.map (CommRingCat.ofHom
    (incidenceParameterPolynomialChartAlgEquiv (K := K) p).symm.toRingHom) ≫
      projectiveCoordinateQuotientChartMap p) = _
  rw [projectiveCoordinateQuotientChartMap_eq, ← Category.assoc, ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem planePolynomialChartMap_comp_structure (p : Fin 3) :
    planePolynomialChartMap (K := K) p ≫ projectivePlaneStructure K =
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 2) K))) := by
  change (Spec.map (CommRingCat.ofHom
    (incidenceParameterPolynomialChartAlgEquiv (K := K) p).symm.toRingHom) ≫
      projectiveCoordinateQuotientChartMap p) ≫
        projectiveCoordinateStructure (K := K) (ι := Fin 3) = _
  rw [Category.assoc, projectiveCoordinateQuotientChartMap_comp_structure,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (incidenceParameterPolynomialChartAlgEquiv p).symm.commutes c

/-- A further principal open in the genuine polynomial projective chart. -/
def planeLocalizedPolynomialChartMap (p : Fin 3) (m : MvPolynomial (Fin 2) K) :
    Spec (CommRingCat.of (Localization.Away m)) ⟶ ProjectivePlaneScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin 2) K)
    (Localization.Away m))) ≫ planePolynomialChartMap p

instance planeLocalizedPolynomialChartMap_isOpenImmersion
    (p : Fin 3) (m : MvPolynomial (Fin 2) K) :
    IsOpenImmersion (planeLocalizedPolynomialChartMap p m) := by
  unfold planeLocalizedPolynomialChartMap
  infer_instance

/-- The literal equation ideal after dehomogenizing and localizing. -/
def planeLocalizedEquationIdeal (Q : PlanePolynomial K) (p : Fin 3)
    (m : MvPolynomial (Fin 2) K) : Ideal (Localization.Away m) :=
  localizedEquationIdeal (Ideal.span {dehomogenizeAt p Q}) m

/-- Pulling back the actual projective equation gives exactly its displayed
localized equation, before taking any radical. -/
theorem planeLocalizedPolynomialChartMap_preimage (Q : PlanePolynomial K)
    (d : ℕ) (hQ : Q.IsHomogeneous d) (hd : 0 < d)
    (p : Fin 3) (m : MvPolynomial (Fin 2) K) :
    (planeLocalizedPolynomialChartMap p m).base ⁻¹'
        (planeCurveClosedSet Q : Set _) =
      PrimeSpectrum.zeroLocus (planeLocalizedEquationIdeal Q p m) := by
  let φ := (algebraMap (MvPolynomial (Fin 2) K) (Localization.Away m)).comp
    (planePolynomialChartRingEquiv p).toRingHom
  have hj : planeLocalizedPolynomialChartMap p m =
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (homogeneousSubmodule (Fin 3) K) (X p)
          (isHomogeneous_X K p) (by decide) := by
    rw [planeLocalizedPolynomialChartMap, planePolynomialChartMap_eq,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  rw [hj]
  have hr : Set.range (fun _ : Unit => Q) = ({Q} : Set (PlanePolynomial K)) := by
    ext f
    simp
  change (Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (homogeneousSubmodule (Fin 3) K) (X p)
        (isHomogeneous_X K p) (by decide)).base ⁻¹'
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 3) K) {Q} = _
  rw [← hr, projAway_specMap_preimage_zeroLocus (homogeneousSubmodule (Fin 3) K)
    (isHomogeneous_X K p) (by decide) (fun _ : Unit => Q) (fun _ => d)
    (fun _ => hQ) (fun _ => hd) φ]
  simp only [φ, RingHom.comp_apply,
    Set.range_const, planeLocalizedEquationIdeal, localizedEquationIdeal,
    Ideal.map_span, Set.image_singleton]
  have hf : (planePolynomialChartRingEquiv (K := K) p).toRingHom
      (HomogeneousLocalization.Away.isLocalizationElem (isHomogeneous_X K p) hQ) =
      dehomogenizeAt p Q := planePolynomialChartRingEquiv_fraction p d Q hQ
  rw [hf]

@[reassoc (attr := simp)]
theorem planeLocalizedPolynomialChartMap_comp_structure (p : Fin 3)
    (m : MvPolynomial (Fin 2) K) :
    planeLocalizedPolynomialChartMap p m ≫ projectivePlaneStructure K =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away m))) := by
  rw [planeLocalizedPolynomialChartMap, Category.assoc,
    planePolynomialChartMap_comp_structure, ← Spec.map_comp]
  congr 1

/-- The affine plane-equation chart, localized at its actual minor class. -/
abbrev PlaneEquationMinorAlgebra (Q : PlanePolynomial K) (p : Fin 3)
    (m : MvPolynomial (Fin 2) K) :=
  Localization.Away (Ideal.Quotient.mk (Ideal.span {dehomogenizeAt p Q}) m)

/-- Reducedness is required only after localizing the actual equation. -/
theorem planeLocalizedEquationIdeal_isRadical (Q : PlanePolynomial K)
    (p : Fin 3) (m : MvPolynomial (Fin 2) K)
    [_root_.IsReduced (PlaneEquationMinorAlgebra Q p m)] :
    (planeLocalizedEquationIdeal Q p m).IsRadical := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  change _root_.IsReduced
    (Localization.Away m ⧸ localizedEquationIdeal (Ideal.span {dehomogenizeAt p Q}) m)
  exact isReduced_of_injective
    (quotientLocalizationRingEquiv (Ideal.span {dehomogenizeAt p Q}) m)
    (quotientLocalizationRingEquiv (Ideal.span {dehomogenizeAt p Q}) m).injective

/-- The literal localized equation quotient maps into the actual projective
plane locus by an open immersion constructed from its affine equations. -/
def planeEquationMinorChartMap (Q : PlanePolynomial K) (d : ℕ)
    (hQ : Q.IsHomogeneous d) (hd : 0 < d) (p : Fin 3)
    (m : MvPolynomial (Fin 2) K)
    [_root_.IsReduced (PlaneEquationMinorAlgebra Q p m)] :
    Spec (CommRingCat.of (PlaneEquationMinorAlgebra Q p m)) ⟶ PlaneCurveScheme Q :=
  (Scheme.Spec.mapIso (quotientLocalizationRingEquiv
    (Ideal.span {dehomogenizeAt p Q}) m).toCommRingCatIso.op).hom ≫
      reducedClosedChartMap (planeCurveClosedSet Q) (planeLocalizedPolynomialChartMap p m)
        (planeLocalizedEquationIdeal Q p m) (planeLocalizedEquationIdeal_isRadical Q p m)
        (planeLocalizedPolynomialChartMap_preimage Q d hQ hd p m)

instance planeEquationMinorChartMap_isOpenImmersion (Q : PlanePolynomial K) (d : ℕ)
    (hQ : Q.IsHomogeneous d) (hd : 0 < d) (p : Fin 3)
    (m : MvPolynomial (Fin 2) K)
    [_root_.IsReduced (PlaneEquationMinorAlgebra Q p m)] :
    IsOpenImmersion (planeEquationMinorChartMap Q d hQ hd p m) := by
  unfold planeEquationMinorChartMap
  infer_instance

/-- Its image is exactly the intersection with the specified actual ambient
principal chart; no density in an unrelated scheme is asserted. -/
theorem planeEquationMinorChartMap_opensRange (Q : PlanePolynomial K) (d : ℕ)
    (hQ : Q.IsHomogeneous d) (hd : 0 < d) (p : Fin 3)
    (m : MvPolynomial (Fin 2) K)
    [_root_.IsReduced (PlaneEquationMinorAlgebra Q p m)] :
    (planeEquationMinorChartMap Q d hQ hd p m).opensRange =
      planeCurveInclusion Q ⁻¹ᵁ (planeLocalizedPolynomialChartMap p m).opensRange := by
  unfold planeEquationMinorChartMap
  rw [Scheme.Hom.opensRange_comp_of_isIso, reducedClosedChartMap_opensRange]
  rfl

/-- The constructed chart preserves the actual coefficient-field structure. -/
@[reassoc (attr := simp)]
theorem planeEquationMinorChartMap_comp_structure (Q : PlanePolynomial K) (d : ℕ)
    (hQ : Q.IsHomogeneous d) (hd : 0 < d) (p : Fin 3)
    (m : MvPolynomial (Fin 2) K)
    [_root_.IsReduced (PlaneEquationMinorAlgebra Q p m)] :
    planeEquationMinorChartMap Q d hQ hd p m ≫ planeCurveStructure Q =
      Spec.map (CommRingCat.ofHom (algebraMap K (PlaneEquationMinorAlgebra Q p m))) := by
  change ((Scheme.Spec.mapIso (quotientLocalizationRingEquiv
    (Ideal.span {dehomogenizeAt p Q}) m).toCommRingCatIso.op).hom ≫
      reducedClosedChartMap _ _ _ _ _) ≫
        ((Scheme.IdealSheafData.vanishingIdeal (planeCurveClosedSet Q)).subschemeι ≫
          projectivePlaneStructure K) = _
  rw [Category.assoc, ← Category.assoc (reducedClosedChartMap _ _ _ _ _),
    reducedClosedChartMap_over, Category.assoc,
    planeLocalizedPolynomialChartMap_comp_structure]
  change Spec.map (CommRingCat.ofHom (quotientLocalizationRingEquiv
    (Ideal.span {dehomogenizeAt p Q}) m).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away m)))) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact quotientLocalizationRingEquiv_mk (Ideal.span {dehomogenizeAt p Q}) m (C c)

end EvenQuinticConic
