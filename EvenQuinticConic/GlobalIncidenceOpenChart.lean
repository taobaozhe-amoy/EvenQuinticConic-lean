import EvenQuinticConic.ProjectiveClosedChart
import EvenQuinticConic.ProjectiveCoordinateQuotient
import EvenQuinticConic.GlobalIncidenceScheme
import EvenQuinticConic.GlobalIncidenceMinorAlgebra

/-!
# The actual global incidence minor chart

The ambient coordinate chart is the genuine standard open of polynomial
`Proj`, expressed as the quotient by the pivot coordinate minus one.  We
then invert the actual homogeneous cubic minor.  Pullback of all global
homogeneous equations is computed through the actual projective chart map.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial

variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual cubic minor in the ambient normalized Segre coordinate ring. -/
def globalAmbientMinorElement (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) : ProjectiveCoordinateQuotient (K := K) (k, p) :=
  Ideal.Quotient.mk _ (globalIncidenceMinor M i j k)

/-- The ambient affine ring of the simultaneous pivot-and-minor open. -/
abbrev GlobalAmbientMinorRing (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) :=
  Localization.Away (globalAmbientMinorElement M p i j k)

/-- The specified polynomial coordinate map into the actual localized chart. -/
def globalAmbientMinorPolynomialMap (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) :
    MvPolynomial SegreIndex K →+* GlobalAmbientMinorRing M p i j k :=
  (algebraMap (ProjectiveCoordinateQuotient (K := K) (k, p)) _).comp
    (Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) (k, p)))

/-- The actual open immersion into the ambient projective Segre space. -/
def globalAmbientMinorChart (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) :
    Spec (CommRingCat.of (GlobalAmbientMinorRing M p i j k)) ⟶ SegreProjectiveScheme K :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (ProjectiveCoordinateQuotient (K := K) (k, p)) _)) ≫
      projectiveCoordinateQuotientChartMap (K := K) (k, p)

instance globalAmbientMinorChart_isOpenImmersion
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    IsOpenImmersion (globalAmbientMinorChart M p i j k) := by
  unfold globalAmbientMinorChart
  infer_instance

/-- The localized equations are the images of the literal global ideal;
no radical is added in this definition. -/
def globalAmbientMinorEquationIdeal
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    Ideal (GlobalAmbientMinorRing M p i j k) :=
  Ideal.map (globalAmbientMinorPolynomialMap M p i j k)
    (Ideal.span (segreIncidenceEquationSet M))

/-- The map from homogeneous fractions through the normalized chart and
localization evaluates each homogeneous equation to its literal image. -/
theorem globalAmbientMinor_fraction (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) (d : ℕ) (F : MvPolynomial SegreIndex K)
    (hF : F.IsHomogeneous d) :
    algebraMap (ProjectiveCoordinateQuotient (K := K) (k, p))
      (GlobalAmbientMinorRing M p i j k)
      (projectiveCoordinateQuotientRingEquiv (k, p)
        (HomogeneousLocalization.Away.isLocalizationElem
          (isHomogeneous_X K (k, p)) hF)) =
      globalAmbientMinorPolynomialMap M p i j k F := by
  rw [projectiveCoordinateQuotientRingEquiv_isLocalizationElem]
  rfl

/-- The actual inverse image of the global projective closed locus is
exactly the zero locus of the localized displayed equations. -/
theorem globalAmbientMinorChart_preimage
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    (globalAmbientMinorChart M p i j k).base ⁻¹' (globalIncidenceClosedSet M : Set _) =
      PrimeSpectrum.zeroLocus (globalAmbientMinorEquationIdeal M p i j k) := by
  let φ := (algebraMap (ProjectiveCoordinateQuotient (K := K) (k, p))
      (GlobalAmbientMinorRing M p i j k)).comp
    (projectiveCoordinateQuotientRingEquiv (K := K) (k, p)).toRingHom
  have hj : globalAmbientMinorChart M p i j k =
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (homogeneousSubmodule SegreIndex K) (X (k, p))
          (isHomogeneous_X K (k, p)) (by decide) := by
    rw [globalAmbientMinorChart, projectiveCoordinateQuotientChartMap_eq,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  rw [hj]
  change (Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (homogeneousSubmodule SegreIndex K) (X (k, p))
        (isHomogeneous_X K (k, p)) (by decide)).base ⁻¹'
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule SegreIndex K)
        (Set.range (segreEquationPolynomial M)) = _
  rw [projAway_specMap_preimage_zeroLocus (homogeneousSubmodule SegreIndex K)
    (isHomogeneous_X K (k, p)) (by decide) (segreEquationPolynomial M)
    segreEquationDegree (segreEquationPolynomial_homogeneous M) segreEquationDegree_pos φ]
  have hf : (fun e => φ (HomogeneousLocalization.Away.isLocalizationElem
      (isHomogeneous_X K (k, p)) (segreEquationPolynomial_homogeneous M e))) =
      (fun e => globalAmbientMinorPolynomialMap M p i j k (segreEquationPolynomial M e)) := by
    funext e
    exact globalAmbientMinor_fraction M p i j k _ _
      (segreEquationPolynomial_homogeneous M e)
  rw [hf, globalAmbientMinorEquationIdeal, Ideal.map_span,
    segreIncidenceEquationSet, ← Set.range_comp]
  rfl

/-- The normalized coordinate chart pulls back the cubic basic open to
the basic open of the literal normalized minor. -/
theorem globalCoordinateChart_preimage_minor
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    projectiveCoordinateQuotientChartMap (K := K) (k, p) ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule SegreIndex K) (globalIncidenceMinor M i j k) =
      PrimeSpectrum.basicOpen (globalAmbientMinorElement M p i j k) := by
  rw [projectiveCoordinateQuotientChartMap_eq, Scheme.preimage_comp,
    Proj.awayι_preimage_basicOpen _ (isHomogeneous_X K (k, p)) (by decide)
      (globalIncidenceMinor_homogeneous M i j k) (by decide)]
  ext x
  change (projectiveCoordinateQuotientRingEquiv (k, p)
      (HomogeneousLocalization.Away.isLocalizationElem (isHomogeneous_X K (k, p))
        (globalIncidenceMinor_homogeneous M i j k)) ∉ x.asIdeal) ↔ _
  rw [projectiveCoordinateQuotientRingEquiv_isLocalizationElem]
  rfl

/-- The actual ambient chart image is precisely the simultaneous nonzero
pivot and nonzero homogeneous minor locus. -/
theorem globalAmbientMinorChart_opensRange
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    (globalAmbientMinorChart M p i j k).opensRange =
      Proj.basicOpen (homogeneousSubmodule SegreIndex K) (X (k, p)) ⊓
        Proj.basicOpen (homogeneousSubmodule SegreIndex K) (globalIncidenceMinor M i j k) := by
  have hcoord : (projectiveCoordinateQuotientChartMap (K := K) (k, p)).opensRange =
      Proj.basicOpen (homogeneousSubmodule SegreIndex K) (X (k, p)) := by
    unfold projectiveCoordinateQuotientChartMap
    rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]
  have hloc : (Spec.map (CommRingCat.ofHom
      (algebraMap (ProjectiveCoordinateQuotient (K := K) (k, p))
        (GlobalAmbientMinorRing M p i j k)))).opensRange =
      PrimeSpectrum.basicOpen (globalAmbientMinorElement M p i j k) := by
    ext1
    exact PrimeSpectrum.localization_away_comap_range _ _
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (ProjectiveCoordinateQuotient (K := K) (k, p))
      (GlobalAmbientMinorRing M p i j k))) ≫
        projectiveCoordinateQuotientChartMap (K := K) (k, p)).opensRange = _
  rw [Scheme.Hom.opensRange_comp, hloc,
    ← globalCoordinateChart_preimage_minor M p i j k,
    Scheme.Hom.image_preimage_eq_opensRange_inter, hcoord]

/-- After inverting the actual nonzero coefficient minor, the actual
localized global equation ideal is radical. This follows from the proved
domain structure of its explicitly identified quotient. -/
theorem globalAmbientMinorEquationIdeal_isRadical
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (k : Fin 3)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    (globalAmbientMinorEquationIdeal M p (k.succAbove 0) (k.succAbove 1) k).IsRadical := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  letI : IsDomain (SegreIncidenceMinorLocalization M k p) :=
    segreIncidenceMinorLocalization_isDomain M k p h
  letI : IsDomain (GlobalIncidenceAmbientMinorQuotient M k p) :=
    Function.Injective.isDomain (globalIncidenceAmbientMinorQuotientAlgEquiv M k p).toRingHom
      (globalIncidenceAmbientMinorQuotientAlgEquiv M k p).injective
  exact inferInstanceAs (_root_.IsReduced (GlobalIncidenceAmbientMinorQuotient M k p))

/-- The explicit Segre minor algebra maps into the actual global incidence
scheme by the constructed reduced-closed-chart comparison. -/
def globalIncidenceMinorChartMap
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (k : Fin 3)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    Spec (CommRingCat.of (SegreIncidenceMinorLocalization M k p)) ⟶ GlobalIncidenceScheme M :=
  (Scheme.Spec.mapIso (globalIncidenceAmbientMinorQuotientAlgEquiv M k p).toRingEquiv.toCommRingCatIso.op).hom ≫
    reducedClosedChartMap (globalIncidenceClosedSet M)
      (globalAmbientMinorChart M p (k.succAbove 0) (k.succAbove 1) k)
      (globalAmbientMinorEquationIdeal M p (k.succAbove 0) (k.succAbove 1) k)
      (globalAmbientMinorEquationIdeal_isRadical M p k h)
      (globalAmbientMinorChart_preimage M p (k.succAbove 0) (k.succAbove 1) k)

instance globalIncidenceMinorChartMap_isOpenImmersion
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (k : Fin 3)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    IsOpenImmersion (globalIncidenceMinorChartMap M p k h) := by
  unfold globalIncidenceMinorChartMap
  infer_instance

/-- This chart image is the previously defined genuine open of the global
incidence scheme, with its specified pivot and actual cubic minor. -/
theorem globalIncidenceMinorChartMap_opensRange
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (k : Fin 3)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    (globalIncidenceMinorChartMap M p k h).opensRange =
      globalIncidenceMinorOpen M p (k.succAbove 0) (k.succAbove 1) k := by
  change ((Scheme.Spec.mapIso
    (globalIncidenceAmbientMinorQuotientAlgEquiv M k p).toRingEquiv.toCommRingCatIso.op).hom ≫
      reducedClosedChartMap _ _ _ _ _).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, reducedClosedChartMap_opensRange,
    globalAmbientMinorChart_opensRange]
  rfl

/-- The actual global minor open is the spectrum of the explicitly
computed Segre incidence localization. Its radicality and geometric chart
comparison are proved, not hypotheses. -/
def globalIncidenceMinorOpenIso
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (k : Fin 3)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    (globalIncidenceMinorOpen M p (k.succAbove 0) (k.succAbove 1) k).toScheme ≅
      Spec (CommRingCat.of (SegreIncidenceMinorLocalization M k p)) :=
  (IsOpenImmersion.isoOfRangeEq (globalIncidenceMinorChartMap M p k h)
    (globalIncidenceMinorOpen M p (k.succAbove 0) (k.succAbove 1) k).ι
    (by
      rw [Scheme.Opens.range_ι]
      exact congrArg SetLike.coe (globalIncidenceMinorChartMap_opensRange M p k h))).symm

@[reassoc (attr := simp)]
theorem globalIncidenceMinorOpenIso_inv_ι
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (k : Fin 3)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    (globalIncidenceMinorOpenIso M p k h).inv ≫
      (globalIncidenceMinorOpen M p (k.succAbove 0) (k.succAbove 1) k).ι =
      globalIncidenceMinorChartMap M p k h := by
  unfold globalIncidenceMinorOpenIso
  apply IsOpenImmersion.isoOfRangeEq_hom_fac
  rw [Scheme.Opens.range_ι]
  exact congrArg SetLike.coe (globalIncidenceMinorChartMap_opensRange M p k h)

/-- The ambient pivot-and-minor chart respects the original base field. -/
@[reassoc (attr := simp)]
theorem globalAmbientMinorChart_comp_structure
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    globalAmbientMinorChart M p i j k ≫ segreProjectiveStructure K =
      Spec.map (CommRingCat.ofHom (algebraMap K (GlobalAmbientMinorRing M p i j k))) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (ProjectiveCoordinateQuotient (K := K) (k, p))
      (GlobalAmbientMinorRing M p i j k))) ≫
        projectiveCoordinateQuotientChartMap (K := K) (k, p)) ≫
          projectiveCoordinateStructure (K := K) (ι := SegreIndex) = _
  rw [Category.assoc, projectiveCoordinateQuotientChartMap_comp_structure,
    ← Spec.map_comp]
  congr 1

/-- The actual global chart inclusion commutes with the structural map
over the original field, not merely after forgetting the field action. -/
@[reassoc (attr := simp)]
theorem globalIncidenceMinorChartMap_comp_structure
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (k : Fin 3)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    globalIncidenceMinorChartMap M p k h ≫ globalIncidenceStructure M =
      Spec.map (CommRingCat.ofHom (algebraMap K (SegreIncidenceMinorLocalization M k p))) := by
  change ((Scheme.Spec.mapIso
    (globalIncidenceAmbientMinorQuotientAlgEquiv M k p).toRingEquiv.toCommRingCatIso.op).hom ≫
      reducedClosedChartMap _ _ _ _ _) ≫
        ((Scheme.IdealSheafData.vanishingIdeal (globalIncidenceClosedSet M)).subschemeι ≫
          segreProjectiveStructure K) = _
  rw [Category.assoc, ← Category.assoc (reducedClosedChartMap _ _ _ _ _),
    reducedClosedChartMap_over, Category.assoc, globalAmbientMinorChart_comp_structure]
  change Spec.map (CommRingCat.ofHom
      (globalIncidenceAmbientMinorQuotientAlgEquiv M k p).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (GlobalAmbientMinorRing M p
        (k.succAbove 0) (k.succAbove 1) k)))) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact (globalIncidenceAmbientMinorQuotientAlgEquiv M k p).commutes c

/-- The inverse chart isomorphism is over the ground field through the
actual inclusion of the global open. -/
@[reassoc (attr := simp)]
theorem globalIncidenceMinorOpenIso_inv_comp_structure
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (k : Fin 3)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    (globalIncidenceMinorOpenIso M p k h).inv ≫
      (globalIncidenceMinorOpen M p (k.succAbove 0) (k.succAbove 1) k).ι ≫
        globalIncidenceStructure M =
      Spec.map (CommRingCat.ofHom (algebraMap K (SegreIncidenceMinorLocalization M k p))) := by
  rw [globalIncidenceMinorOpenIso_inv_ι_assoc,
    globalIncidenceMinorChartMap_comp_structure]

end EvenQuinticConic.Incidence
