import EvenQuinticConic.PlaneCurveScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Actual affine charts of a reduced closed projective locus

This construction applies to any scheme, in particular to the projective
Segre ambient space.  An affine open immersion and a radical ideal whose
zero locus is the actual inverse image of the closed set determine an
actual open immersion from the quotient spectrum into the reduced closed
subscheme.  The chart is constructed by a pullback and equality of ideal
sheaves; no chart isomorphism is supplied as an assumption.
-/

noncomputable section

namespace EvenQuinticConic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- The kernel ideal sheaf of a quasi-compact morphism with reduced source
is radical.  This is checked on actual rings of regular sections. -/
theorem schemeHom_kernel_radical {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] : f.ker.radical = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  apply Ideal.radical_eq_iff.mpr
  intro x hx
  obtain ⟨n, hx⟩ := hx
  change (f.app U).hom (x ^ n) = 0 at hx
  rw [map_pow] at hx
  exact (IsNilpotent.mk ((f.app U).hom x) n hx).eq_zero

/-- A reduced closed subscheme is determined scheme-theoretically by the
range of its closed immersion. -/
theorem reduced_closedImmersion_kernel_eq_of_range_eq
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsClosedImmersion f] [IsClosedImmersion g] [IsReduced X] [IsReduced Y]
    (h : Set.range f.base = Set.range g.base) : f.ker = g.ker := by
  have hs : f.ker.support = g.ker.support := by
    ext1
    simp only [Scheme.Hom.support_ker, h]
  calc
    f.ker = f.ker.radical := (schemeHom_kernel_radical f).symm
    _ = Scheme.IdealSheafData.vanishingIdeal f.ker.support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal g.ker.support := congrArg _ hs
    _ = g.ker.radical := Scheme.IdealSheafData.vanishingIdeal_support
    _ = g.ker := schemeHom_kernel_radical g

/-- The isomorphism between two actual reduced closed subschemes with the
same underlying locus. Its construction uses the universal property of
closed immersions after proving equality of their actual kernels. -/
def reducedClosedImmersionIsoOfRangeEq
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsClosedImmersion f] [IsClosedImmersion g] [IsReduced X] [IsReduced Y]
    (h : Set.range f.base = Set.range g.base) : X ≅ Y := by
  have hk := reduced_closedImmersion_kernel_eq_of_range_eq f g h
  let l := IsClosedImmersion.lift g f hk.symm.le
  letI : IsIso l := IsClosedImmersion.isIso_lift g f hk.symm
  exact asIso l

@[reassoc (attr := simp)]
theorem reducedClosedImmersionIsoOfRangeEq_hom_over
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsClosedImmersion f] [IsClosedImmersion g] [IsReduced X] [IsReduced Y]
    (h : Set.range f.base = Set.range g.base) :
    (reducedClosedImmersionIsoOfRangeEq f g h).hom ≫ g = f := by
  exact IsClosedImmersion.lift_fac g f _

section Chart

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
    (Z : Closeds X) (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (J : Ideal A) (hJ : J.IsRadical)
    (hZ : j.base ⁻¹' (Z : Set X) = PrimeSpectrum.zeroLocus J)

/-- The pullback defining the genuine intersection of the closed subscheme
with the ambient affine chart. -/
def reducedClosedChartPullback : Scheme :=
  pullback j (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

instance reducedClosedChartPullback_isReduced :
    IsReduced (reducedClosedChartPullback Z j) := by
  letI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    reduced_induced_scheme_isReduced X Z
  exact isReduced_of_isOpenImmersion
    (pullback.snd j (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)

omit [IsOpenImmersion j] in
include hZ in
/-- The range of the pullback closed immersion is the actual prescribed
affine zero locus. -/
theorem reducedClosedChartPullback_range :
    Set.range (pullback.fst j (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).base =
      PrimeSpectrum.zeroLocus J := by
  rw [Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hZ

/-- The quotient spectrum has the same actual affine zero locus. -/
theorem quotientSpectrum_range :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).base =
      PrimeSpectrum.zeroLocus J := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) = _
  rw [PrimeSpectrum.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]

/-- The actual quotient chart is isomorphic to the actual pullback of the
reduced closed subscheme, because the ideal is radical. -/
def reducedClosedChartPullbackIso :
    Spec (CommRingCat.of (A ⧸ J)) ≅ reducedClosedChartPullback Z j := by
  letI : _root_.IsReduced (A ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).mp hJ
  letI : IsReduced (pullback j (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    reducedClosedChartPullback_isReduced Z j
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact reducedClosedImmersionIsoOfRangeEq
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (pullback.fst j (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
    ((quotientSpectrum_range J).trans
      (reducedClosedChartPullback_range Z j J hZ).symm)

@[reassoc (attr := simp)]
theorem reducedClosedChartPullbackIso_hom_fst :
    (reducedClosedChartPullbackIso Z j J hJ hZ).hom ≫
        pullback.fst j (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  letI : _root_.IsReduced (A ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).mp hJ
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsReduced (pullback j (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    reducedClosedChartPullback_isReduced Z j
  exact reducedClosedImmersionIsoOfRangeEq_hom_over _ _ _

/-- The actual morphism of the quotient chart into the reduced closed
scheme, not merely a bijection of point sets. -/
def reducedClosedChartMap :
    Spec (CommRingCat.of (A ⧸ J)) ⟶
      (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  (reducedClosedChartPullbackIso Z j J hJ hZ).hom ≫
    pullback.snd j (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

instance reducedClosedChartMap_isOpenImmersion :
    IsOpenImmersion (reducedClosedChartMap Z j J hJ hZ) := by
  dsimp [reducedClosedChartMap]
  infer_instance

/-- The quotient chart retains its specified embedding in the ambient
scheme: the square commutes with the actual quotient map. -/
@[reassoc (attr := simp)]
theorem reducedClosedChartMap_over :
    reducedClosedChartMap Z j J hJ hZ ≫
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ j := by
  rw [reducedClosedChartMap, Category.assoc, ← pullback.condition,
    ← Category.assoc, reducedClosedChartPullbackIso_hom_fst]

/-- The quotient chart square is genuinely cartesian, including its
scheme structure and not just its underlying points. -/
theorem reducedClosedChartMap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (reducedClosedChartMap Z j J hJ hZ) j
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
  IsPullback.of_iso_pullback ⟨(reducedClosedChartMap_over Z j J hJ hZ).symm⟩
    (reducedClosedChartPullbackIso Z j J hJ hZ)
    (reducedClosedChartPullbackIso_hom_fst Z j J hJ hZ) rfl

/-- The chart image is precisely the inverse image of the ambient chart,
so these constructed charts cover whenever the ambient charts do. -/
theorem reducedClosedChartMap_opensRange :
    (reducedClosedChartMap Z j J hJ hZ).opensRange =
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ⁻¹ᵁ j.opensRange := by
  change ((reducedClosedChartPullbackIso Z j J hJ hZ).hom ≫
    pullback.snd j (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  ext1
  exact Scheme.Pullback.range_snd j
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

end Chart

section ProjectiveEquations

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    {f : B} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m)
    {ι : Type*} (F : ι → B) (d : ι → ℕ)
    (hF : ∀ i, F i ∈ 𝒜 (d i)) (hd : ∀ i, 0 < d i)

include hd in
/-- Homogeneous equations on `Proj` pull back under its genuine standard
affine chart to their homogeneous fractions. The proof compares the
actual basic opens, hence the actual scheme morphism's underlying map. -/
theorem projAway_preimage_zeroLocus :
    (Proj.awayι 𝒜 f hf hm).base ⁻¹'
        ProjectiveSpectrum.zeroLocus 𝒜 (Set.range F) =
      PrimeSpectrum.zeroLocus
        (Set.range fun i => HomogeneousLocalization.Away.isLocalizationElem hf (hF i)) := by
  ext p
  change (Set.range F ⊆ ((Proj.awayι 𝒜 f hf hm).base p).asHomogeneousIdeal) ↔
    Set.range (fun i => HomogeneousLocalization.Away.isLocalizationElem hf (hF i)) ⊆ p.asIdeal
  simp only [Set.range_subset_iff]
  apply forall_congr'
  intro i
  have hopen := congrArg (fun U : (Spec (CommRingCat.of
      (HomogeneousLocalization.Away 𝒜 f))).Opens => p ∈ U)
    (Proj.awayι_preimage_basicOpen 𝒜 hf hm (hF i) (hd i))
  have hn : F i ∉ ((Proj.awayι 𝒜 f hf hm).base p).asHomogeneousIdeal ↔
      HomogeneousLocalization.Away.isLocalizationElem hf (hF i) ∉ p.asIdeal :=
    Iff.of_eq hopen
  simpa using not_congr hn

include hd in
/-- After any specified affine coordinate map, including localization at
a nonzero minor, the pulled-back projective closed locus is defined by
the images of the actual homogeneous fractions. -/
theorem projAway_specMap_preimage_zeroLocus
    {A : Type u} [CommRing A]
    (φ : HomogeneousLocalization.Away 𝒜 f →+* A) :
    (Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι 𝒜 f hf hm).base ⁻¹'
        ProjectiveSpectrum.zeroLocus 𝒜 (Set.range F) =
      PrimeSpectrum.zeroLocus (Ideal.span
        (Set.range fun i => φ (HomogeneousLocalization.Away.isLocalizationElem hf (hF i)))) := by
  change (PrimeSpectrum.comap φ) ⁻¹'
      ((Proj.awayι 𝒜 f hf hm).base ⁻¹'
        ProjectiveSpectrum.zeroLocus 𝒜 (Set.range F)) = _
  rw [projAway_preimage_zeroLocus 𝒜 hf hm F d hF hd,
    PrimeSpectrum.preimage_comap_zeroLocus, PrimeSpectrum.zeroLocus_span,
    ← Set.range_comp]
  rfl

end ProjectiveEquations

end EvenQuinticConic
