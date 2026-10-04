import EvenQuinticConic.PlaneChartRepresentatives
import EvenQuinticConic.PlaneHomogeneousKernel

/-!
# Actual curve charts cut out by linear forms

Every regular function on the actual chart `D(L)` has a homogeneous
representative `P/L^n`. Comparing genuine projective stalk fractions gives
its expression in any standard coordinate chart's actual function field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open HomogeneousLocalization
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic

variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual curve open on which a specified linear form is nonzero. -/
def planeCurveLinearOpen (F L : PlanePolynomial K) : (PlaneCurveScheme F).Opens :=
  planeCurveInclusion F ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 3) K) L

/-- Linear-form charts are affine, including an empty chart. -/
theorem planeCurveLinearOpen_isAffine (F L : PlanePolynomial K)
    (hL : L.IsHomogeneous 1) : IsAffineOpen (planeCurveLinearOpen F L) := by
  apply IsAffineOpen.preimage
  exact Proj.isAffineOpen_basicOpen _ _ hL (by decide)

/-- Actual pullback from the homogeneous chart ring is surjective. -/
theorem planeCurveLinearChartPullback_surjective (F L : PlanePolynomial K)
    (hL : L.IsHomogeneous 1) :
    Function.Surjective (projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
      (planeCurveInclusion F) L) := by
  let U : (ProjectivePlaneScheme K).affineOpens :=
    ⟨Proj.basicOpen (homogeneousSubmodule (Fin 3) K) L,
      Proj.isAffineOpen_basicOpen _ _ hL (by decide)⟩
  have hcurve := planeCurveInclusion_affine_app_surjective F U
  have hproj : Function.Surjective
      (Proj.awayToSection (homogeneousSubmodule (Fin 3) K) L) :=
    (Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 3) K) L
      hL (by decide)).commRingCatIsoToRingEquiv.surjective
  exact hcurve.comp hproj

/-- Every actual linear-chart regular function has an actual homogeneous
polynomial fraction representative. -/
theorem planeCurveLinearOpen_homogeneous_representative
    (F L : PlanePolynomial K) (hL : L.IsHomogeneous 1)
    (r : Γ(PlaneCurveScheme F, planeCurveLinearOpen F L)) :
    ∃ (n : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous n),
      projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
        (planeCurveInclusion F) L
        (Away.mk (homogeneousSubmodule (Fin 3) K) hL n P (by simpa using hP)) = r := by
  obtain ⟨z, hz⟩ := planeCurveLinearChartPullback_surjective F L hL r
  obtain ⟨n, P, hP, hfrac⟩ :=
    Away.mk_surjective (homogeneousSubmodule (Fin 3) K) hL z
  have hPn : P.IsHomogeneous n := by simpa using hP
  refine ⟨n, P, hPn, ?_⟩
  exact (congrArg (projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
    (planeCurveInclusion F) L) hfrac).trans hz

/-- Chart evaluation factors through the actual stalk of the ambient
projective scheme at the image of the source generic point. -/
theorem projectiveChartToFunctionField_via_stalk
    {Y : Scheme} [IsIntegral Y]
    (p : Y ⟶ Proj (homogeneousSubmodule (Fin 3) K)) (f : PlanePolynomial K)
    [Nonempty (p ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 3) K) f)]
    (z : Away (homogeneousSubmodule (Fin 3) K) f) :
    projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p f z =
      p.stalkMap (genericPoint Y)
        ((Proj.stalkIso' (homogeneousSubmodule (Fin 3) K)
          (p.base (genericPoint Y))).symm
            (HomogeneousLocalization.mapId (homogeneousSubmodule (Fin 3) K)
              (Submonoid.powers_le.mpr
                (genericPoint_image_mem_of_nonempty_preimage p
                  (Proj.basicOpen (homogeneousSubmodule (Fin 3) K) f))) z)) := by
  change Y.germToFunctionField _ (p.app _ (Proj.awayToSection _ _ z)) = _
  rw [generic_pullback_eq_stalkMap]
  apply congrArg (p.stalkMap (genericPoint Y))
  apply (Proj.stalkIso' (homogeneousSubmodule (Fin 3) K)
    (p.base (genericPoint Y))).eq_symm_apply.mpr
  change Proj.stalkIso' (homogeneousSubmodule (Fin 3) K) _
    ((ProjectiveSpectrum.Proj.structureSheaf (homogeneousSubmodule (Fin 3) K)).presheaf.germ
      _ _ _ (ProjectiveSpectrum.Proj.awayToSection _ _ z)) = _
  rw [Proj.stalkIso'_germ]
  rfl

/-- Comparing homogeneous fractions at one actual projective stalk gives
the usual change-of-denominator identity after actual generic pullback. -/
theorem projectiveChartToFunctionField_change_linear_denominator
    {Y : Scheme} [IsIntegral Y]
    (p : Y ⟶ Proj (homogeneousSubmodule (Fin 3) K))
    (L : PlanePolynomial K) (hL : L.IsHomogeneous 1) (j : Fin 3)
    [Nonempty (p ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 3) K) L)]
    [Nonempty (p ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (X j))]
    (n : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous n) :
    projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p L
        (Away.mk (homogeneousSubmodule (Fin 3) K) hL n P (by simpa using hP)) *
      (projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p (X j)
        (planeHomogeneousChartFraction j 1 L hL)) ^ n =
      projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p (X j)
        (planeHomogeneousChartFraction j n P hP) := by
  simp only [projectiveChartToFunctionField_via_stalk]
  rw [← map_pow, ← map_mul]
  apply congrArg (p.stalkMap (genericPoint Y))
  apply (Proj.stalkIso' (homogeneousSubmodule (Fin 3) K)
    (p.base (genericPoint Y))).injective
  simp only [map_mul, map_pow, RingEquiv.apply_symm_apply]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow]
  change Localization.mk P _ * (Localization.mk L _) ^ n = Localization.mk P _
  rw [Localization.mk_pow, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    RingHom.id_apply]
  ring

/-- Standard homogeneous fractions evaluate using the actual coefficient
field action and the actual normalized coordinates. -/
theorem planeCurve_homogeneous_fraction_generic_eq_aeval
    (F : PlanePolynomial K) [IsIntegral (PlaneCurveScheme F)] (j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F j)]
    (n : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous n) :
    letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ Proj.basicOpen
      (homogeneousSubmodule (Fin 3) K) (X j)) :=
        inferInstanceAs (Nonempty (planeCurveCoordinateOpen F j))
    projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K)
      (planeCurveInclusion F) (X j) (planeHomogeneousChartFraction j n P hP) =
        aeval (planeCurveGenericCoordinates F j) P := by
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ Proj.basicOpen
      (homogeneousSubmodule (Fin 3) K) (X j)) :=
    inferInstanceAs (Nonempty (planeCurveCoordinateOpen F j))
  have hh := planeChart_map_eval₂_homogeneous j n P hP
    (projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K)
      (planeCurveInclusion F) (X j))
  change eval₂ (planeCurveGenericConstants F j) (planeCurveGenericCoordinates F j) P = _ at hh
  rw [planeCurveGenericConstants_eq_algebraMap] at hh
  exact hh.symm

/-- A homogeneous fraction on a linear chart is related to any standard
chart by the precise denominator power, in the actual curve function field. -/
theorem planeCurveLinearOpen_homogeneous_fraction_generic
    (F L : PlanePolynomial K) (hL : L.IsHomogeneous 1)
    [IsIntegral (PlaneCurveScheme F)] (j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F j)] [Nonempty (planeCurveLinearOpen F L)]
    (n : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous n) :
    (PlaneCurveScheme F).germToFunctionField (planeCurveLinearOpen F L)
      (projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
        (planeCurveInclusion F) L
        (Away.mk (homogeneousSubmodule (Fin 3) K) hL n P (by simpa using hP))) *
      (aeval (planeCurveGenericCoordinates F j) L) ^ n =
        aeval (planeCurveGenericCoordinates F j) P := by
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ Proj.basicOpen
      (homogeneousSubmodule (Fin 3) K) (X j)) :=
    inferInstanceAs (Nonempty (planeCurveCoordinateOpen F j))
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ Proj.basicOpen
      (homogeneousSubmodule (Fin 3) K) L) :=
    inferInstanceAs (Nonempty (planeCurveLinearOpen F L))
  have hh := projectiveChartToFunctionField_change_linear_denominator
    (planeCurveInclusion F) L hL j n P hP
  rw [planeCurve_homogeneous_fraction_generic_eq_aeval,
    planeCurve_homogeneous_fraction_generic_eq_aeval] at hh
  exact hh

/-- Every actual linear-chart regular function admits the denominator
identity in any chosen standard chart's actual generic coordinates. -/
theorem planeCurveLinearOpen_generic_representative
    (F L : PlanePolynomial K) (hL : L.IsHomogeneous 1)
    [IsIntegral (PlaneCurveScheme F)] (j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F j)] [Nonempty (planeCurveLinearOpen F L)]
    (r : Γ(PlaneCurveScheme F, planeCurveLinearOpen F L)) :
    ∃ (n : ℕ) (P : PlanePolynomial K), P.IsHomogeneous n ∧
      (PlaneCurveScheme F).germToFunctionField (planeCurveLinearOpen F L) r *
        (aeval (planeCurveGenericCoordinates F j) L) ^ n =
          aeval (planeCurveGenericCoordinates F j) P := by
  obtain ⟨n, P, hP, hrepr⟩ := planeCurveLinearOpen_homogeneous_representative F L hL r
  refine ⟨n, P, hP, ?_⟩
  rw [← hrepr]
  exact planeCurveLinearOpen_homogeneous_fraction_generic F L hL j n P hP

/-- The actual regular function `Xᵢ/L` on the actual linear-form chart. -/
def planeCurveLinearRatio (F L : PlanePolynomial K) (hL : L.IsHomogeneous 1)
    (i : Fin 3) : Γ(PlaneCurveScheme F, planeCurveLinearOpen F L) :=
  projectiveChartPullback (homogeneousSubmodule (Fin 3) K) (planeCurveInclusion F) L
    (Away.mk (homogeneousSubmodule (Fin 3) K) hL 1 (X i)
      (by simpa using isHomogeneous_X K i))

/-- Generic coefficients of actual ratio functions satisfy the exact
linear change-of-frame identity. -/
theorem planeCurveLinearRatio_generic
    (F L : PlanePolynomial K) (hL : L.IsHomogeneous 1)
    [IsIntegral (PlaneCurveScheme F)] (j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F j)] [Nonempty (planeCurveLinearOpen F L)]
    (i : Fin 3) :
    (PlaneCurveScheme F).germToFunctionField (planeCurveLinearOpen F L)
      (planeCurveLinearRatio F L hL i) * aeval (planeCurveGenericCoordinates F j) L =
        planeCurveGenericCoordinates F j i := by
  simpa only [pow_one, aeval_X] using
    planeCurveLinearOpen_homogeneous_fraction_generic F L hL j 1 (X i) (isHomogeneous_X K i)

end EvenQuinticConic
