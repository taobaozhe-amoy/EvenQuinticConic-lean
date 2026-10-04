import EvenQuinticConic.PlaneThetaIneffectivity

/-!
# Homogeneous representatives for actual curve-chart sections

The closed immersion's surjection on affine coordinate rings and the genuine
projective-chart isomorphism give polynomial fractions for every regular
function on each actual curve chart. These are local representatives, not an
assumption of global quadratic-section surjectivity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open HomogeneousLocalization

namespace EvenQuinticConic

variable {K : Type} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual homogeneous chart ring surjects onto regular functions of the
actual reduced curve chart. -/
theorem planeCurveChartPullback_surjective (F : PlanePolynomial K) (i : Fin 3) :
    Function.Surjective (projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
      (planeCurveInclusion F) (X i)) := by
  let U : (ProjectivePlaneScheme K).affineOpens :=
    ⟨Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (X i),
      Proj.isAffineOpen_basicOpen _ _ (isHomogeneous_X K i) (by decide)⟩
  have hcurve := planeCurveInclusion_affine_app_surjective F U
  have hproj : Function.Surjective
      (Proj.awayToSection (homogeneousSubmodule (Fin 3) K) (X i)) :=
    (Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 3) K) (X i)
      (isHomogeneous_X K i) (by decide)).commRingCatIsoToRingEquiv.surjective
  exact hcurve.comp hproj

/-- Every actual chart regular function is the pullback of `P / Xᵢ^n`,
where `P` is genuinely homogeneous of degree `n`. -/
theorem planeCurveCoordinateOpen_homogeneous_representative
    (F : PlanePolynomial K) (i : Fin 3)
    (r : Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i)) :
    ∃ (n : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous n),
      projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
        (planeCurveInclusion F) (X i)
        (planeHomogeneousChartFraction i n P hP) = r := by
  obtain ⟨z, hz⟩ := planeCurveChartPullback_surjective F i r
  obtain ⟨n, P, hP, hfrac⟩ :=
    Away.mk_surjective (homogeneousSubmodule (Fin 3) K) (isHomogeneous_X K i) z
  have hPn : P.IsHomogeneous n := by simpa using hP
  refine ⟨n, P, hPn, ?_⟩
  exact (congrArg (projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
    (planeCurveInclusion F) (X i)) hfrac).trans hz

/-- Consequently every actual chart function has a homogeneous polynomial
expression in the actual normalized coordinates in the curve function field.
This is only a degree-dependent chart expression. -/
theorem planeCurveCoordinateOpen_generic_representative
    (F : PlanePolynomial K) [IsIntegral (PlaneCurveScheme F)] (i : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)]
    (r : Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i)) :
    ∃ (n : ℕ) (P : PlanePolynomial K), P.IsHomogeneous n ∧
      eval₂ (planeCurveGenericConstants F i) (planeCurveGenericCoordinates F i) P =
        (PlaneCurveScheme F).germToFunctionField (planeCurveCoordinateOpen F i) r := by
  obtain ⟨n, P, hP, hrepr⟩ := planeCurveCoordinateOpen_homogeneous_representative F i r
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ Proj.basicOpen
      (homogeneousSubmodule (Fin 3) K) (X i)) :=
    inferInstanceAs (Nonempty (planeCurveCoordinateOpen F i))
  refine ⟨n, P, hP, ?_⟩
  unfold planeCurveGenericConstants planeCurveGenericCoordinates
  rw [planeChart_map_eval₂_homogeneous i n P hP]
  exact congrArg ((PlaneCurveScheme F).germToFunctionField
    (planeCurveCoordinateOpen F i)) hrepr

/-- Each frame coefficient of an actual global quadratic section has a
homogeneous chart-fraction representative, obtained from its actual regular
function rather than supplied as lifting data. -/
theorem planeCurveQuadraticSection_chart_representative
    (F : PlanePolynomial K) (i : Fin 3)
    (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) :
    ∃ (n : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous n),
      projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
        (planeCurveInclusion F) (X i) (planeHomogeneousChartFraction i n P hP) =
        (planeCurveQuadraticFrame F i).coordinate (planeCurveCoordinateOpen F i) le_rfl
          ((PlaneCurveQuadraticSheaf F).val.map (homOfLE le_top).op s) :=
  planeCurveCoordinateOpen_homogeneous_representative F i _

end EvenQuinticConic
