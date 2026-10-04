import EvenQuinticConic.ProjectiveGenericChart
import EvenQuinticConic.ProjectiveStalkUnits
import EvenQuinticConic.PlaneCurveScheme

/-!
# Low-degree restriction into the actual plane curve function field

These results use actual projective chart sections, an actual scheme
morphism, and the actual function field. The source of injectivity is the
homogeneous prime at the image of the generic point, not an assumed
embedding of the affine cone fraction field.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open HomogeneousLocalization

universe u

namespace EvenQuinticConic

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero homogeneous polynomial of degree below the defining equation
restricts to a nonzero actual rational function. The equality specifying
the image of the generic prime will be proved for the concrete curve below. -/
theorem projective_fraction_pullback_ne_zero_of_degree_lt
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Proj (homogeneousSubmodule (Fin 3) K))
    (F : PlanePolynomial K) (hF : F ≠ 0)
    (hη : (p.base (genericPoint X)).asHomogeneousIdeal.toIdeal = Ideal.span {F})
    (j : Fin 3) [Nonempty (p ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j))]
    (d : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous d)
    (hP0 : P ≠ 0) (hdeg : P.totalDegree < F.totalDegree) :
    projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p (MvPolynomial.X j)
      (planeHomogeneousChartFraction j d P hP) ≠ 0 := by
  apply projective_chart_fraction_generic_pullback_ne_zero
    (homogeneousSubmodule (Fin 3) K) p (MvPolynomial.X j)
    ⟨d • 1, ⟨P, by simpa using hP⟩,
      ⟨(MvPolynomial.X j) ^ d, SetLike.pow_mem_graded d (isHomogeneous_X K j)⟩, ⟨d, rfl⟩⟩
  change P ∉ (p.base (genericPoint X)).asHomogeneousIdeal.toIdeal
  rw [hη]
  intro hmem
  exact hP0 (eq_zero_of_dvd_of_totalDegree_lt F P hF
    (Ideal.mem_span_singleton.mp hmem) hdeg)

/-- Low-degree homogeneous evaluation is injective for the actual chart
coordinates and the coefficient map pulled back from the base constants. -/
theorem projective_eval₂_injective_of_degree_lt
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Proj (homogeneousSubmodule (Fin 3) K))
    (F : PlanePolynomial K) (hF : F ≠ 0)
    (hη : (p.base (genericPoint X)).asHomogeneousIdeal.toIdeal = Ideal.span {F})
    (j : Fin 3) [Nonempty (p ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j))]
    (d : ℕ) (hd : d < F.totalDegree)
    (P : PlanePolynomial K) (hP : P.IsHomogeneous d)
    (hzero : eval₂
      ((projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p (MvPolynomial.X j)).comp
        (planeChartConstants j))
      (fun i ↦ projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p (MvPolynomial.X j)
        (planeChartRatio j i)) P = 0) : P = 0 := by
  by_contra hP0
  apply projective_fraction_pullback_ne_zero_of_degree_lt p F hF hη j d P hP hP0
    (hP.totalDegree_le.trans_lt hd)
  rw [← planeChart_eval₂_homogeneous j d P hP, eval₂_comp_left]
  exact hzero

/-- The genuine normalized coordinate functions on the actual curve scheme. -/
noncomputable def planeCurveGenericCoordinates (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F j)] :
    Fin 3 → (PlaneCurveScheme F).functionField := by
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j)) :=
    ‹Nonempty (planeCurveCoordinateOpen F j)›
  exact fun i ↦ projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K)
    (planeCurveInclusion F) (MvPolynomial.X j) (planeChartRatio j i)

/-- The actual coefficient map obtained by pulling constant chart sections
back along the concrete curve inclusion and taking their generic germs. -/
noncomputable def planeCurveGenericConstants (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F j)] :
    K →+* (PlaneCurveScheme F).functionField := by
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j)) :=
    ‹Nonempty (planeCurveCoordinateOpen F j)›
  exact (projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K)
    (planeCurveInclusion F) (MvPolynomial.X j)).comp (planeChartConstants j)

/-- Low-degree homogeneous restriction is injective on the actual reduced
plane-curve scheme. Integrality, chart nonemptiness, and the generic-prime
description are all derived from the explicit polynomial hypotheses. -/
theorem planeCurve_homogeneous_restriction_injective
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (j : Fin 3) (d : ℕ) (hd : d < F.totalDegree) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
    ∀ P : PlanePolynomial K, P.IsHomogeneous d →
      eval₂ (planeCurveGenericConstants F j) (planeCurveGenericCoordinates F j) P = 0 →
      P = 0 := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
  intro P hP hzero
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j)) :=
    planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
  have hF0 : F ≠ 0 := by
    intro h
    simp [h] at hFdeg
  have hη : ((planeCurveInclusion F).base (genericPoint (PlaneCurveScheme F))).asHomogeneousIdeal.toIdeal =
      Ideal.span {F} := by
    rw [planeCurveInclusion_genericPoint F e hF hFdeg hprime]
    rfl
  exact projective_eval₂_injective_of_degree_lt (planeCurveInclusion F) F hF0 hη
    j d hd P hP hzero

/-- In particular, the actual smooth-quintic argument's quartic injectivity
holds already for an integral homogeneous plane quintic. No smoothness,
cone-field identification, or assumed restriction injectivity is used. -/
theorem planeQuintic_actual_chart_quartic_injective
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : F.totalDegree = 5) (hprime : (Ideal.span {F}).IsPrime) (j : Fin 3) :
    letI := planeCurveScheme_isIntegral F 5 hF (by omega) hprime
    letI := planeCurveCoordinateOpen_nonempty F 5 hF (by omega) hprime j
    ∀ P : PlanePolynomial K, P.IsHomogeneous 4 →
      eval₂ (planeCurveGenericConstants F j) (planeCurveGenericCoordinates F j) P = 0 →
      P = 0 :=
  planeCurve_homogeneous_restriction_injective F 5 hF (by omega) hprime j 4 (by omega)

end EvenQuinticConic
