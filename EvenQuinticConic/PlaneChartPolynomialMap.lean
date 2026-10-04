import EvenQuinticConic.PlaneChartRepresentatives
import EvenQuinticConic.PlaneHomogeneousKernel
import EvenQuinticConic.ChartHomogenization

/-!
# Polynomial coordinates of actual affine curve charts

The map below takes each polynomial variable to the actual regular function
`Xⱼ/Xᵢ`. Surjectivity comes from actual homogeneous-fraction representatives.
Its homogeneous kernel is computed using the actual curve generic point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic

variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual constants on a curve coordinate chart. -/
def planeCurveChartConstants (F : PlanePolynomial K) (i : Fin 3) :
    K →+* Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
  (projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
    (planeCurveInclusion F) (X i)).comp (planeChartConstants i)

/-- The actual regular normalized coordinates on a curve chart. -/
def planeCurveChartCoordinates (F : PlanePolynomial K) (i j : Fin 3) :
    Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
  projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
    (planeCurveInclusion F) (X i) (planeChartRatio i j)

/-- Evaluation at actual regular coordinate-ratio sections. -/
def planeCurveChartPolynomialMap (F : PlanePolynomial K) (i : Fin 3) :
    PlanePolynomial K →+* Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
  eval₂Hom (planeCurveChartConstants F i) (planeCurveChartCoordinates F i)

@[simp]
theorem planeCurveChartPolynomialMap_X (F : PlanePolynomial K) (i j : Fin 3) :
    planeCurveChartPolynomialMap F i (X j) = planeCurveChartCoordinates F i j := by
  simp [planeCurveChartPolynomialMap]

@[simp]
theorem planeCurveChartCoordinates_self (F : PlanePolynomial K) (i : Fin 3) :
    planeCurveChartCoordinates F i i = 1 := by
  change (planeCurveInclusion F).app (planeCoordinateOpen K i)
    (planeCoordinateRatio K i i) = 1
  rw [planeCoordinateRatio_self, map_one]

/-- Homogeneous polynomials evaluate to their actual homogeneous fractions. -/
theorem planeCurveChartPolynomialMap_homogeneous (F : PlanePolynomial K)
    (i : Fin 3) (d : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous d) :
    planeCurveChartPolynomialMap F i P =
      projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
        (planeCurveInclusion F) (X i) (planeHomogeneousChartFraction i d P hP) :=
  planeChart_map_eval₂_homogeneous i d P hP _

/-- Actual polynomial coordinates generate the whole actual chart ring. -/
theorem planeCurveChartPolynomialMap_surjective (F : PlanePolynomial K) (i : Fin 3) :
    Function.Surjective (planeCurveChartPolynomialMap F i) := by
  intro r
  obtain ⟨d, P, hP, hr⟩ := planeCurveCoordinateOpen_homogeneous_representative F i r
  exact ⟨P, (planeCurveChartPolynomialMap_homogeneous F i d P hP).trans hr⟩

/-- The actual chart polynomial evaluation has the actual generic evaluation
as its germ; this is an equality of the specified maps. -/
theorem planeCurveChartPolynomialMap_generic (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] (P : PlanePolynomial K) :
    (PlaneCurveScheme F).germToFunctionField (planeCurveCoordinateOpen F i)
      (planeCurveChartPolynomialMap F i P) =
        aeval (planeCurveGenericCoordinates F i) P := by
  change (PlaneCurveScheme F).germToFunctionField (planeCurveCoordinateOpen F i)
    (eval₂ (planeCurveChartConstants F i) (planeCurveChartCoordinates F i) P) = _
  rw [eval₂_comp_left]
  change eval₂ (planeCurveGenericConstants F i) (planeCurveGenericCoordinates F i) P = _
  rw [planeCurveGenericConstants_eq_algebraMap]
  rfl

/-- Exact homogeneous kernel in the actual affine section ring. -/
theorem planeCurveChartPolynomialMap_homogeneous_eq_zero_iff
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i : Fin 3) (d : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous d) :
    planeCurveChartPolynomialMap F i P = 0 ↔ P ∈ Ideal.span {F} := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime i
  rw [← (PlaneCurveScheme F).germToFunctionField_injective
    (planeCurveCoordinateOpen F i) |>.eq_iff, map_zero,
    planeCurveChartPolynomialMap_generic]
  exact planeCurve_homogeneous_aeval_eq_zero_iff F e hF hFdeg hprime i d P hP

/-- The complete defining ideal of the actual affine chart, including
nonhomogeneous relations. -/
theorem planeCurveChartPolynomialMap_ker
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    RingHom.ker (planeCurveChartPolynomialMap F i) = Ideal.span {F, X i - 1} := by
  apply ker_eq_span_of_homogeneous_vanishing_on_chart
  · simp
  · exact (planeCurveChartPolynomialMap_homogeneous_eq_zero_iff
      F e hF hFdeg hprime i e F hF).mpr (Ideal.subset_span (Set.mem_singleton F))
  · intro P d hP hz
    exact (planeCurveChartPolynomialMap_homogeneous_eq_zero_iff
      F e hF hFdeg hprime i d P hP).mp hz

/-- The chart's scalar structure is induced by actual constant sections. -/
def planeCurveChartAlgebra (F : PlanePolynomial K) (i : Fin 3) :
    Algebra K Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
  (planeCurveChartConstants F i).toAlgebra

/-- With these actual scalars, polynomial evaluation is the same chart map. -/
theorem planeCurveChart_aeval_eq (F : PlanePolynomial K) (i : Fin 3) :
    letI := planeCurveChartAlgebra F i
    (aeval (planeCurveChartCoordinates F i)).toRingHom =
      planeCurveChartPolynomialMap F i := rfl

/-- The chart constants are exactly those induced by the actual curve
structure morphism. Thus a standard smooth presentation with these scalars
is a presentation over the original geometric base field. -/
theorem planeCurveChartConstants_eq_structure (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] :
    planeCurveChartConstants F i =
      ((planeCurveStructure F).appLE ⊤ (planeCurveCoordinateOpen F i) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
  letI : Nonempty (⊤ : (PlaneCurveScheme F).Opens) :=
    ⟨⟨genericPoint (PlaneCurveScheme F), trivial⟩⟩
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (X i)) :=
    inferInstanceAs (Nonempty (planeCurveCoordinateOpen F i))
  ext c
  apply (PlaneCurveScheme F).germToFunctionField_injective (planeCurveCoordinateOpen F i)
  change projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K)
      (planeCurveInclusion F) (X i) (planeChartConstants i c) = _
  rw [planeChartToFunctionField_constants]
  change (PlaneCurveScheme F).germToFunctionField ⊤
      (schemeBaseScalarHom (planeCurveInclusion F ≫ projectivePlaneStructure K) c) =
    (PlaneCurveScheme F).germToFunctionField (planeCurveCoordinateOpen F i)
      ((PlaneCurveScheme F).presheaf.map (homOfLE le_top).op
        ((planeCurveStructure F).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)))
  rw [generic_germ_restrict]
  rfl

end EvenQuinticConic
