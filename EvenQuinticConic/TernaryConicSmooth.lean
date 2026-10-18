import EvenQuinticConic.PlaneJacobianSmooth
import EvenQuinticConic.TernaryConicIrreducibility
import EvenQuinticConic.TernaryConicGradient

/-!
# Smooth plane hypersurfaces in arbitrary positive homogeneous degree

The actual affine-coordinate Jacobian argument is independent of degree.
This file makes that argument available for quadrics over arbitrary fields,
without algebraic closedness or a smoothness hypothesis on the target scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial

namespace EvenQuinticConic

variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine regular section `(∂F/∂X_j)/X_i^d` on the actual curve's
standard affine chart. -/
def planeCurveDegreeGradientSection (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous (d + 1))
    (i j : Fin 3) : Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
  projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
    (planeCurveInclusion F) (X i)
    (planeHomogeneousChartFraction i d (pderiv j F) hF.pderiv)

/-- Each Jacobian principal open is affine in the actual curve scheme. -/
theorem planeCurveDegreeGradientBasicOpen_isAffine
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous (d + 1)) (i j : Fin 3) :
    IsAffineOpen ((PlaneCurveScheme F).basicOpen (planeCurveDegreeGradientSection F d hF i j)) :=
  (planeCurveCoordinateOpen_isAffine F i).basicOpen _

/-- A nonvanishing homogeneous partial derivative gives an invertible germ
of its actual normalized derivative section on the curve. -/
theorem planeCurveDegreeGradientSection_germ_isUnit
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous (d + 1))
    (i j : Fin 3) (x : PlaneCurveScheme F)
    (hx : x ∈ planeCurveCoordinateOpen F i)
    (hj : pderiv j F ∉ ((planeCurveInclusion F).base x).asHomogeneousIdeal.toIdeal) :
    IsUnit ((PlaneCurveScheme F).presheaf.germ (planeCurveCoordinateOpen F i) x hx
      (planeCurveDegreeGradientSection F d hF i j)) := by
  have ha := (projective_chart_fraction_germ_isUnit_iff
    (homogeneousSubmodule (Fin 3) K) (X i) ((planeCurveInclusion F).base x) hx
    ⟨d • 1, ⟨pderiv j F, by simpa using hF.pderiv (i := j)⟩,
      ⟨(X i) ^ d, SetLike.pow_mem_graded d (isHomogeneous_X K i)⟩,
      ⟨d, rfl⟩⟩).mpr hj
  have hb := ha.map ((planeCurveInclusion F).stalkMap x).hom
  have heq := Scheme.stalkMap_germ_apply (planeCurveInclusion F)
    (Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (X i)) x hx
    ((Proj.awayToSection (homogeneousSubmodule (Fin 3) K) (X i))
      (planeHomogeneousChartFraction i d (pderiv j F) hF.pderiv))
  exact (congrArg IsUnit heq).mp hb

/-- The actual Jacobian principal opens cover every point if the
homogeneous gradient has no projective zero on the defining curve. -/
theorem exists_mem_planeCurveDegreeGradientBasicOpen
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous (d + 1))
    (hgrad : ∀ p : Proj (homogeneousSubmodule (Fin 3) K),
      F ∈ p.asHomogeneousIdeal.toIdeal →
        ∃ j : Fin 3, pderiv j F ∉ p.asHomogeneousIdeal.toIdeal)
    (x : PlaneCurveScheme F) :
    ∃ i j : Fin 3, j ≠ i ∧
      x ∈ (PlaneCurveScheme F).basicOpen (planeCurveDegreeGradientSection F d hF i j) := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show x ∈ iSup (planeCurveCoordinateOpen F) by
      rw [planeCurveCoordinateOpen_cover]; trivial)
  have hp : (planeCurveInclusion F).base x ∈ planeHypersurfaceLocus F := by
    rw [← range_planeCurveInclusion]
    exact ⟨x, rfl⟩
  have hFp : F ∈ ((planeCurveInclusion F).base x).asHomogeneousIdeal.toIdeal :=
    hp (Set.mem_singleton F)
  obtain ⟨j, hji, hj⟩ := exists_nonradial_pderiv_notMem F (d + 1) hF
    ((planeCurveInclusion F).base x) hFp i hi (hgrad _ hFp)
  exact ⟨i, j, hji, ((PlaneCurveScheme F).mem_basicOpen _ x hi).mpr
    (planeCurveDegreeGradientSection_germ_isUnit F d hF i j x hi hj)⟩

/-- Polynomial evaluation of a partial derivative is the actual normalized
homogeneous derivative section. -/
theorem planeCurveChartPolynomialMap_degree_pderiv
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous (d + 1)) (i j : Fin 3) :
    planeCurveChartPolynomialMap F i (pderiv j F) =
      planeCurveDegreeGradientSection F d hF i j :=
  planeCurveChartPolynomialMap_homogeneous F i d (pderiv j F) hF.pderiv

/-- The actual derivative principal-open chart is standard smooth of relative
dimension one as a ring over the original field. -/
theorem planeCurveDegreeGradientBasicOpen_standardSmooth_constants
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous (d + 1))
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j : Fin 3) (hji : j ≠ i) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      (((PlaneCurveScheme F).presheaf.map (homOfLE
          ((PlaneCurveScheme F).basicOpen_le (planeCurveDegreeGradientSection F d hF i j))).op).hom.comp
        (planeCurveChartConstants F i)) := by
  let A := Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i)
  let a := planeCurveDegreeGradientSection F d hF i j
  let T := Γ(PlaneCurveScheme F, (PlaneCurveScheme F).basicOpen a)
  letI := planeCurveChartAlgebra F i
  letI : Algebra K T := ((algebraMap A T).comp (planeCurveChartConstants F i)).toAlgebra
  haveI : IsScalarTower K A T := IsScalarTower.of_algebraMap_eq' rfl
  have ha : (aeval (planeCurveChartCoordinates F i)) (pderiv j F) = a :=
    planeCurveChartPolynomialMap_degree_pderiv F d hF i j
  haveI : IsLocalization.Away ((aeval (planeCurveChartCoordinates F i)) (pderiv j F)) T := by
    rw [ha]
    exact (planeCurveCoordinateOpen_isAffine F i).isLocalization_basicOpen a
  have hv : Function.Surjective (aeval (planeCurveChartCoordinates F i)) :=
    planeCurveChartPolynomialMap_surjective F i
  have hk : RingHom.ker (aeval (planeCurveChartCoordinates F i)) =
      Ideal.span {F, X i - 1} := planeCurveChartPolynomialMap_ker F (d + 1) hF hFdeg hprime i
  exact planeChart_derivative_localization_isStandardSmooth F i j hji
    (planeCurveChartCoordinates F i) hv hk T

/-- Each actual derivative principal open has a standard smooth structure map
on coordinate rings over the actual affine base scheme. -/
theorem planeCurveDegreeGradientBasicOpen_standardSmooth
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous (d + 1))
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j : Fin 3) (hji : j ≠ i) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      ((planeCurveStructure F).appLE ⊤
        ((PlaneCurveScheme F).basicOpen (planeCurveDegreeGradientSection F d hF i j)) le_top).hom := by
  letI := planeCurveScheme_isIntegral F (d + 1) hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F (d + 1) hF hFdeg hprime i
  let a := planeCurveDegreeGradientSection F d hF i j
  let res := (PlaneCurveScheme F).presheaf.map
    (homOfLE ((PlaneCurveScheme F).basicOpen_le a)).op
  let c := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have h := (planeCurveDegreeGradientBasicOpen_standardSmooth_constants F d hF hFdeg hprime i j hji).comp
    (RingHom.IsStandardSmoothOfRelativeDimension.equiv c)
  have heq : (res.hom.comp (planeCurveChartConstants F i)).comp c.toRingHom =
      ((planeCurveStructure F).appLE ⊤ ((PlaneCurveScheme F).basicOpen a) le_top).hom := by
    rw [planeCurveChartConstants_eq_structure]
    change (res.hom.comp
      (((planeCurveStructure F).appLE ⊤ (planeCurveCoordinateOpen F i) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).comp
          (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom = _
    rw [RingHom.comp_assoc, RingHom.comp_assoc, ← CommRingCat.hom_comp,
      Iso.hom_inv_id, CommRingCat.hom_id, RingHom.comp_id]
    rw [← CommRingCat.hom_comp]
    congr 1
    exact (planeCurveStructure F).appLE_map le_top
      (homOfLE ((PlaneCurveScheme F).basicOpen_le a)).op
  change RingHom.IsStandardSmoothOfRelativeDimension (1 + 0)
    ((res.hom.comp (planeCurveChartConstants F i)).comp c.toRingHom) at h
  rwa [heq] at h

/-- The projective nonvanishing-gradient condition proves smoothness of
relative dimension one for the actual plane-curve structure morphism. -/
theorem planeCurveStructure_isSmoothOfRelativeDimension_of_homogeneous_gradient
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous (d + 1))
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (hgrad : ∀ p : Proj (homogeneousSubmodule (Fin 3) K),
      F ∈ p.asHomogeneousIdeal.toIdeal →
        ∃ j : Fin 3, pderiv j F ∉ p.asHomogeneousIdeal.toIdeal) :
    IsSmoothOfRelativeDimension 1 (planeCurveStructure F) where
  exists_isStandardSmoothOfRelativeDimension x := by
    obtain ⟨i, j, hji, hx⟩ := exists_mem_planeCurveDegreeGradientBasicOpen F d hF hgrad x
    exact ⟨⟨⊤, isAffineOpen_top _⟩,
      ⟨_, planeCurveDegreeGradientBasicOpen_isAffine F d hF i j⟩, hx, le_top,
      planeCurveDegreeGradientBasicOpen_standardSmooth F d hF hFdeg hprime i j hji⟩

namespace Incidence

/-- The actual structure morphism of the reduced plane curve cut out by a
nondegenerate symmetric ternary quadratic equation is smooth of relative
dimension one. No algebraic closedness, rational point, or smoothness of the
curve is assumed: primality, degree, and the projective gradient condition
are derived from the actual matrix and its nonzero determinant. -/
theorem ternaryConicStructure_isSmoothOfRelativeDimension
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.IsSymm) (hdet : M.det ≠ 0) :
    IsSmoothOfRelativeDimension 1 (planeCurveStructure (matrixQuadraticPolynomial M)) := by
  apply planeCurveStructure_isSmoothOfRelativeDimension_of_homogeneous_gradient
    (matrixQuadraticPolynomial M) 1 (matrixQuadraticPolynomial_homogeneous M)
  · rw [ternary_matrixQuadraticPolynomial_totalDegree h2 M hM hdet]
    decide
  · exact ternary_matrixQuadraticPolynomial_principal_isPrime h2 M hM hdet
  · intro p _
    exact matrixQuadraticPolynomial_projective_gradient h2 M hM hdet p

end Incidence

end EvenQuinticConic
