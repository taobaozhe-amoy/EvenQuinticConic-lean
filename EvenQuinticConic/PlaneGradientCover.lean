import EvenQuinticConic.PlaneHomogeneousKernel
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Actual Jacobian principal-open charts on a projective plane curve

A nonvanishing projective gradient yields an affine-coordinate derivative
that is nonvanishing on a standard chart. Euler's identity supplies the
nonradial derivative without any restriction on the characteristic.
The resulting opens are principal opens of actual regular sections of
the curve's structure sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial

universe u

namespace EvenQuinticConic

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- On a coordinate chart of a projective hypersurface, a nonzero gradient
has a nonzero derivative in a coordinate different from the chart coordinate.
Euler's identity is used without division by the homogeneous degree. -/
theorem exists_nonradial_pderiv_notMem
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (p : Proj (homogeneousSubmodule (Fin 3) K))
    (hFp : F ∈ p.asHomogeneousIdeal.toIdeal)
    (i : Fin 3) (hi : X i ∉ p.asHomogeneousIdeal.toIdeal)
    (hgrad : ∃ j : Fin 3, pderiv j F ∉ p.asHomogeneousIdeal.toIdeal) :
    ∃ j : Fin 3, j ≠ i ∧ pderiv j F ∉ p.asHomogeneousIdeal.toIdeal := by
  classical
  by_contra! h
  let I := p.asHomogeneousIdeal.toIdeal
  have hs : (∑ j ∈ Finset.univ.erase i, X j * pderiv j F) ∈ I := by
    apply I.sum_mem
    intro j hj
    exact I.mul_mem_left _ (h j (Finset.ne_of_mem_erase hj))
  have ht : (∑ j : Fin 3, X j * pderiv j F) ∈ I := by
    rw [hF.sum_X_mul_pderiv]
    exact I.nsmul_mem hFp d
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at ht
  have hm : X i * pderiv i F ∈ I := (I.add_mem_iff_right hs).mp ht
  have hd : pderiv i F ∈ I := ((show I.IsPrime from inferInstance).mem_or_mem hm).resolve_left hi
  obtain ⟨j, hj⟩ := hgrad
  by_cases hji : j = i
  · exact hj (hji ▸ hd)
  · exact hj (h j hji)

/-- The genuine regular section `(∂F/∂X_j)/X_i^4` on the actual curve's
standard affine chart. -/
def planeCurveGradientSection (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (i j : Fin 3) : Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
  projectiveChartPullback (homogeneousSubmodule (Fin 3) K)
    (planeCurveInclusion F) (X i)
    (planeHomogeneousChartFraction i 4 (pderiv j F) hF.pderiv)

/-- Each Jacobian principal open is affine in the actual curve scheme. -/
theorem planeCurveGradientBasicOpen_isAffine
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j : Fin 3) :
    IsAffineOpen ((PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) :=
  (planeCurveCoordinateOpen_isAffine F i).basicOpen _

/-- A nonvanishing homogeneous partial derivative gives an invertible germ
of its actual normalized derivative section on the curve. -/
theorem planeCurveGradientSection_germ_isUnit
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (i j : Fin 3) (x : PlaneCurveScheme F)
    (hx : x ∈ planeCurveCoordinateOpen F i)
    (hj : pderiv j F ∉ ((planeCurveInclusion F).base x).asHomogeneousIdeal.toIdeal) :
    IsUnit ((PlaneCurveScheme F).presheaf.germ (planeCurveCoordinateOpen F i) x hx
      (planeCurveGradientSection F hF i j)) := by
  have ha := (projective_chart_fraction_germ_isUnit_iff
    (homogeneousSubmodule (Fin 3) K) (X i) ((planeCurveInclusion F).base x) hx
    ⟨4 • 1, ⟨pderiv j F, by simpa using hF.pderiv (i := j)⟩,
      ⟨(X i) ^ 4, SetLike.pow_mem_graded 4 (isHomogeneous_X K i)⟩,
      ⟨4, rfl⟩⟩).mpr hj
  have hb := ha.map ((planeCurveInclusion F).stalkMap x).hom
  have heq := Scheme.stalkMap_germ_apply (planeCurveInclusion F)
    (Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (X i)) x hx
    ((Proj.awayToSection (homogeneousSubmodule (Fin 3) K) (X i))
      (planeHomogeneousChartFraction i 4 (pderiv j F) hF.pderiv))
  exact (congrArg IsUnit heq).mp hb

/-- The actual Jacobian principal opens cover every point if the
homogeneous gradient has no projective zero on the defining curve. -/
theorem exists_mem_planeCurveGradientBasicOpen
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hgrad : ∀ p : Proj (homogeneousSubmodule (Fin 3) K),
      F ∈ p.asHomogeneousIdeal.toIdeal →
        ∃ j : Fin 3, pderiv j F ∉ p.asHomogeneousIdeal.toIdeal)
    (x : PlaneCurveScheme F) :
    ∃ i j : Fin 3, j ≠ i ∧
      x ∈ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j) := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show x ∈ iSup (planeCurveCoordinateOpen F) by
      rw [planeCurveCoordinateOpen_cover]; trivial)
  have hp : (planeCurveInclusion F).base x ∈ planeHypersurfaceLocus F := by
    rw [← range_planeCurveInclusion]
    exact ⟨x, rfl⟩
  have hFp : F ∈ ((planeCurveInclusion F).base x).asHomogeneousIdeal.toIdeal :=
    hp (Set.mem_singleton F)
  obtain ⟨j, hji, hj⟩ := exists_nonradial_pderiv_notMem F 5 hF
    ((planeCurveInclusion F).base x) hFp i hi (hgrad _ hFp)
  exact ⟨i, j, hji, ((PlaneCurveScheme F).mem_basicOpen _ x hi).mpr
    (planeCurveGradientSection_germ_isUnit F hF i j x hi hj)⟩

/-- Indexing by distinct chart and derivative coordinates, the actual
Jacobian principal opens have supremum equal to the entire curve. -/
theorem planeCurveGradientBasicOpen_cover
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hgrad : ∀ p : Proj (homogeneousSubmodule (Fin 3) K),
      F ∈ p.asHomogeneousIdeal.toIdeal →
        ∃ j : Fin 3, pderiv j F ∉ p.asHomogeneousIdeal.toIdeal) :
    (⨆ a : Σ i : Fin 3, {j : Fin 3 // j ≠ i},
      (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF a.1 a.2.1)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, j, hji, hx⟩ := exists_mem_planeCurveGradientBasicOpen F hF hgrad x
  exact Opens.mem_iSup.mpr ⟨⟨i, j, hji⟩, hx⟩

end EvenQuinticConic
