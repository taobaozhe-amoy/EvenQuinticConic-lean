import EvenQuinticConic.PlaneCurveScheme
import EvenQuinticConic.SchemeIntegralOpenCover
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The actual standard cover after extending the coefficient field

The three standard charts are base changed as categorical pullbacks. A point
over the original curve's generic point lies in all three chart ranges. Thus
integrality of the actual base-changed charts implies integrality of the whole
actual pullback; no comparison of underlying sets with field-valued points is
substituted for a scheme-theoretic base change.
-/

noncomputable section
set_option maxRecDepth 4096

namespace EvenQuinticConic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

variable {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]

/-- Extension of coefficients is the actual categorical pullback of the
original projective curve structure morphism. -/
abbrev PlaneCurveFieldBaseChange (F : PlanePolynomial K) :=
  pullback (planeCurveStructure F)
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The three actual standard affine opens as a scheme open cover. -/
def planeCurveStandardOpenCover (F : PlanePolynomial K) :
    (PlaneCurveScheme F).OpenCover :=
  (PlaneCurveScheme F).openCoverOfIsOpenCover (planeCurveCoordinateOpen F)
    (.mk (planeCurveCoordinateOpen_cover F))

/-- The actual pullbacks of the standard opens cover the actual extended curve. -/
def planeCurveFieldBaseChangeCover (F : PlanePolynomial K) :
    (PlaneCurveFieldBaseChange L F).OpenCover :=
  Scheme.Pullback.openCoverOfLeft (planeCurveStandardOpenCover F)
    (planeCurveStructure F) (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- Its chart range is precisely the inverse image of the original coordinate
open under the actual first projection. -/
theorem planeCurveFieldBaseChangeCover_range (F : PlanePolynomial K) (i : Fin 3) :
    Set.range ((planeCurveFieldBaseChangeCover L F).f i).base =
      (pullback.fst (planeCurveStructure F)
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base ⁻¹'
        (planeCurveCoordinateOpen F i : Set (PlaneCurveScheme F)) := by
  have hr := Scheme.Pullback.range_map
    ((planeCurveStandardOpenCover F).f i ≫ planeCurveStructure F)
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) (planeCurveStructure F)
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    ((planeCurveStandardOpenCover F).f i) (𝟙 _) (𝟙 _)
    (Category.comp_id _) (by simp)
  have hri : Set.range (planeCurveCoordinateOpen F i).ι.base =
      (planeCurveCoordinateOpen F i : Set (PlaneCurveScheme F)) :=
    Scheme.Opens.range_ι (planeCurveCoordinateOpen F i)
  have hr' : Set.range ((planeCurveFieldBaseChangeCover L F).f i).base =
      (pullback.fst (planeCurveStructure F)
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base ⁻¹'
        Set.range (planeCurveCoordinateOpen F i).ι.base := by
    simpa only [planeCurveFieldBaseChangeCover, Scheme.Pullback.openCoverOfLeft_f,
      planeCurveStandardOpenCover, Scheme.openCoverOfIsOpenCover_f,
      Scheme.id.base, TopCat.coe_id, Set.range_id,
      Set.preimage_univ, Set.inter_univ] using hr
  exact hr'.trans (congrArg (fun s : Set (PlaneCurveScheme F) =>
    (pullback.fst (planeCurveStructure F)
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base ⁻¹' s) hri)


/-- A single actual point lies in every extended standard chart. Its residue
field need not equal the extension field. -/
theorem exists_mem_all_planeCurveFieldBaseChangeCover
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) :
    ∃ z : PlaneCurveFieldBaseChange L F,
      ∀ i : Fin 3, z ∈ Set.range ((planeCurveFieldBaseChangeCover L F).f i).base := by
  letI := planeCurveScheme_isIntegral F d hF hFdeg hprime
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := planeCurveStructure F)
    (g := Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (genericPoint (PlaneCurveScheme F)) (genericPoint (Spec (CommRingCat.of L)))
    (Subsingleton.elim _ _)
  refine ⟨z, fun i => ?_⟩
  rw [planeCurveFieldBaseChangeCover_range]
  change (pullback.fst (planeCurveStructure F)
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base z ∈
      planeCurveCoordinateOpen F i
  rw [hz]
  exact genericPoint_mem_planeCurveCoordinateOpen F d hF hFdeg hprime i

/-- Integral standard-chart pullbacks imply integrality of the whole actual
curve pullback. The required intersections are derived from the original
homogeneous prime equation, rather than supplied separately. -/
theorem planeCurveFieldBaseChange_isIntegral_of_charts
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (hcharts : ∀ i : Fin 3,
      IsIntegral ((planeCurveFieldBaseChangeCover L F).X i)) :
    IsIntegral (PlaneCurveFieldBaseChange L F) := by
  haveI : Nonempty (planeCurveFieldBaseChangeCover L F).I₀ :=
    inferInstanceAs (Nonempty (Fin 3))
  apply scheme_isIntegral_of_openCover (planeCurveFieldBaseChangeCover L F) hcharts
  obtain ⟨z, hz⟩ := exists_mem_all_planeCurveFieldBaseChangeCover L F d hF hFdeg hprime
  exact fun i j => ⟨z, hz i, hz j⟩

end EvenQuinticConic
